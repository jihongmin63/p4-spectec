#!/usr/bin/env python3
"""Prove accepted Program_ok outputs, in increasing P4 source byte size."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import signal
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent


class CaseTimeout(TimeoutError):
    pass


def expire_case(_signal, _frame):
    raise CaseTimeout('case time limit reached')


def success(status):
    if status in ('pending', 'running', 'not-run'):
        return '—'
    return 'PASS' if status == 'proved' else 'FAIL'


def digest(path):
    hasher = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            hasher.update(chunk)
    return hasher.hexdigest()


def select_cases(manifest):
    cases = []
    index = 0
    for line in manifest.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        fields = line.split('\t')
        if fields[0] not in ('accept', 'reject', 'abort-reject') or len(fields) != (3 if fields[0] == 'accept' else 2):
            raise ValueError(f'invalid manifest entry {index}: {line}')
        if fields[0] == 'accept':
            source = (manifest.parent / fields[1]).resolve()
            oracle = (manifest.parent / fields[2]).resolve()
            cases.append(dict(case_id=index, source=str(source), oracle=str(oracle),
                              bytes=source.stat().st_size, source_sha256=digest(source),
                              oracle_sha256=digest(oracle), status='pending', attempts=[]))
        index += 1
    return sorted(cases, key=lambda row: (row['bytes'], row['source'], row['case_id']))


def replace_text(path, content):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(content)
    temporary.replace(path)


def save_report(output, path, report):
    report['proved'] = sum(c['status'] == 'proved' for c in report['cases'])
    replace_text(output / 'results.json', json.dumps(report, indent=2) + '\n')
    lines = ['# Positive case proof log', '',
             '| Case | Seconds | Success |', '|---|---:|---|']
    for row in report['cases']:
        if row['status'] == 'pending':
            continue
        seconds = f"{row['seconds']:.2f}" if 'seconds' in row else '—'
        lines.append(f"| case_{row['case_id']} | {seconds} | {success(row['status'])} |")
    passed = report['status'] == 'complete' and report['proved'] == len(report['cases'])
    result = '—' if report['status'] == 'running' else ('PASS' if passed else 'FAIL')
    lines.append(f"| total | {report.get('seconds', 0):.2f} | {result} |")
    replace_text(path, '\n'.join(lines) + '\n')


def run_phase(command, output, label, timeout):
    start = time.monotonic()
    env = os.environ | {'LEAN_PATH': str(output)}
    interrupted = False
    with subprocess.Popen(command, cwd=output, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True, start_new_session=True) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
            code = process.returncode
        except (subprocess.TimeoutExpired, KeyboardInterrupt, CaseTimeout) as error:
            interrupted = isinstance(error, KeyboardInterrupt)
            expired = isinstance(error, CaseTimeout)
            # The translator can spawn a preprocessor or gzip. Bound the whole
            # process group, including children that still hold the output pipes.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
            code = None
            stderr += '\nPhase interrupted.\n' if interrupted else '\nPhase timed out.\n'
        else:
            expired = False
    (output / f'{label}.stdout.txt').write_text(stdout)
    (output / f'{label}.stderr.txt').write_text(stderr)
    record = dict(command=command, returncode=code, seconds=time.monotonic() - start)
    (output / f'{label}.json').write_text(json.dumps(record, indent=2) + '\n')
    if interrupted:
        raise KeyboardInterrupt
    if expired:
        raise CaseTimeout('case time limit reached')
    return record, stdout, stderr


def lean_phase(source, output, timeout):
    return run_phase(['lean', '-o', str(source.with_suffix('.olean')), str(source)],
                     output, source.stem, timeout)


def reuse_semantics(cache, output, report):
    cached = json.loads((cache / 'results.json').read_text())
    if cached['lean_version'] != report['lean_version']:
        raise ValueError('cached semantics Lean version differs')
    if (cached.get('semantics_sha256') != report['semantics_sha256']
            or digest(cache / 'Semantics.lean') != report['semantics_sha256']):
        raise ValueError('cached semantics source differs from freshly generated semantics')
    compiled_hash = digest(cache / 'Semantics.olean')
    if cached.get('semantics_olean_sha256') != compiled_hash:
        raise ValueError('cached compiled semantics hash is missing or differs')
    shutil.copyfile(cache / 'Semantics.olean', output / 'Semantics.olean')
    report['semantics_cache'] = str(cache)


def proved_in(previous):
    cached = json.loads((previous / 'results.json').read_text())
    return {(c['case_id'], c['source_sha256'], c['oracle_sha256'])
            for c in cached['cases'] if c['status'] == 'proved'}


def require_success(phase, stdout, stderr):
    if phase['returncode'] is None:
        raise TimeoutError(shlex.join(phase['command']) + '\n' + stdout + stderr)
    if phase['returncode'] != 0 or 'declaration uses `sorry`' in stdout + stderr:
        raise ValueError(('timeout' if phase['returncode'] is None else 'command failed')
                         + ': ' + shlex.join(phase['command']) + '\n' + stdout + stderr)


def prove_case(row, args, output):
    index = row['case_id']
    # Every data module is compiled independently and imported by only its own
    # probe/proof. Preserve exporter identifiers and all serialized literals.
    name = 'case_0'
    theorem = f'case_{index}_by_runEval'
    module = f'Case{index:04d}Data'
    phase, data, error = run_phase([args.exe, '--obligations-only', '--case',
        row['source'], row['oracle'], *args.includes, args.spec], output,
        f'Case{index:04d}Export', args.timeout)
    require_success(phase, data, error)
    source = output / f'{module}.lean'
    source.write_text('import Semantics\nset_option maxRecDepth 16384\n'
                      + ('noncomputable section\n' if args.kernel_only else '') + data)
    require_success(*lean_phase(source, output, args.timeout))
    for fuel in args.fuel:
        row['fuel'] = fuel
        probe = output / f'Case{index:04d}Probe{fuel}.lean'
        branches = '''
  | .done (.success _) supply => (0, supply)
  | .done .unmatch _ => (1, 0)
  | .done (.abort _) _ => (2, 0)
  | .outOfFuel => (3, 0)
  | .unsupportedChoice => (4, 0)
''' if args.kernel_only else '''
  | .done (.success _) supply => "RESULT success " ++ toString supply
  | .done .unmatch _ => "RESULT unmatch"
  | .done (.abort message) _ => "RESULT abort " ++ message
  | .outOfFuel => "RESULT outOfFuel"
  | .unsupportedChoice => "RESULT unsupportedChoice"
'''
        probe.write_text(f'''import {module}
set_option maxRecDepth 16384
set_option maxHeartbeats {args.heartbeats}
open SpecTec SpecTecExecution
{'#reduce' if args.kernel_only else '#eval'} match runEval specTecExecutableProgram {fuel} (.call (Call.Program_ok {name}_input)) 0 with
{branches}
''')
        phase, stdout, stderr = lean_phase(probe, output, args.timeout)
        row['attempts'].append(dict(fuel=fuel, **phase))
        if phase['returncode'] != 0:
            row.update(status='timeout' if phase['returncode'] is None else 'evaluation-error',
                       error=stdout + stderr)
            return
        match = (re.fullmatch(r'\s*\(([0-4]),\s*(\d+)\)\s*', stdout)
                 if args.kernel_only else re.search(
                     r'^"RESULT (success (\d+)|outOfFuel|unsupportedChoice|unmatch|abort.*)"$', stdout, re.M))
        if not match:
            row.update(status='evaluation-error', error=stdout + stderr)
            return
        status = (['success', 'unmatch', 'abort', 'outOfFuel', 'unsupportedChoice'][int(match[1])]
                  if args.kernel_only else match[1].split()[0])
        if status != 'success':
            row['status'] = status
            if status == 'outOfFuel':
                continue
            if status == 'abort' and not args.kernel_only:
                row['error'] = match[1]
            return
        supply = int(match[2])
        proof = output / f'Case{index:04d}Proof.lean'
        # Smart unfolding rebuilds runEval's continuation lambdas at every step, so
        # elaborating `rfl` can exhaust memory where `#reduce` (which disables it) does not.
        proof.write_text(f'''import {module}
set_option maxRecDepth 16384
set_option maxHeartbeats {args.heartbeats}
set_option smartUnfolding false
namespace SpecTec
open SpecTecExecution
theorem {theorem} : Program_ok {name}_input {name}_expected :=
  ⟨{supply}, runEval_sound specTecExecutableProgram {fuel}
    (.call (Call.Program_ok {name}_input)) 0 (.success {name}_expected) {supply} rfl⟩
end SpecTec
#print axioms SpecTec.{theorem}
''')
        phase, stdout, stderr = lean_phase(proof, output, args.timeout)
        row['attempts'].append(dict(fuel=fuel, **phase))
        row['final_supply'] = supply
        # Audit the transitive axiom list, not just Lean's successful exit code.
        audit = re.search(r"depends on axioms: \[([^\]]*)\]", stdout)
        clean = (audit is not None and set(audit[1].split(', ')) <= {'propext', 'Quot.sound', 'Classical.choice'})
        clean |= 'does not depend on any axioms' in stdout
        if phase['returncode'] == 0 and clean and 'sorry' not in stdout + stderr:
            row.update(status='proved', axioms=stdout.strip())
        else:
            row.update(status='timeout' if phase['returncode'] is None else 'proof-error',
                       error=stdout + stderr)
        return


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exe', required=True)
    parser.add_argument('--spec', default='spec')
    parser.add_argument('--manifest', type=Path, default=HERE / 'typecheck-cases.tsv')
    parser.add_argument('--output', type=Path, required=True, help='new artifact directory')
    parser.add_argument('--report', type=Path, required=True, help='new Markdown log document')
    parser.add_argument('-I', dest='include', action='append', default=[])
    parser.add_argument('--limit', type=int, default=0, help='smallest N positives; default 0 means all')
    parser.add_argument('--offset', type=int, default=0, help='skip N positives in sorted order')
    parser.add_argument('--fuel', type=int, nargs='+', default=[128, 512, 2048])
    parser.add_argument('--timeout', type=float, help='optional tighter limit in seconds per case phase')
    parser.add_argument('--setup-timeout', type=float, default=900)
    parser.add_argument('--case-timeout', type=float, default=1800,
                        help='wall-clock seconds for each case, including all fuel attempts (default: 1800)')
    parser.add_argument('--semantics-from', type=Path,
                        help='reuse checked shared semantics from a previous run with matching source and Lean version')
    parser.add_argument('--skip-proved-from', type=Path,
                        help='omit cases a previous run proved for the same source and oracle hashes')
    parser.add_argument('--heartbeats', type=int, default=4000000)
    parser.add_argument('--kernel-only', action='store_true',
                        help='allow noncomputable semantics and probe with kernel reduction')
    args = parser.parse_args()
    if (args.limit < 0 or args.offset < 0 or min(args.fuel) < 1
            or not all(math.isfinite(n) and n > 0 for n in
                       (args.setup_timeout, args.case_timeout, args.heartbeats))
            or (args.timeout is not None and (not math.isfinite(args.timeout) or args.timeout <= 0))):
        parser.error('limits must be positive (limit and offset may be zero)')
    output, report_path = args.output.resolve(), args.report.resolve()
    if output.exists() or report_path.exists():
        parser.error('output and report must be new paths; previous evidence is never overwritten')
    args.exe, args.spec = str(Path(args.exe).resolve()), str(Path(args.spec).resolve())
    args.includes = [item for directory in args.include for item in ('-I', str(Path(directory).resolve()))]
    args.fuel = sorted(set(args.fuel))
    run_start = time.monotonic()
    output.mkdir(parents=True)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report = dict(started=datetime.now(timezone.utc).isoformat(), status='running',
                  command=shlex.join([sys.executable, *sys.argv]), commit='unknown',
                  lean_version='unknown', total_positive=0, cases=[], proved=0,
                  runner_sha256=digest(Path(__file__)), kernel_only=args.kernel_only,
                  seconds=0.0, case_timeout=args.case_timeout)
    if os.environ.get('ELAN_TOOLCHAIN'):
        report['command'] = 'ELAN_TOOLCHAIN=' + shlex.quote(os.environ['ELAN_TOOLCHAIN']) + ' ' + report['command']
    previous_handler = signal.signal(signal.SIGALRM, expire_case)
    print('case\tseconds\tsuccess', flush=True)
    try:
        report['commit'] = subprocess.run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
        report['lean_version'] = subprocess.run(['lean', '--version'], check=True, capture_output=True, text=True).stdout.strip()
        rows = select_cases(args.manifest.resolve())
        report['total_positive'] = len(rows)
        report['manifest_sha256'] = digest(args.manifest.resolve())
        report['executable_sha256'] = digest(Path(args.exe))
        if args.skip_proved_from:
            proved = proved_in(args.skip_proved_from.resolve())
            rows = [row for row in rows if (row['case_id'], row['source_sha256'], row['oracle_sha256']) not in proved]
            report['skipped_proved'] = dict(source=str(args.skip_proved_from.resolve()),
                                            count=report['total_positive'] - len(rows))
        report['cases'] = rows[args.offset:args.offset + args.limit if args.limit else None]
        if not report['cases']:
            raise ValueError('no positive cases selected')
        save_report(output, report_path, report)
        phase, semantics, error = run_phase([args.exe, '--executable', args.spec],
                                            output, 'translation', args.setup_timeout)
        require_success(phase, semantics, error)
        source = output / 'Semantics.lean'
        source.write_text(('noncomputable section\n' if args.kernel_only else '') + semantics)
        report['semantics_sha256'] = digest(source)
        if args.semantics_from:
            reuse_semantics(args.semantics_from.resolve(), output, report)
        else:
            require_success(*lean_phase(source, output, args.setup_timeout))
        report['semantics_olean_sha256'] = digest(source.with_suffix('.olean'))
        for row in report['cases']:
            start = time.monotonic()
            row['status'] = 'running'
            save_report(output, report_path, report)
            signal.setitimer(signal.ITIMER_REAL,
                             max(0.000001, args.case_timeout - (time.monotonic() - start)))
            try:
                prove_case(row, args, output)
            except TimeoutError as error:
                row.update(status='timeout', error=str(error))
            except (OSError, ValueError) as error:
                row.update(status='case-error', error=str(error))
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
                row['seconds'] = time.monotonic() - start
            report['seconds'] = time.monotonic() - run_start
            save_report(output, report_path, report)
            print(f"case_{row['case_id']}\t{row['seconds']:.2f}\t{success(row['status'])}", flush=True)
        report['status'] = 'complete'
    except (OSError, ValueError, KeyError, subprocess.SubprocessError, KeyboardInterrupt) as error:
        report.update(status='failed', error=str(error) or 'interrupted')
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)
    report['seconds'] = time.monotonic() - run_start
    save_report(output, report_path, report)
    failed = report['status'] != 'complete' or report['proved'] != len(report['cases'])
    print(f"total\t{report['seconds']:.2f}\t{'FAIL' if failed else 'PASS'}", flush=True)
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
