#!/usr/bin/env python3
"""Prove accepted Program_ok outputs, in increasing P4 source byte size."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
             f"Started (UTC): {report['started']}. Status: **{report['status']}**.", '',
             f"Commit: `{report['commit']}`. Lean: `{report['lean_version']}`.", '',
             'Target: `Program_ok input expected`, with the exact recorded oracle and initial fresh supply 0.',
             'This proves acceptance only; the corpus proposition also asks for uniqueness, which this runner does not prove.',
             'Native evaluation selects fuel and final supply. Only a kernel-checked `runEval_sound … rfl` theorem counts as proved.', '',
             f"Order: source bytes, then path. Selected: {len(report['cases'])}/{report['total_positive']}. "
             f"Proved: **{report['proved']}**.", '',
             'Command:', '', '```sh', report['command'], '```', '',
             f"Artifacts: `{output}` (generated Lean, phase output, commands, timings, hashes and `results.json`).", '',
             '| ID | Bytes | Source | Result | Fuel | Seconds |',
             '|---:|---:|---|---|---:|---:|']
    for row in report['cases']:
        source = Path(row['source'])
        try:
            source = source.relative_to(Path.cwd())
        except ValueError:
            pass
        lines.append(f"| {row['case_id']} | {row['bytes']} | `{source}` | {row['status']} | "
                     f"{row.get('fuel', '')} | {row.get('seconds', 0):.2f} |")
    if report.get('error'):
        lines += ['', 'Setup/run error:', '', '```text', report['error'], '```']
    for row in report['cases']:
        if row.get('error') or row.get('axioms'):
            lines += ['', f"Case {row['case_id']} ({row['status']}):", '', '```text',
                      row.get('error', row.get('axioms', '')), '```']
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
        except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
            interrupted = isinstance(error, KeyboardInterrupt)
            # The translator can spawn a preprocessor or gzip. Bound the whole
            # process group, including children that still hold the output pipes.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
            code = None
            stderr += '\nPhase interrupted.\n' if interrupted else '\nPhase timed out.\n'
    (output / f'{label}.stdout.txt').write_text(stdout)
    (output / f'{label}.stderr.txt').write_text(stderr)
    record = dict(command=command, returncode=code, seconds=time.monotonic() - start)
    (output / f'{label}.json').write_text(json.dumps(record, indent=2) + '\n')
    if interrupted:
        raise KeyboardInterrupt
    return record, stdout, stderr


def lean_phase(source, output, timeout):
    return run_phase(['lean', '-o', str(source.with_suffix('.olean')), str(source)],
                     output, source.stem, timeout)


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
    source.write_text('import Semantics\nset_option maxRecDepth 16384\n' + data)
    require_success(*lean_phase(source, output, args.timeout))
    for fuel in args.fuel:
        row['fuel'] = fuel
        probe = output / f'Case{index:04d}Probe{fuel}.lean'
        probe.write_text(f'''import {module}
open SpecTec SpecTecExecution
#eval match runEval specTecExecutableProgram {fuel} (.call (Call.Program_ok {name}_input)) 0 with
  | .done (.success _) supply => "RESULT success " ++ toString supply
  | .done .unmatch _ => "RESULT unmatch"
  | .done (.abort message) _ => "RESULT abort " ++ message
  | .outOfFuel => "RESULT outOfFuel"
  | .unsupportedChoice => "RESULT unsupportedChoice"
''')
        phase, stdout, stderr = lean_phase(probe, output, args.timeout)
        row['attempts'].append(dict(fuel=fuel, **phase))
        if phase['returncode'] != 0:
            row.update(status='timeout' if phase['returncode'] is None else 'evaluation-error',
                       error=stdout + stderr)
            return
        match = re.search(r'^"RESULT (success (\d+)|outOfFuel|unsupportedChoice|unmatch|abort.*)"$', stdout, re.M)
        if not match:
            row.update(status='evaluation-error', error=stdout + stderr)
            return
        status = match[1].split()[0]
        if status != 'success':
            row['status'] = status
            if status == 'outOfFuel':
                continue
            if status == 'abort':
                row['error'] = match[1]
            return
        supply = int(match[2])
        proof = output / f'Case{index:04d}Proof.lean'
        proof.write_text(f'''import {module}
set_option maxRecDepth 16384
set_option maxHeartbeats {args.heartbeats}
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
    parser.add_argument('--limit', type=int, default=10, help='smallest N positives; 0 means all')
    parser.add_argument('--offset', type=int, default=0, help='skip N positives in sorted order')
    parser.add_argument('--fuel', type=int, nargs='+', default=[128, 512, 2048])
    parser.add_argument('--timeout', type=float, default=120, help='seconds per case phase')
    parser.add_argument('--setup-timeout', type=float, default=900)
    parser.add_argument('--heartbeats', type=int, default=4000000)
    args = parser.parse_args()
    if args.limit < 0 or args.offset < 0 or min(args.fuel) < 1 or min(args.timeout, args.setup_timeout, args.heartbeats) <= 0:
        parser.error('limits must be positive (limit and offset may be zero)')
    output, report_path = args.output.resolve(), args.report.resolve()
    if output.exists() or report_path.exists():
        parser.error('output and report must be new paths; previous evidence is never overwritten')
    args.exe, args.spec = str(Path(args.exe).resolve()), str(Path(args.spec).resolve())
    args.includes = [item for directory in args.include for item in ('-I', str(Path(directory).resolve()))]
    args.fuel = sorted(set(args.fuel))
    output.mkdir(parents=True)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report = dict(started=datetime.now(timezone.utc).isoformat(), status='running',
                  command=shlex.join([sys.executable, *sys.argv]), commit='unknown',
                  lean_version='unknown', total_positive=0, cases=[], proved=0,
                  runner_sha256=digest(Path(__file__)))
    if os.environ.get('ELAN_TOOLCHAIN'):
        report['command'] = 'ELAN_TOOLCHAIN=' + shlex.quote(os.environ['ELAN_TOOLCHAIN']) + ' ' + report['command']
    try:
        report['commit'] = subprocess.run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
        report['lean_version'] = subprocess.run(['lean', '--version'], check=True, capture_output=True, text=True).stdout.strip()
        rows = select_cases(args.manifest.resolve())
        report['total_positive'] = len(rows)
        report['manifest_sha256'] = digest(args.manifest.resolve())
        report['executable_sha256'] = digest(Path(args.exe))
        report['cases'] = rows[args.offset:args.offset + args.limit if args.limit else None]
        if not report['cases']:
            raise ValueError('no positive cases selected')
        save_report(output, report_path, report)
        print(f"Selected {len(report['cases'])}/{len(rows)} positive cases; compiling shared semantics", flush=True)
        phase, semantics, error = run_phase([args.exe, '--executable', args.spec],
                                            output, 'translation', args.setup_timeout)
        require_success(phase, semantics, error)
        source = output / 'Semantics.lean'
        source.write_text(semantics)
        report['semantics_sha256'] = digest(source)
        require_success(*lean_phase(source, output, args.setup_timeout))
        for row in report['cases']:
            start = time.monotonic()
            row['status'] = 'running'
            save_report(output, report_path, report)
            print(f"case {row['case_id']}: {row['bytes']} bytes, {row['source']}", flush=True)
            try:
                prove_case(row, args, output)
            except TimeoutError as error:
                row.update(status='timeout', error=str(error))
            except (OSError, ValueError) as error:
                row.update(status='case-error', error=str(error))
            row['seconds'] = time.monotonic() - start
            save_report(output, report_path, report)
            print(f"  {row['status']} ({row['seconds']:.2f}s)", flush=True)
        report['status'] = 'complete'
    except (OSError, ValueError, subprocess.SubprocessError, KeyboardInterrupt) as error:
        report.update(status='failed', error=str(error) or 'interrupted')
    save_report(output, report_path, report)
    print(f"Proved {report['proved']}/{len(report['cases'])}; log: {report_path}", flush=True)
    return int(report['status'] != 'complete' or report['proved'] != len(report['cases']))


if __name__ == '__main__':
    raise SystemExit(main())
