#!/usr/bin/env python3
"""Kernel-check exported case declarations; this does not prove their goals."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


def read_index(directory):
    with (directory / 'index.tsv').open() as stream:
        rows = list(csv.DictReader(stream, delimiter='\t'))
    if not rows:
        raise ValueError('index.tsv contains no cases')
    seen = set()
    kinds = {'accept': 'accepted-exact', 'reject': 'no-success',
             'abort-reject': 'rejection-conjecture'}
    for row in rows:
        index = int(row['case_id'])
        if index < 0 or index in seen:
            raise ValueError('invalid or duplicate case_id')
        seen.add(index)
        if row['goal_kind'] != kinds.get(row['expectation']):
            raise ValueError(f'case {index}: invalid expectation/goal_kind')
        for field, expected in [('data_module', f'Case{index:04d}Data.lean'),
                                ('goal_module', f'Case{index:04d}.lean')]:
            if row[field] != expected:
                raise ValueError(f'case {index}: invalid {field}')
            source = directory / 'cases' / expected
            if not source.is_file() or source.is_symlink():
                raise ValueError(f'case {index}: missing or linked {field}')
    return rows


def check_lean(source, env, build):
    start = time.monotonic()
    output = build / source.with_suffix('.olean').name
    result = subprocess.run(['lean', '--root', str(source.parent),
                             '-o', str(output), str(source)],
                            cwd=build, env=env, capture_output=True, text=True)
    text = result.stdout + result.stderr
    if result.returncode == 0 and 'declaration uses `sorry`' in text:
        return time.monotonic() - start, 'Lean accepted a declaration using sorry\n' + text
    return time.monotonic() - start, text if result.returncode else None


def check_case(directory, row, env, build):
    result = {'case_id': int(row['case_id']), 'expectation': row['expectation'],
              'source': row['source'], 'goal_kind': row['goal_kind'],
              'data_checked': False, 'goal_checked': False, 'seconds': 0.0}
    for field, status, checked in [('data_module', 'data-error', 'data_checked'),
                                   ('goal_module', 'goal-error', 'goal_checked')]:
        source = directory / 'cases' / row[field]
        seconds, error = check_lean(source, env, build)
        result['seconds'] += seconds
        if error is not None:
            result.update(status=status, error=error)
            return result
        result[checked] = True
    result['status'] = 'checked'
    return result


def replace_text(path, text):
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent,
                                     prefix=f'.{path.name}.', delete=False) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(text)
            stream.close()
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)


def write_report(directory, report):
    replace_text(directory / 'checks.json', json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    lines = ['# Case declaration checks', '',
             'These checks validate declarations, not proofs of the case propositions.', '',
             f"Verification status: {report['status']}.", '',
             f"All declarations checked: {report['all_declarations_checked']}. "
             'Corpus propositions proved by this command: 0.', '',
             '| ID | Result | Data declaration | Proposition declaration |',
             '|---:|---|---|---|']
    for case in report['cases']:
        index = case['case_id']
        lines.append(f"| {index} | {case['status']} | "
                     f"[Case{index:04d}Data](cases/Case{index:04d}Data.lean) | "
                     f"[Case{index:04d}](cases/Case{index:04d}.lean) |")
    replace_text(directory / 'checks.md', '\n'.join(lines) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=2)
    args = parser.parse_args()
    directory = args.directory.resolve()
    start = time.monotonic()
    report = {'status': 'running', 'all_declarations_checked': False,
              'propositions_proved': 0, 'semantics_modules_checked': 0, 'cases': []}
    try:
        write_report(directory, report)
        if args.jobs < 1:
            raise ValueError('--jobs must be positive')
        rows = read_index(directory)
        semantics = directory / 'semantics'
        modules = [semantics / 'SpecTecCore.lean', semantics / 'SpecTecSupport.lean']
        modules += sorted(semantics.glob('SpecTecDecl*.lean'))
        modules += [semantics / f'{name}.lean' for name in
                    ('SpecTecAll', 'SpecTecProofs', 'SpecTecCases')]
        # Both import lookup and cwd use this fresh directory. Package .olean
        # files and the caller's LEAN_PATH cannot satisfy a missing source.
        with tempfile.TemporaryDirectory(prefix='spectec-case-check-') as temporary:
            build = Path(temporary)
            env = os.environ | {'LEAN_PATH': str(build)}
            for source in modules:
                _, error = check_lean(source, env, build)
                if error is not None:
                    report['semantics_error'] = {'module': source.name, 'error': error}
                    raise ValueError(f'{source.name}: {error}')
                report['semantics_modules_checked'] += 1
                if report['semantics_modules_checked'] % 32 == 0:
                    print(f"Checked {report['semantics_modules_checked']}/{len(modules)} semantics modules", flush=True)
            print(f'Checked all {len(modules)} shared semantics modules', flush=True)
            with ThreadPoolExecutor(max_workers=args.jobs) as pool:
                # Start large data files first so one large case does not begin
                # only after all the small cases have already finished.
                scheduled = sorted(rows, key=lambda row:
                    (directory / 'cases' / row['data_module']).stat().st_size, reverse=True)
                futures = [pool.submit(check_case, directory, row, env, build) for row in scheduled]
                for future in as_completed(futures):
                    result = future.result()
                    report['cases'].append(result)
                    count = len(report['cases'])
                    if result['status'] != 'checked':
                        print(f"case {result['case_id']}: {result['status']}", file=sys.stderr, flush=True)
                    if count % 32 == 0 or count == len(rows):
                        print(f'Checked {count}/{len(rows)} cases', flush=True)
        report['cases'].sort(key=lambda case: case['case_id'])
        report['all_declarations_checked'] = all(case['status'] == 'checked' for case in report['cases'])
        report['status'] = 'complete' if report['all_declarations_checked'] else 'failed'
        report['seconds'] = time.monotonic() - start
        write_report(directory, report)
        failures = sum(case['status'] != 'checked' for case in report['cases'])
        print(f'Case declarations: {len(rows) - failures} checked, {failures} failed; propositions proved: 0')
        return int(bool(failures))
    except (OSError, ValueError, KeyError, TypeError, csv.Error) as error:
        report.update(status='failed', all_declarations_checked=False,
                      error=str(error), seconds=time.monotonic() - start)
        report['cases'].sort(key=lambda case: case['case_id'])
        try:
            write_report(directory, report)
        except OSError as report_error:
            print(f'Cannot write failure report: {report_error}', file=sys.stderr)
        print(error, file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
