#!/usr/bin/env python3
"""Slow integration check of the actual spec, its proofs, and every output module."""
import argparse
from pathlib import Path
import os
import subprocess
import tempfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--exe', required=True)
parser.add_argument('--spec', default='spec')
args = parser.parse_args()
exe = str(Path(args.exe).resolve())
spec = str(Path(args.spec).resolve())
proof = Path(__file__).with_name('actual-cast-proof.lean').read_text()

def run(command, *, env=None, cwd=None, accepted=(0,)):
    result = subprocess.run(command, capture_output=True, text=True, env=env, cwd=cwd)
    if result.returncode not in accepted:
        raise RuntimeError(' '.join(command) + '\n' + result.stdout + result.stderr)
    return result

with tempfile.TemporaryDirectory(prefix='ordered-spec-') as tmp:
    root = Path(tmp)
    source = run([exe, '--keep-going', spec], accepted=(0, 1))
    if not source.stdout or 'def Cast_expl_neq ' not in source.stdout:
        raise RuntimeError('the actual cast relation was pruned')
    (root / 'diagnostics.txt').write_text(source.stderr)
    standalone = root / 'Standalone.lean'
    standalone.write_text(source.stdout + proof)
    run(['lean', str(standalone)])
    print('Actual spec: standalone kernel check and OK/FAIL cast proofs passed', flush=True)
    modules = root / 'modules'
    result = run([exe, '--keep-going', '--emit-modules', str(modules), spec], accepted=(0, 1))
    files = ['SpecTecCore.lean', 'SpecTecSupport.lean']
    files += [p.name for p in sorted(modules.glob('SpecTecDecl*.lean'))]
    files += ['SpecTecAll.lean', 'SpecTecProofs.lean', 'SpecTecCases.lean']
    env = os.environ | {'LEAN_PATH': str(modules)}
    for index, name in enumerate(files):
        path = modules / name
        run(['lean', '-o', str(path.with_suffix('.olean')), str(path)], env=env, cwd=modules)
        if index % 32 == 0:
            print(f'Checked {index + 1}/{len(files)} modules', flush=True)
    client = modules / 'CastProof.lean'
    client.write_text('import SpecTecAll\nset_option maxRecDepth 4096\nset_option maxHeartbeats 4000000\n' + proof)
    run(['lean', str(client)], env=env, cwd=modules)
    print(f'Actual spec: all {len(files)} modules and imported OK/FAIL cast proofs passed')
    messages = sorted({line for line in source.stderr.splitlines() if line.startswith('error: Lean skeleton does not support')})
    print('Unsupported definitions remain explicit and their callers are pruned:')
    for message in messages:
        print(message)
