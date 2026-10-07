#!/usr/bin/env python3
"""Compare source declaration blocks with generated Lean sections and owners.

Source block lines include blank/comment lines up to the next declaration.
Generated relation helpers are charged to the source name before the first ':'.
Common infrastructure and type declarations are reported separately.
"""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re


SOURCE_DECL = re.compile(
    r'^\s*(?:(?:extern|builtin)\s+)?(?:'
    r'(?:tbl\s+)?(?:dec|def)\s+(\$[^\s(<:]+)|'
    r'(?:relation|rule|rulegroup)\s+([^\s/:{]+)|'
    r'(?:syntax|var|hint)\b)'
)
NAME = r'(?:«([^»]+)»|([^\s({]+))'


def source_stats(root):
    sizes = Counter()
    paths = defaultdict(set)
    files = sorted(root.rglob('*.watsup'))
    lines = nonblank_lines = byte_count = 0
    for path in files:
        content = path.read_text()
        byte_count += path.stat().st_size
        current = None
        for line in content.splitlines():
            lines += 1
            nonblank_lines += bool(line.strip())
            declaration = SOURCE_DECL.match(line)
            if declaration:
                current = declaration.group(1) or declaration.group(2)
                if current:
                    paths[current].add(str(path))
            if current:
                sizes[current] += 1
    return {'files': len(files), 'lines': lines, 'nonblank_lines': nonblank_lines,
            'bytes': byte_count}, sizes, paths


def analyze(root, lean):
    source, source_lines, source_paths = source_stats(root)
    content = lean.read_text()
    lines = content.splitlines(keepends=True)
    atom = next(i for i, line in enumerate(lines) if line.startswith(('inductive Atom :', 'inductive «Atom:')))
    program = next(i for i, line in enumerate(lines) if line.startswith(('inductive InProgram :', 'inductive «InProgram:')))
    public = next(i for i in range(program + 1, len(lines)) if lines[i].startswith('def '))
    theorems = next(i for i in range(public, len(lines))
                    if lines[i].startswith(('theorem ', 'namespace ')))
    boundaries = [0, atom, program, public, theorems, len(lines)]
    labels = ['common_and_types', 'atoms', 'program', 'public_relations', 'rule_theorems']
    sections = {}
    for label, start, end in zip(labels, boundaries, boundaries[1:]):
        sections[label] = {'lines': end - start,
                           'bytes': len(''.join(lines[start:end]).encode())}
    owner_lines, owner_bytes = Counter(), Counter()

    def add(match, line):
        owner = (match.group(1) or match.group(2)).split(':', 1)[0]
        owner_lines[owner] += 1
        owner_bytes[owner] += len(line.encode())

    for line in lines[atom:program]:
        match = re.match(r'  \| ' + NAME, line)
        if match and not line.startswith('  | «group:'):
            add(match, line)
        match = re.match(r'@\[match_pattern\] abbrev Atom\.' + NAME, line)
        if match:
            add(match, line)
    rule_owners = {}
    for line in lines[program:public]:
        match = re.search(r'head := \((?:@)?Atom\.' + NAME, line)
        if match:
            add(match, line)
            constructor = re.match(r'  \| (\S+)', line)
            if constructor:
                rule_owners[constructor.group(1)] = match
        alias = re.match(r'abbrev InProgram\.(\S+)', line)
        if alias and alias.group(1) in rule_owners:
            add(rule_owners[alias.group(1)], line)
    current = None
    for line in lines[public:]:
        match = re.match(r'theorem (?:«([^»]+)»|([^\s.«]+))\.', line)
        if match is None:
            match = re.match(r'(?:def|namespace) ' + NAME, line)
        if match:
            current = match
        if current:
            add(current, line)
    duplicates = [line for line in lines if line.startswith('  exact SpecTecWFS.Holds.rule ({')]
    return {
        'source': source,
        'generated': {
            'lines': len(lines), 'bytes': lean.stat().st_size,
            'nonblank_lines': sum(bool(line.strip()) for line in lines),
            'atom_constructors': sum(line.startswith('  | ') and not line.startswith('  | «group:')
                                     for line in lines[atom:program]),
            'atom_wrapper_constructors': sum(line.startswith('  | «group:')
                                             for line in lines[atom:program]),
            'program_constructors': sum(line.startswith('  | ') and not line.startswith('  | «group:')
                                        for line in lines[program:public]),
            'program_wrapper_constructors': sum(line.startswith('  | «group:')
                                                for line in lines[program:public]),
            'repeated_rule_proof_lines': len(duplicates),
            'repeated_rule_proof_bytes': sum(len(line.encode()) for line in duplicates),
        },
        'sections': sections,
        'owners': [
            {'name': name, 'source_block_lines': source_lines[name],
             'lean_lines': owner_lines[name], 'lean_bytes': byte_count,
             'source_files': sorted(source_paths[name])}
            for name, byte_count in owner_bytes.most_common()
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec', required=True, type=Path)
    parser.add_argument('--lean', required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(analyze(args.spec, args.lean), indent=2, ensure_ascii=False))


if __name__ == '__main__':
    main()
