#!/usr/bin/env python3
"""Check typed callback propagation and relation SCC construction."""

import argparse
import json
from pathlib import Path
import subprocess


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    args = parser.parse_args()

    result = subprocess.run(
        [str(args.exe.resolve()), "--dump-relation-graph", str(args.source)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    graph = json.loads(result.stdout)

    components = {frozenset(component["relations"]): component
                  for component in graph["components"]}
    recursive = frozenset({"$invoke", "$forward", "$recursive"})
    assert recursive in components, components
    assert components[recursive]["recursive"] is True
    assert frozenset({"A", "B"}) in components
    assert components[frozenset({"A", "B"})]["negative_cycle"] is True
    assert frozenset({"$unused"}) in components
    assert frozenset({"$identity"}) in components

    edges = {(edge["source"], edge["target"], edge["kind"])
             for edge in graph["edges"]}
    assert ("$recursive", "$forward", "positive") in edges
    assert ("$forward", "$invoke", "positive") in edges
    assert ("$invoke", "$recursive", "callback") in edges
    assert ("A", "B", "negative") in edges
    assert ("B", "A", "negative") in edges
    assert not any(source == "$invoke" and target == "$unused"
                   for source, target, _ in edges)
    assert not any(source == "$invoke" and target == "$identity"
                   for source, target, _ in edges)

    sites = {(site["relation"], site["parameter"], tuple(site["targets"]),
              site["external"])
             for site in graph["callback_sites"]}
    assert ("$invoke", 0, ("$recursive",), True) in sites
    print("relation graph: typed transitive callback SCCs checked")


if __name__ == "__main__":
    main()
