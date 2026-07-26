#!/usr/bin/env python3
"""Map a DRAT-trim core back to equivalent source DIMACS clause IDs.

`drat-trim -c` renumbers—and may reorder—the selected source clauses.  This
program writes, one per core clause, a distinct one-based ID of an identical
clause in the full input formula.
"""

from __future__ import annotations

import argparse
from collections import deque
from collections.abc import Iterator
from pathlib import Path


def dimacs_clauses(path: Path) -> Iterator[tuple[int, ...]]:
    clause: list[int] = []
    with path.open("rt", encoding="ascii") as handle:
        for line in handle:
            stripped = line.strip()
            if not stripped or stripped[0] in "cp":
                continue
            for token in stripped.split():
                literal = int(token)
                if literal == 0:
                    yield tuple(clause)
                    clause.clear()
                else:
                    clause.append(literal)
    if clause:
        raise ValueError(f"{path}: final clause is missing its terminating 0")


def canonical_clause(clause: tuple[int, ...]) -> tuple[int, ...]:
    """Use clause semantics, not DIMACS literal presentation order, as the key."""
    return tuple(sorted(clause))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("full", type=Path, help="full normalized DIMACS input")
    parser.add_argument("core", type=Path, help="ordered core produced by drat-trim -c")
    parser.add_argument("output", type=Path, help="one-based full clause IDs, one per core clause")
    args = parser.parse_args()

    core = list(dimacs_clauses(args.core))
    candidates: dict[tuple[int, ...], deque[int]] = {
        canonical_clause(clause): deque() for clause in core
    }
    for full_index, full_clause in enumerate(dimacs_clauses(args.full), start=1):
        if (ids := candidates.get(canonical_clause(full_clause))) is not None:
            ids.append(full_index)

    mapped = 0
    with args.output.open("wt", encoding="ascii") as output:
        for core_index, core_clause in enumerate(core, start=1):
            try:
                output.write(f"{candidates[canonical_clause(core_clause)].popleft()}\n")
            except IndexError as error:
                raise ValueError(
                    f"core clause {core_index} has no unused identical clause in {args.full}"
                ) from error
            mapped += 1

    print(f"mapped {mapped} core clauses")


if __name__ == "__main__":
    main()
