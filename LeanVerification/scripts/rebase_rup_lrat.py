#!/usr/bin/env python3
"""Rebase a RUP-only LRAT proof from a core CNF to a full CNF.

Lean's compact LRAT checker assigns learned-clause IDs by append order, while
drat-trim retains sparse solver IDs.  Given a core-to-full source-ID map, this
program maps core hints to full-input IDs and renumbers every learned clause
densely after the full input.  It deliberately rejects RAT groups: this keeps
the transformation small and auditable for the no-factor Kissat pipeline.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def parse_map(path: Path) -> list[int]:
    values = [int(line) for line in path.read_text(encoding="ascii").splitlines() if line]
    if not values or min(values) <= 0:
        raise ValueError(f"{path}: expected positive one-based clause IDs")
    return values


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proof", type=Path, help="text LRAT proof for the dense core CNF")
    parser.add_argument("core_map", type=Path, help="core-ID to full-ID map")
    parser.add_argument("full_clause_count", type=int, help="number of clauses in the full CNF")
    parser.add_argument("output", type=Path, help="rebased text LRAT proof")
    args = parser.parse_args()

    source_map = parse_map(args.core_map)
    core_clause_count = len(source_map)
    full_clause_count = args.full_clause_count
    learned: dict[int, int] = {}
    next_learned = full_clause_count + 1

    def mapped_id(old: int, line_no: int) -> int:
        if old <= 0:
            raise ValueError(f"LRAT line {line_no}: nonpositive clause ID {old}")
        if old <= core_clause_count:
            return source_map[old - 1]
        try:
            return learned[old]
        except KeyError as error:
            raise ValueError(f"LRAT line {line_no}: unknown learned clause ID {old}") from error

    additions = 0
    deletions = 0
    with args.proof.open("rt", encoding="ascii") as source, args.output.open(
        "wt", encoding="ascii"
    ) as output:
        for line_no, line in enumerate(source, start=1):
            fields = line.split()
            if not fields or fields[0] == "c":
                continue
            if len(fields) < 3:
                raise ValueError(f"LRAT line {line_no}: malformed action")

            old_action_id = int(fields[0])
            if fields[1] == "d":
                if fields[-1] != "0":
                    raise ValueError(f"LRAT line {line_no}: unterminated deletion")
                targets = [mapped_id(int(field), line_no) for field in fields[2:-1]]
                output.write("1 d " + " ".join(map(str, targets)) + " 0\n")
                deletions += 1
                continue

            if old_action_id <= core_clause_count:
                raise ValueError(f"LRAT line {line_no}: learned ID collides with input ID")
            try:
                clause_end = fields.index("0", 1)
            except ValueError as error:
                raise ValueError(f"LRAT line {line_no}: missing clause terminator") from error
            if fields[-1] != "0":
                raise ValueError(f"LRAT line {line_no}: unterminated hint list")

            hints = fields[clause_end + 1 : -1]
            if any(int(hint) < 0 for hint in hints):
                raise ValueError(f"LRAT line {line_no}: RAT groups are not supported")
            learned[old_action_id] = next_learned
            rebased_hints = [str(mapped_id(int(hint), line_no)) for hint in hints]
            clause = fields[1:clause_end]
            rendered_clause = " ".join(clause)
            output.write(
                f"{next_learned}" + (f" {rendered_clause}" if rendered_clause else "")
                + " 0 "
                + " ".join(rebased_hints)
                + " 0\n"
            )
            next_learned += 1
            additions += 1

    print(f"rebased {additions} additions and {deletions} deletions")


if __name__ == "__main__":
    main()
