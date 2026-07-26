# Size-11 LRAT certificate

This directory contains the certificate for the reviewer-facing theorem
`Wilkies.no_order11_generalCountermodel`.

`wilkies_11.lrat` is a RUP-only LRAT replay for the full, normalized
`Wilkies.encode 11` CNF. Kissat was run with `--no-factor`, and `drat-trim`
emitted a proof over the full input formula. The source-clause IDs are kept
unchanged and `scripts/rebase_rup_lrat.py` renumbers learned-clause IDs densely
after the full CNF. The final replay is checked directly by Lean core's LRAT
checker.

`Wilkies/LRAT11.lean` imports this certificate with
[LRAT-Catcher](https://github.com/leansolving/lrat-catcher)'s
`lrat_reflect_cnf` command and checks it directly against the Lean-defined
CNF `toStdCNF (encode 11)`.  The command uses Lean core's verified LRAT
checker through `native_decide`; Kissat and `drat-trim` are certificate
producers, not trusted proof steps.

## Replaying with progress logging

```sh
zsh scripts/build_lrat11_with_progress.sh
```

The script logs elapsed time and the resident memory of the Lean worker every
30 seconds.  It also gives an estimated remaining time from a successful
757-second run.  This is necessarily an estimate: `native_decide` treats the
verified LRAT checker as one closed computation and does not expose a
per-action progress counter.

Expected SHA-256 hashes:

```text
b50556389f68aa0aea82c5e7706f58a066efe3b90cf5f719054ec16f467255c0  wilkies_11.lrat
```

On the development machine, LRAT-Catcher replay took 757 seconds.  Its axiom
audit contains Lean's standard logical axioms (`propext`, `Classical.choice`,
`Quot.sound`) and the expected `native_decide` evaluation axiom only; there is
no solver or project UNSAT axiom.
