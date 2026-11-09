# Pinned source snapshots

The `.lean.txt` files are documentary snapshots from Formal Conjectures PR
#7841 at commit `9f2a84284e69f992c113f894869cd7cdf292390f`. They are not
compiled modules or proof dependencies. In particular, the original admitted
conjecture is retained here only as evidence of its exact statement.

`source-bindings.json` records their original paths and SHA-256 hashes.
`scripts/check-submission.py` checks those hashes and the literal theorem
statement in both Challenge and Solution. The current compiled model is
ported to Lean 4.35 as explained in `docs/provenance.md`. Comparator checks
the compiled Challenge against the compiled Solution.
