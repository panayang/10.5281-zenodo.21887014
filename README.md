# The Scale-Coupled Dynamics (SCD) Theory

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21887014.svg)](https://doi.org/10.5281/zenodo.21887014)
[![Zulip Chat](https://img.shields.io/badge/chat-on%20Zulip-5e7ce2?logo=zulip&logoColor=white)](https://apich.zulipchat.com/)
[![Discord Server](https://img.shields.io/discord/1459399539403522074.svg?label=Discord&logo=discord&color=blue)](https://discord.gg/D5e2czMTT9)

Formal proof of the Scale-Coupled Dynamics (SCD) Theory: An axiomatic framework for the recovery of physical phenomena verified via Lean 4.

## Verifying

```
lake exe cache get
lake build                       # 0 errors
lake env lean SCD/Verify.lean    # #print axioms on all 1187 theorems
python3 tools/sync_report.py     # consistency check; exit 1 on drift
```

All 1187 theorems are audited: every one reduces to `propext`,
`Classical.choice` and `Quot.sound`, and none to `sorryAx`. The audit list, the
report's file table and its theorem index are **generated from the sources**, so
nothing can quietly fall out of them.

## Status

Read `SCD/Audit.lean` before relying on any result. It is the register of what
has been **retracted** (4), **narrowed in scope** (8), **cited without proof**
(3) and **assumed** (9, including A6′ and A7 — the count rose because the
register was audited, not because the framework got worse). The seven axioms are
stated together in `SCD/Postulates.lean`; `SCD.lean` is the intended reading
order.

`SCD/Anchor.lean` is the second thing to read: it applies one falsifiability test
to the framework's own list of predictions and finds four of the eight were
arithmetic on imported definitions. What survives is one free magnitude against
five falsifiable dimensionless statements, of which one discriminates against
general relativity and the Standard Model.

Two live empirical problems, both stated in `SCD/Data.lean`: DESI prefers an
evolving dark-energy equation of state at 2.8–4.2σ, and the framework's own
prediction in that sector — that `w` varies on the log-scale set by the
threshold spectrum — has never been computed as a curve, so the data can
neither confirm nor kill it. **A5 does not forbid an evolving `w`**; that
reading was withdrawn in `SCD/Scanning.lean` and is registered in `Audit` §V.e,
and this file quoted it for several revisions after it had been withdrawn. The
second problem: the no-horizon result implies a nonzero ringdown reflectivity
whose magnitude the framework cannot compute, while rapidly spinning remnants
bound it from above.

The report (Chinese, ~95pp) is `paper/SCD.pdf`.
