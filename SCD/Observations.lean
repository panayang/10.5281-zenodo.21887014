/-
# The two identifications, named — and what naming a debt does not do

`Anchor.lean` records the `w`/`H₀` link as three inputs deep: the scanning
hypothesis, plus two identifications that "appear nowhere in Lean" — that a
`w₀wₐ` fit measures the response's fractional evolution, and that the
ladder-versus-ruler discrepancy measures the density's.  `Bridge.lean` removed
the first input.  This file gives the other two a type.

## What formalising an identification can and cannot be

It cannot be a proof.  No algebra decides what an astronomical pipeline reports.
What it can be is the **A6′ treatment**: the identification becomes an explicit
hypothesis carried visibly by everything downstream, so that a reader asking
"does this rest on the axioms alone?" is answered by the type and not by a
search.

And there is a trap in doing it, which the first draft of this file fell into.
Written as a *structure* with the observed number as a field, an identification
is **trivially inhabited** — one can always name a real equal to a formula — and
constrains nothing.  Written with the observed number as a **parameter**, it is a
constraint on a number the world supplies.  `fit_identification_is_a_constraint`
exhibits a report that fails it, which is what makes it a claim.

## What it buys, which is more than tidiness

`observations_agree`: given both identifications, `Scanning.two_anomalies_one_number`
makes the two **measured** numbers equal.  The theoretical quantities cancel and
what is left is a relation between two measurements made by different communities
with different instruments.

> It predicts neither number.  It says they are the same number.

That is the strongest form this claim can take, and it is two-sided:
`falsified_by_one_anomaly_alone` and `falsified_by_the_other_alone`.  An evolving
`w` with agreeing distance ladders kills it; agreeing `w` with discrepant ladders
kills it too.

## What it does not do, and this is the point of the section

**Naming a debt does not pay it.**  The link is still two inputs deep and stays
out of `Anchor.lean`'s prediction ledger.  What has changed is that the two
inputs are now *typed hypotheses* rather than sentences in a docstring — the same
change A6′ underwent, and the register's own account of why that change matters:
nothing is hidden at the type level.

**And the division of labour is now exact.**  The framework has produced a
testable relation between two observations and named precisely what someone else
must supply to make it a test: that these two pipelines report these two
fractions.  That is a question for cosmologists, not for this development, and
saying so is not a retreat — it is the correct location of the remaining work.
-/
import SCD.Bridge
import SCD.Scanning

namespace SCD.Observations

open SCD


/-- **What a `w₀wₐ` fit is taken to measure.**

The first of `Anchor.lean`'s two unformalised identifications, given a type.  It
is not proved and cannot be — no algebra decides what an astronomical fit
measures.

**`obs` is a parameter**, the number the pipeline actually reports, so this is a
*constraint* on that number and not a definition of one.  Written as a structure
with `obs` as a field it would be trivially inhabited — one can always name a
real equal to a formula — and would constrain nothing. -/
def FitReadsRate (obs κ : ℝ) (rho : ℝ → ℝ) (t t' : ℝ) : Prop :=
  obs = (Scanning.scanRate κ rho t - Scanning.scanRate κ rho t')
          / Scanning.scanRate κ rho t'

/-- **What the ladder-versus-ruler discrepancy is taken to measure.**

The second identification, likewise a constraint on a reported number. -/
def LadderReadsDensity (obs : ℝ) (rho : ℝ → ℝ) (t t' : ℝ) : Prop :=
  obs = (rho t - rho t') / rho t'

/-- **Given both, the two measured numbers must agree.**

`Scanning.two_anomalies_one_number` equates the two *theoretical* fractions; with
the identifications named, the theory drops out and what is left is a relation
**between two measurements made by different communities with different
instruments**.

That is the strongest form the claim can take.  It predicts neither number; it
says they are the same number. -/
theorem observations_agree {o₁ o₂ κ : ℝ} {rho : ℝ → ℝ} {t t' : ℝ} (hκ : κ ≠ 0)
    (h₁ : FitReadsRate o₁ κ rho t t') (h₂ : LadderReadsDensity o₂ rho t t') :
    o₁ = o₂ := by
  rw [FitReadsRate] at h₁
  rw [LadderReadsDensity] at h₂
  rw [h₁, h₂, Scanning.two_anomalies_one_number κ hκ rho t t']

/-- **And it dies if one anomaly appears without the other.**

`Scanning.lean` states the falsification in words; with the identifications typed
it is a theorem.  An evolving `w` with agreeing distance ladders kills the
picture. -/
theorem falsified_by_one_anomaly_alone {o₁ o₂ κ : ℝ} {rho : ℝ → ℝ} {t t' : ℝ}
    (hκ : κ ≠ 0) (h₁ : FitReadsRate o₁ κ rho t t')
    (h₂ : LadderReadsDensity o₂ rho t t') (hne : o₁ ≠ 0) (hz : o₂ = 0) : False :=
  hne ((observations_agree hκ h₁ h₂).trans hz)

/-- **The other way round too**, so the test is two-sided and not a one-way
consistency check. -/
theorem falsified_by_the_other_alone {o₁ o₂ κ : ℝ} {rho : ℝ → ℝ} {t t' : ℝ}
    (hκ : κ ≠ 0) (h₁ : FitReadsRate o₁ κ rho t t')
    (h₂ : LadderReadsDensity o₂ rho t t') (hz : o₁ = 0) (hne : o₂ ≠ 0) : False :=
  hne ((observations_agree hκ h₁ h₂).symm.trans hz)

/-- **And the constraint is not vacuous**: a reported number failing it exists.

If the identification held of every number it would say nothing.  This exhibits a
world and a report that disagree, which is what makes `FitReadsRate` a claim. -/
theorem fit_identification_is_a_constraint :
    ¬ FitReadsRate 1 1 (fun _ => 1) 0 1 := by
  rw [FitReadsRate]
  norm_num [Scanning.scanRate]


end SCD.Observations
