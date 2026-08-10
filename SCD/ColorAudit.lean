/-
# The colour block is not the spatial block

`Axis.lean` restored point defects by showing the order parameter is an
unoriented axis.  That required a **uniaxial** scale pattern: one distinguished
direction and a degenerate remainder.  In three spatial dimensions the
degenerate remainder has exactly **two** members.

`Color.lean` derives, for a degenerate block of size `n`, that bound states have
`n` constituents and that constituent charges come in units of `1/n`.

Putting those together tempts an identification: *the colour block is the
spatial degeneracy block*.  It would be an attractive result — colour would then
be a consequence of geometry rather than an input.

**It is false, and this file records why.**

The uniaxial block in three dimensions has size two.  So the identification
predicts two-constituent bound states and charges in halves.  Baryons have
three constituents and quark charges come in thirds.  The identification is
therefore excluded — not weakened, excluded, by a factor that is not close.

What survives and what does not:

* `Color.lean` is untouched.  Its theorems are about a degenerate block of size
  `n` and remain correct for every `n`; it always said `n` was an input.
* What is excluded is the *route* that would have derived `n` from the spatial
  scale pattern.  That route gives `n = 2` and is refuted.
* Consequently colour, if the framework is to have it, is **not** a permutation
  of spatial directions.  It has to come from structure the framework does not
  currently contain.

This also removes an unstated worry: had the identification held, colour would
have been a spacetime symmetry rather than an internal one, which is exactly
the mixing that Coleman–Mandula forbids.  The framework failing to produce it is
the expected outcome, not a surprise.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

namespace SCD.ColorAudit

/-! ## What the two structures each fix -/

/-- The size of the degenerate block in a uniaxial pattern in three spatial
dimensions: one direction is distinguished, the other two are not. -/
def uniaxialBlockSize : ℕ := 2

/-- The number of constituents `Color.lean` predicts for a block of size `n`. -/
def boundStateSize (n : ℕ) : ℕ := n

/-- The charge quantum `Color.lean` predicts for a block of size `n`. -/
def chargeQuantum (n : ℕ) : ℚ := 1 / (n : ℚ)

/-- Observed baryon number: three constituents. -/
def observedBaryonNumber : ℕ := 3

/-- Observed quark charge quantum: thirds. -/
def observedChargeQuantum : ℚ := 1 / 3

/-! ## The identification and its refutation -/

/-- Under the identification, bound states would have two constituents. -/
theorem identification_predicts_two :
    boundStateSize uniaxialBlockSize = 2 := rfl

/-- And charges would come in halves. -/
theorem identification_predicts_halves :
    chargeQuantum uniaxialBlockSize = 1 / 2 := by
  norm_num [chargeQuantum, uniaxialBlockSize]

/-- **The identification is excluded by baryon number.** -/
theorem identification_fails_baryon :
    boundStateSize uniaxialBlockSize ≠ observedBaryonNumber := by
  simp only [boundStateSize, uniaxialBlockSize, observedBaryonNumber]
  omega

/-- **And by the charge quantum.**  Halves are not thirds, and not nearly. -/
theorem identification_fails_charge :
    chargeQuantum uniaxialBlockSize ≠ observedChargeQuantum := by
  simp only [chargeQuantum, uniaxialBlockSize, observedChargeQuantum]
  norm_num

/-- Collected: the spatial degeneracy block cannot be the colour block. -/
theorem spatial_block_is_not_colour_block :
    boundStateSize uniaxialBlockSize ≠ observedBaryonNumber
    ∧ chargeQuantum uniaxialBlockSize ≠ observedChargeQuantum :=
  ⟨identification_fails_baryon, identification_fails_charge⟩

/-! ## What would have been needed

Only a block of size three reproduces the observed pattern, and three is not
the size of the degenerate remainder in three spatial dimensions.  The value of
`n` is therefore not fixed by the geometry, and `Color.lean` was right to treat
it as an input. -/

/-- Only `n = 3` matches observation, on both counts at once. -/
theorem three_is_forced_by_data (n : ℕ) (hb : boundStateSize n = observedBaryonNumber) :
    n = 3 := hb

/-- And `n = 3` does reproduce the charge quantum, so the two observations are
consistent with a single block size — just not with the spatial one. -/
theorem three_matches_charge : chargeQuantum 3 = observedChargeQuantum := by
  norm_num [chargeQuantum, observedChargeQuantum]

/-- The gap, stated as a number: the geometry offers two where the data
requires three. -/
theorem geometry_offers_two_data_needs_three :
    uniaxialBlockSize = 2 ∧ observedBaryonNumber = 3 ∧ uniaxialBlockSize ≠ observedBaryonNumber :=
  ⟨rfl, rfl, by simp only [uniaxialBlockSize, observedBaryonNumber]; omega⟩

end SCD.ColorAudit
