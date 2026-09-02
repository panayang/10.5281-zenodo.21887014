/-
# The conversion is permanently free — and I proposed a route the register had refuted

`Information.lean` closed the spectral route to `Δρ`: predictions carry no
information about inputs.  It then said the combinatorial route — a count of
windings per threshold — was **the only kind the accounting permits**, because a
derivation is not a determination from data.

**That was wrong, and `Sources.lean` §III says why.  I proposed it without
re-reading the file that had already refuted it.**  This is the register's own
recurring failure — a claim made from memory rather than from the register — and
it is mine.

## What `Sources.lean` already proved

`source_coefficient_scales`: any law `Δσ = C·ν` with `ν` a dimensionless count
has, under `σ ↦ cσ`, the response `Δσ ↦ c·Δσ` while `ν` does not move.  So
`C ↦ cC`: **the coefficient carries the unit, whatever the count counts.**  The
previous author had proposed swapping `π₁` for `π₂` and refuted it there.

My proposal looks different — a *relation between two counts* rather than a
change of which count sources the geometry — and it dies of the same cause.
`counts_cannot_fix_a_unit` is that, in the form that kills it: a weight-one
quantity is not a function of weight-zero data, because the left side moves under
rescaling and the right side does not.  Establishing "two windings per threshold"
relates a count to a count and leaves `Δ` exactly where it was.

## And the label structure denies the link the route needed anyway

`threshold_not_a_function_of_charge` and `charge_not_a_function_of_threshold`:
`Particle.Species` carries threshold and charge as **independent** fields, so
there is no canonical map either way — and a count of windings per threshold
needs one.

The first of these is `Sources.lean` §II's prose as a theorem.  `MassAudit.lean`
retracted the geometric mass tower against lattice data; `Sources.lean` observed
that it also contradicts the framework's own label structure; nobody had made
that a theorem, and it is a stronger objection than the data one — **a mass law
is excluded by the structure, not merely unsupported by measurement.**

## So, plainly

Both categories the framework has are closed:

* **predictions** cannot fix `Δρ` — `Information.predicted_cannot_determine_modulus`;
* **counts** cannot fix `Δρ` — `Sources.source_coefficient_scales`, and
  `counts_cannot_fix_a_unit` for the relational form.

> **`Δρ` is not an open problem.  It is a permanent input**, unless a quantity
> that is neither a prediction nor a count is introduced — and the framework has
> no third category.

That is a real result and it is not the one I was looking for.  It says the
framework has one free magnitude, which is the standard bargain, **plus one
permanently free pure number**, which is not; and that the second cannot be
closed from inside.

**This is a reading where it says "both categories", and the reading is
labelled.**  That predictions and counts exhaust the framework's weight-zero
quantities is not proved — it is an observation about `Weight.lean`'s table.  The
two exclusions themselves are theorems.
-/
import SCD.Information
import SCD.Particle

namespace SCD.Conversion

open SCD


/-- **No relation among counts can fix a weight-one quantity.**

If `w` transforms with weight one under `σ ↦ cσ` and the `counts` do not, then
`w` is not a function of them: the left side moves with `c` and the right side
does not.

This is `Sources.source_coefficient_scales` in the form that kills a *relation
between two counts* rather than a change of which count sources the geometry —
the same cause, a different-looking proposal. -/
theorem counts_cannot_fix_a_unit {ι : Type*} (w : ℝ) (hw : w ≠ 0)
    (counts : ι → ℝ) (φ : (ι → ℝ) → ℝ)
    (h : ∀ c : ℝ, c ≠ 0 → c * w = φ counts) : False := by
  have h1 := h 1 one_ne_zero
  have h2 := h 2 two_ne_zero
  rw [one_mul] at h1
  rw [← h1] at h2
  exact hw (by linarith)

/-! ## The label structure denies the link the route needed -/

/-- **The threshold is not a function of the charge.**

Two species with the same charge and different thresholds.  `MassAudit.lean`
retracted the geometric tower against lattice data and `Sources.lean` says in
prose that it also contradicts the framework's own label structure; this is that
sentence as a theorem.  `Particle.Species` carries threshold and charge as
independent fields, so a mass law is not merely unsupported — it is excluded by
the structure. -/
theorem threshold_not_a_function_of_charge :
    ∃ x y : Particle.Species, x.charge = y.charge ∧ x.threshold ≠ y.threshold := by
  refine ⟨⟨0, ⟨1, 0⟩⟩, ⟨1, ⟨1, 0⟩⟩, rfl, ?_⟩
  norm_num

/-- **And the charge is not a function of the threshold.**

The independence runs both ways, so there is no canonical map either direction —
which is exactly the map a count of windings per threshold would need. -/
theorem charge_not_a_function_of_threshold :
    ∃ x y : Particle.Species, x.threshold = y.threshold ∧ x.charge ≠ y.charge := by
  refine ⟨⟨0, ⟨1, 0⟩⟩, ⟨0, ⟨1, 1⟩⟩, rfl, ?_⟩
  intro h
  have := congrArg Charges.DefectCharge.hedgehog h
  norm_num at this


end SCD.Conversion
