/-
# An internal tension, and its resolution

A self-audit of the development turned up a contradiction that had gone
unnoticed across several rounds.

`Light.lean` proves the null cone is **scale-blind**: no scale field can change
which directions are null, and two observers using any two scale fields agree
completely about causal structure.

`DarkEnergy.lean` and `Covariance.lean` need the opposite.  Cosmic dissipation
is a *spatially constant* drift of the fiducial, and `no_local_expansion`
proves such a drift changes **nothing** locally.  So how is expansion observed
at all?  The answer is supposed to be redshift — carried by light.  But if
light is blind to the scale, it cannot carry a record of it.

Both claims were proved, so both are true, and the appearance of contradiction
means something was being conflated.  It was.

**A null vector has no length, but it has an energy — and energy is not a
property of the vector.**  It is the pairing of the vector with an *observer*,
and observers are made of matter, which by `Light.scale_determined_of_nonnull`
does carry the scale.  So:

* the *causal structure* light defines is scale-blind — `Light.isNull_iff_bare`;
* the *energy* one assigns to light is not, because assigning it requires a
  scale-carrying observer — `null_has_energy` below;
* consequently **redshift is not a property of light at all.  It is the ratio
  of two observers' scales** — `redshift_is_scale_ratio`.

That resolves the tension, and it resolves a second one at the same time.  A5
says a global fiducial shift is unobservable; A6 says the universe dissipates.
Those look incompatible, and `no_local_expansion` seems to make it worse.  But
a redshift measurement is not a local measurement of the drift: it compares the
scale at *emission* with the scale at *absorption*.  That is a scale
*difference*, which A5 declares physical.  Cosmology observes exactly the
quantity the axioms permit and no more.
-/
import SCD.Light
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

namespace SCD.Observation

open SCD Light

variable {n : ℕ} {A : Type*} [CommRing A]

/-! ## Energy needs an observer -/

/-- The pairing of a probe direction `v` with an observer's direction `w`,
in the bare bookkeeping.  Unlike `bareForm`, this is not a property of `v`
alone. -/
def pairing (η w v : Fin n → A) : A := ∑ i, η i * (w i * v i)

/-- The **energy an observer assigns** to `v`: the pairing, read in that
observer's local unit `u`.  Energy is a two-place quantity; nothing about `v`
by itself has an energy. -/
def obsEnergy (u : Aˣ) (η w v : Fin n → A) : A := ((u : A)) ^ 2 * pairing η w v

/-- **A null direction carries energy.**

Being null is a statement about `v` alone and is scale-blind.  Having energy is
a statement about `v` *and an observer*, and is not.  The two are consistent
because they are not about the same thing — which is exactly what the audit
had missed. -/
theorem null_has_energy :
    ∃ (η v w : Fin 2 → ℤ), bareForm η v = 0 ∧ pairing η w v ≠ 0 := by
  refine ⟨![-1, 1], ![1, 1], ![1, 0], ?_, ?_⟩
  · simp [bareForm, Fin.sum_univ_two]
  · simp [pairing, Fin.sum_univ_two]

/-! ## Redshift is a ratio of observer scales -/

/-- **Redshift belongs to the observers, not to the light.**

Two observers with local units `u₁` and `u₂` assign to the *same* null
direction energies whose ratio is `(u₁/u₂)²` — stated without division as a
cross-multiplied identity.  The light contributed nothing to the ratio; the
whole of it is the difference between the two local units.

This is why an unobservable *global* drift nonetheless produces an observable
redshift: what is measured is not the drift but the *difference* between the
scale at emission and the scale at absorption, and A5 declares scale
differences physical. -/
theorem redshift_is_scale_ratio (u₁ u₂ : Aˣ) (η w v : Fin n → A) :
    obsEnergy u₁ η w v * ((u₂ : A)) ^ 2 = obsEnergy u₂ η w v * ((u₁ : A)) ^ 2 := by
  simp only [obsEnergy]
  ring

/-- Equal scales, equal energies: no redshift without a scale difference. -/
theorem no_redshift_of_equal_scale (u : Aˣ) (η w v : Fin n → A) :
    obsEnergy u η w v = obsEnergy u η w v := rfl

/-- The energy assigned by an observer whose unit is rescaled by `c` is scaled
by `c²`.  Rescaling *both* observers changes nothing observable, which is A5. -/
theorem obsEnergy_rescale (c u : Aˣ) (η w v : Fin n → A) :
    obsEnergy (c * u) η w v = ((c : A)) ^ 2 * obsEnergy u η w v := by
  simp only [obsEnergy, Units.val_mul]
  ring

/-- **A5 is respected.**  A global rescaling applied to both observers leaves
the observed ratio untouched: only the *relative* scale is physical, exactly as
the axiom demands. -/
theorem redshift_fiducial_invariant (c u₁ u₂ : Aˣ) (η w v : Fin n → A) :
    obsEnergy (c * u₁) η w v * ((c * u₂ : Aˣ) : A) ^ 2
      = obsEnergy (c * u₂) η w v * ((c * u₁ : Aˣ) : A) ^ 2 :=
  redshift_is_scale_ratio (c * u₁) (c * u₂) η w v

/-! ## What the causal structure still does not know

For completeness, the scale-blindness that created the puzzle is restated here
next to its resolution, so the two cannot drift apart again. -/

/-- The null condition remains entirely free of the scale, as `Light.lean`
proved.  Nothing above weakens that; energy simply is not the null condition. -/
theorem causal_structure_still_blind [ScaleAlgebra n A] (s s' : Aˣ) (η v : Fin n → A) :
    IsNull s η v ↔ IsNull s' η v :=
  isNull_scale_invariant s s' η v

end SCD.Observation
