/-
# Time is the direction the scale is running

The audit listed the Lorentz signature as an unexplained input: nothing said
why exactly one direction should be distinguished, nor why that one.  Treating
it as an input was itself inertia — it is an input in theories where the metric
is primitive, and here the metric is not primitive.

Ask instead what could possibly single out a direction in a world whose only
content is scale.  There is exactly one candidate.  A6 says the universe
dissipates: the scale is *drifting*.  A drift has a direction.

**Time is the direction along which the scale actually changes; space is the
directions along which it does not.**

That is enough to fix the shape of the signature without postulating it:

* `codim_ker_eq_one` — a nonzero drift distinguishes exactly **one** direction,
  its kernel accounting for all the rest.  The split is `1 + (n−1)`, which is
  the Lorentzian shape;
* `no_time_of_no_drift` — if the scale is not drifting, **no** direction is
  distinguished.  A closed, non-dissipating universe has no time direction at
  all;
* `drift_direction_unique` — any two directions along which the scale changes
  at the same rate differ by a spatial one, so "the time direction" is well
  defined modulo space.

The signature is therefore not `(−,+,+,+)` by decree.  It is `1 + (n−1)`
because a drift is a single linear functional, and it exists at all only
because the universe is open.  A5 and A6 between them do the work that a
postulated `η` was doing.

What is still *not* derived: the dimension `n` itself, and the sign convention
that makes the distinguished direction timelike rather than merely
distinguished.  Those remain inputs and are registered as such.
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace SCD.Signature

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-! ## The drift -/

/-- The **scale drift**: how fast the log-scale changes along each direction.
By A6 this is not identically zero — the universe dissipates.  It is a linear
functional and nothing more; no metric is needed to state it. -/
abbrev Drift (V : Type*) [AddCommGroup V] [Module ℝ V] := V →ₗ[ℝ] ℝ

/-- A direction is **spatial** when the scale does not change along it. -/
def IsSpatial (φ : Drift V) (v : V) : Prop := φ v = 0

/-- The spatial directions form a subspace — space is what the drift cannot
distinguish. -/
def spatial (φ : Drift V) : Submodule ℝ V := LinearMap.ker φ


/-! ## A drift distinguishes exactly one direction -/

/-- **The signature shape is `1 + (n−1)`.**

A nonzero drift has one-dimensional range, so by rank–nullity its kernel has
codimension exactly one.  Precisely one direction is distinguished and all the
others are not — which is the Lorentzian shape, obtained from dissipation
rather than postulated. -/
theorem codim_ker_eq_one (φ : Drift V) (hφ : φ ≠ 0) :
    finrank ℝ (spatial φ) + 1 = finrank ℝ V := by
  have hrange : finrank ℝ (LinearMap.range φ) = 1 := by
    have hsurj : LinearMap.range φ = ⊤ := by
      have hex : ∃ v : V, φ v ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hφ (LinearMap.ext fun v => by simp [hc v])
      obtain ⟨v, hv⟩ := hex
      apply LinearMap.range_eq_top.mpr
      intro c
      refine ⟨(c / φ v) • v, ?_⟩
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
    rw [hsurj]
    simpa using finrank_self ℝ
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange] at hrn
  show finrank ℝ (LinearMap.ker φ) + 1 = finrank ℝ V
  omega

/-- **Without dissipation there is no time.**

If the scale is not drifting, every direction is spatial: nothing distinguishes
one from another, and there is no time direction to be had.  Time is not a
dimension the theory is given — it is the fact that the universe is open. -/
theorem no_time_of_no_drift (φ : Drift V) (hφ : φ = 0) : ∀ v : V, IsSpatial φ v := by
  intro v
  simp only [IsSpatial, hφ, LinearMap.zero_apply]

/-- Equivalently: no drift means space is everything. -/
theorem spatial_eq_top_of_no_drift (φ : Drift V) (hφ : φ = 0) : spatial φ = ⊤ := by
  rw [spatial, hφ, LinearMap.ker_zero]

/-- With a drift, space is *not* everything: a time direction exists. -/
theorem spatial_ne_top_of_drift (φ : Drift V) (hφ : φ ≠ 0) : spatial φ ≠ ⊤ := by
  intro hcon
  apply hφ
  ext v
  have : v ∈ spatial φ := by rw [hcon]; trivial
  simpa [spatial, LinearMap.mem_ker] using this

/-! ## The time direction is well defined -/

/-- **Any two directions with the same drift rate differ by a spatial one.**

So "the time direction" is unambiguous modulo space: the drift determines a
single distinguished direction up to the addition of directions along which
nothing changes. -/
theorem drift_direction_unique (φ : Drift V) (u v : V) (h : φ u = φ v) :
    u - v ∈ spatial φ := by
  simp only [spatial, LinearMap.mem_ker, map_sub, h, sub_self]

/-- Rescaling the drift — which is a change of fiducial, unobservable by A5 —
leaves the spatial subspace untouched.  The split into time and space is
therefore fiducial-independent, as any physical statement must be. -/
theorem spatial_smul (φ : Drift V) {c : ℝ} (hc : c ≠ 0) : spatial (c • φ) = spatial φ := by
  ext v
  simp only [spatial, LinearMap.mem_ker, LinearMap.smul_apply, smul_eq_mul,
    mul_eq_zero, hc, false_or]

/-- Collected: a dissipating universe has exactly one time direction and
`n − 1` spatial ones, and a non-dissipating one has no time at all. -/
theorem signature_from_dissipation (φ : Drift V) :
    (φ ≠ 0 → finrank ℝ (spatial φ) + 1 = finrank ℝ V) ∧
    (φ = 0 → spatial φ = ⊤) :=
  ⟨codim_ker_eq_one φ, spatial_eq_top_of_no_drift φ⟩

end SCD.Signature
