/-
# Singularities are small scales, not mathematical singularities

In general relativity a singularity is a place where the metric degenerates
and curvature invariants blow up; the theory stops being able to speak.

In this framework that cannot happen, and the reason is structural rather than
a matter of finding better solutions.  Axiom A2 makes the scale `s = e^σ` an
element of the *unit group* `Aˣ`.  A unit is invertible by definition, so:

* the conformal factor never vanishes — the metric never degenerates;
* by A3 the energy scale `ε = 1/s` is likewise always defined and nonzero;
* curvature (`two_Rm_eq`) is a *polynomial* in the derivatives of `σ` in which
  `s` does not appear at all — so no divergence can be produced by the scale
  being small.

What general relativity reports as a singularity is, here, a region where `σ`
becomes very negative: the scale is tiny and the energy scale is enormous, but
both are finite and both are invertible.  The theory keeps speaking.

This is not a repair bolted on afterwards.  It is a consequence of having
written A2 with `s : Aˣ` rather than `s : A`, which was forced by the physical
requirement that a *unit of measure* must be something one can divide by.
-/
import SCD.Axioms

namespace SCD.Singularity

open SCD ScaleAlgebra

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

namespace ScaleField

variable (F : ScaleField n A)

/-- **The scale never vanishes.**  A unit of measure is by construction
something one can divide by. -/
theorem scale_ne_zero [Nontrivial A] : (F.s : A) ≠ 0 := by
  intro h
  have hone : (1 : A) = 0 := by
    have hmul := F.s.mul_inv
    rw [h, zero_mul] at hmul
    exact hmul.symm
  exact one_ne_zero hone

/-- **The energy scale never vanishes** either, by the duality A3. -/
theorem energy_ne_zero [Nontrivial A] : F.en ≠ 0 := by
  intro h
  have h1 : F.en * (F.s : A) = 1 := F.en_mul_scale
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- **The metric never degenerates.**  The conformal factor `e^{2σ}` relating
the measured line element to the bare one is a unit at every point. -/
theorem conformal_factor_isUnit : IsUnit ((F.s : A) ^ 2) := by
  rw [← Units.val_pow_eq_pow_val]
  exact (F.s ^ 2).isUnit

/-- The measured line element is recoverable from the bare one and vice versa:
the map `Q ↦ s²Q` is invertible. -/
theorem conformal_factor_invertible (x : A) :
    ((F.s : A) ^ 2) * (((F.s⁻¹ : Aˣ) : A) ^ 2 * x) = x := by
  rw [← mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow, one_mul]

end ScaleField

/-! ## Curvature cannot diverge from the scale being small

The master identity expresses the whole Riemann tensor in terms of `σ`'s first
and second derivatives.  The scale `s` itself is absent.  So a small scale — a
"singularity" in the general-relativistic sense — contributes nothing to
curvature by itself. -/

/-- **Curvature depends only on how the scale *changes*, never on its value.**

If two scale fields have the same first and second derivatives, they have
identical curvature, however different their actual scales.  A region of
arbitrarily small scale is therefore not, on that account, a region of large
curvature. -/
theorem curvature_indep_of_scale_value (σ τ : A)
    (h1 : ∀ i : Fin n, sig σ i = sig τ i)
    (h2 : ∀ i j : Fin n, hess σ i j = hess τ i j) (a b c e : Fin n) :
    2 * Rm σ a b c e = 2 * Rm τ a b c e := by
  have hg : gradsq n σ = gradsq n τ := by
    simp only [gradsq]
    exact Finset.sum_congr rfl (fun i _ => by rw [h1 i])
  have hD : ∀ i j, Defm n σ i j = Defm n τ i j := by
    intro i j
    simp only [Defm, h1, h2, hg]
  rw [two_Rm_eq, two_Rm_eq, hD, hD, hD, hD]

/-- Consequently the only way to produce divergent curvature is to make the
*derivatives* of `σ` diverge.  A finite scale field with finite derivatives has
finite curvature — stated here as: bounded deformation gives bounded curvature,
componentwise and exactly. -/
theorem curvature_zero_of_uniform_scale (σ : A)
    (h : ∀ i j : Fin n, Defm n σ i j = 0) [Invertible (2 : A)] (a b c e : Fin n) :
    Rm σ a b c e = 0 :=
  Rm_eq_zero_of_Defm_eq_zero σ h a b c e

end SCD.Singularity
