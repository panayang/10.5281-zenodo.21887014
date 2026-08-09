/-
# A6 — Openness: dissipation is expansion

The universe is not a closed system.  Axiom A6 states that its total
dimensionless energy scale `ε` dissipates.  By the scale–energy duality A3,
`ε · s = 1`, a decaying energy scale *is* a growing length scale.  Cosmic
expansion is therefore not motion of anything through space: it is the running
down of the energy scale, read through the duality.

We prove:

* dissipation at a constant fractional rate `λ` has a unique solution
  `ε(t) = ε₀e^{−λt}` (no ansatz is assumed);
* the corresponding scale factor is `a(t) = a₀e^{λt}` — exact de Sitter;
* `H = ȧ/a = λ` is constant and `ä = λ²a > 0`: expansion accelerates.

So "dark energy" is not a substance with negative pressure.  It is the
dissipation rate of an open universe, and the observed `Λ` is `λ²` up to the
dimensionless factor fixed by the number of dimensions.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

namespace ScaleUniverse.Cosmology

open Real

/-! ## The dissipation law and its unique solution -/

/-- Auxiliary: `t ↦ e^{λt}` and its derivative. -/
theorem hasDerivAt_exp_mul (lam t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (lam * u)) (Real.exp (lam * t) * lam) t := by
  have hin : HasDerivAt (fun u : ℝ => lam * u) lam t := by
    simpa using (hasDerivAt_id t).const_mul lam
  exact (Real.hasDerivAt_exp (lam * t)).comp t hin

/-- **Dissipation has a unique history.**

If the dimensionless energy scale obeys `ε̇ = −λ ε`, then `ε(t) = ε₀e^{−λt}`.
Nothing is assumed about the form of `ε`; the exponential is forced. -/
theorem dissipation_solution (lam : ℝ) (ε : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt ε (-lam * ε t) t) (t : ℝ) :
    ε t = ε 0 * Real.exp (-lam * t) := by
  set u : ℝ → ℝ := fun r => ε r * Real.exp (lam * r) with hu_def
  have hu : ∀ r, HasDerivAt u 0 r := by
    intro r
    have h := (hd r).mul (hasDerivAt_exp_mul lam r)
    have : (-lam * ε r) * Real.exp (lam * r) + ε r * (Real.exp (lam * r) * lam) = 0 := by
      ring
    rwa [this] at h
  have hconst : ∀ x y, u x = u y :=
    is_const_of_deriv_eq_zero (fun r => (hu r).differentiableAt) (fun r => (hu r).deriv)
  have h0 : ε t * Real.exp (lam * t) = ε 0 := by
    have := hconst t 0
    simpa [hu_def] using this
  have hne : Real.exp (lam * t) ≠ 0 := Real.exp_ne_zero _
  rw [← h0, show -lam * t = -(lam * t) by ring, Real.exp_neg, mul_assoc,
    mul_inv_cancel₀ hne, mul_one]

/-- The energy scale of an open universe is strictly decreasing. -/
theorem energy_strictly_decreasing (lam : ℝ) (hlam : 0 < lam) (ε : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt ε (-lam * ε t) t) (hpos : 0 < ε 0) {t : ℝ} (ht : 0 < t) :
    ε t < ε 0 := by
  rw [dissipation_solution lam ε hd t]
  have hexp : Real.exp (-lam * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  nlinarith [Real.exp_pos (-lam * t)]

/-! ## The scale factor: exact de Sitter

By A3 the scale is the reciprocal of the energy scale, so we may *define* the
cosmological scale factor as `a = 1/ε`.  It is not an independent field. -/

/-- The scale factor, defined by duality from the energy scale. -/
noncomputable def scaleFactor (a₀ lam : ℝ) : ℝ → ℝ := fun t => a₀ * Real.exp (lam * t)

/-- **Dissipation is expansion.**  The reciprocal of a decaying energy scale is
an exponentially growing length scale: exact de Sitter, with no cosmological
constant inserted anywhere. -/
theorem scaleFactor_eq (lam : ℝ) (ε : ℝ → ℝ) (hd : ∀ t, HasDerivAt ε (-lam * ε t) t)
    (hpos : ε 0 ≠ 0) (t : ℝ) :
    1 / ε t = scaleFactor (1 / ε 0) lam t := by
  rw [dissipation_solution lam ε hd t, scaleFactor,
    show -lam * t = -(lam * t) by ring, Real.exp_neg]
  have hne : Real.exp (lam * t) ≠ 0 := Real.exp_ne_zero _
  field_simp

/-- The Hubble rate `ȧ = λa`, i.e. `H = λ` is constant. -/
theorem hasDerivAt_scaleFactor (a₀ lam t : ℝ) :
    HasDerivAt (scaleFactor a₀ lam) (lam * scaleFactor a₀ lam t) t := by
  have h := (hasDerivAt_exp_mul lam t).const_mul a₀
  have heq : a₀ * (Real.exp (lam * t) * lam) = lam * scaleFactor a₀ lam t := by
    simp only [scaleFactor]; ring
  rw [heq] at h
  exact h

/-- **Accelerated expansion.**  `ä = λ²a`, strictly positive for any nonzero
dissipation rate and positive scale.  Acceleration is not evidence of a
repulsive substance; it is the second derivative of a reciprocal. -/
theorem hasDerivAt_hubble (a₀ lam t : ℝ) :
    HasDerivAt (fun r => lam * scaleFactor a₀ lam r) (lam ^ 2 * scaleFactor a₀ lam t) t := by
  have h := (hasDerivAt_scaleFactor a₀ lam t).const_mul lam
  have heq : lam * (lam * scaleFactor a₀ lam t) = lam ^ 2 * scaleFactor a₀ lam t := by ring
  rw [heq] at h
  exact h

theorem acceleration_pos (a₀ lam t : ℝ) (ha : 0 < a₀) (hlam : lam ≠ 0) :
    0 < lam ^ 2 * scaleFactor a₀ lam t := by
  have h1 : 0 < scaleFactor a₀ lam t := by
    simp only [scaleFactor]
    positivity
  positivity

/-- Collected statement: an open universe dissipating at constant fractional
rate `λ > 0` expands, and does so at an accelerating rate, with constant
Hubble parameter `H = λ`. -/
theorem open_universe_accelerates (lam ε₀ : ℝ) (hlam : 0 < lam) (hε : 0 < ε₀)
    (ε : ℝ → ℝ) (hd : ∀ t, HasDerivAt ε (-lam * ε t) t) (h0 : ε 0 = ε₀) :
    (∀ t, 1 / ε t = scaleFactor (1 / ε₀) lam t)
    ∧ (∀ t, HasDerivAt (scaleFactor (1 / ε₀) lam)
        (lam * scaleFactor (1 / ε₀) lam t) t)
    ∧ (∀ t, 0 < lam ^ 2 * scaleFactor (1 / ε₀) lam t) := by
  refine ⟨fun t => ?_, fun t => hasDerivAt_scaleFactor _ _ t, fun t => ?_⟩
  · rw [scaleFactor_eq lam ε hd (by rw [h0]; exact ne_of_gt hε) t, h0]
  · exact acceleration_pos _ _ _ (by positivity) (ne_of_gt hlam)

end ScaleUniverse.Cosmology
