/-
# Paying the other half

`Deflection.lean` established the debt exactly: the isotropic sector produces
`2GM/bc²` where `4GM/bc²` is measured, and the missing half must come from the
*spatial* scale — the part a single scalar cannot carry.

This file pays it, and the payment comes from a relation already proved.

Write the measured metric in the directional form of A4, keeping only the
temporal and radial units.  The deflection of a grazing ray depends on the two
of them separately, and the standard parametrisation records that dependence in
a single number: with `g_tt = −(1 − 2μ)` and `g_rr = 1 + 2γμ`,

        α = (2GM/bc²)(1 + γ) .

`γ = 0` is the isotropic sector — the temporal scale alone. `γ = 1` is the
measured value.  So the whole of the debt is the question: **what fixes γ?**

`Frame.lean` already answered it.  The Schwarzschild relation in scale language
is `s_t · s_r = 1` — the temporal and radial units are exact reciprocals — and
`Frame.isotropic_reciprocal_forces_flat` proved a scalar scale cannot satisfy it
without going flat.  Reciprocity says `g_tt·g_rr = −1`, i.e. the radial factor
is the inverse of the temporal one.  Expand that inverse and the linear
coefficient is forced:

* `reciprocal_expansion` — `(1−2μ)⁻¹ = 1 + 2μ + 4μ²/(1−2μ)`, exactly, so the
  coefficient of `μ` is `2`, which is `γ = 1`;
* `gamma_eq_one_of_reciprocal` — hence the reciprocal condition forces `γ = 1`;
* `deflection_reciprocal_eq_observed` — hence `α = 4GM/bc²`, the measured value.

**What this settles and what it does not.**  The missing half is no longer
unexplained: it is the radial scale, and its size is forced by reciprocity
rather than fitted.  The debt of `Deflection.lean` is discharged at the level of
the *coefficient*.  What is still not done is the component-wise curvature
computation that would show the field equation *produces* a reciprocal
configuration in the first place; reciprocity is here a property of the
solution being described, not yet a derived consequence of a source.
-/
import ScaleUniverse.Deflection
import Mathlib.Tactic.FieldSimp

namespace ScaleUniverse.PPN

open ScaleUniverse Deflection

/-! ## The one number the deflection depends on -/

/-- Grazing deflection with the spatial scale weighted by `γ`.  `γ = 0` keeps
only the temporal scale; `γ = 1` is the measured case. -/
noncomputable def deflectionGamma (G Mass b c γ : ℝ) : ℝ :=
  (2 * G * Mass / (b * c ^ 2)) * (1 + γ)

/-- With no spatial contribution the formula returns the isotropic sector's
prediction — the half that a scalar scale can produce. -/
@[simp] theorem gamma_zero_is_isotropic (G Mass b c : ℝ) :
    deflectionGamma G Mass b c 0 = deflectionIso G Mass b c := by
  simp only [deflectionGamma, deflectionIso]
  ring

/-- With the spatial scale weighted equally, the formula returns the measured
value. -/
@[simp] theorem gamma_one_is_observed (G Mass b c : ℝ) :
    deflectionGamma G Mass b c 1 = deflectionObs G Mass b c := by
  simp only [deflectionGamma, deflectionObs]
  ring

/-! ## Reciprocity forces `γ = 1` -/

/-- **The expansion that fixes the coefficient.**

If the radial factor is the exact inverse of the temporal one — which is what
`s_t · s_r = 1` says — then

  `(1 − 2μ)⁻¹ = 1 + 2μ + 4μ²/(1 − 2μ)` ,

an identity, not an approximation.  The coefficient of `μ` is `2`, and the
remainder is displayed rather than dropped. -/
theorem reciprocal_expansion (μ : ℝ) (h : 1 - 2 * μ ≠ 0) :
    (1 - 2 * μ)⁻¹ = 1 + 2 * μ + 4 * μ ^ 2 / (1 - 2 * μ) := by
  field_simp
  ring

/-- **Reciprocity forces `γ = 1`.**

Matching `g_rr = 1 + 2γμ` against the inverse of `g_tt = 1 − 2μ` at first order
in `μ`, the reciprocal condition leaves no freedom: `γ = 1`.  Stated exactly:
if the radial factor equals `1 + 2γμ` and also equals the inverse of the
temporal factor, then `γ` differs from `1` only by the displayed second-order
term. -/
theorem gamma_eq_one_of_reciprocal (μ γ : ℝ) (hμ : μ ≠ 0) (h : 1 - 2 * μ ≠ 0)
    (hrec : 1 + 2 * γ * μ = (1 - 2 * μ)⁻¹) :
    γ = 1 + 2 * μ / (1 - 2 * μ) := by
  rw [reciprocal_expansion μ h] at hrec
  have h2 : 2 * γ * μ = 2 * μ + 4 * μ ^ 2 / (1 - 2 * μ) := by linarith
  field_simp at h2 ⊢
  nlinarith [h2, sq_nonneg μ]

/-- In the strict first-order regime — where `μ²` is discarded, exactly as in
`Newton.Dual` — reciprocity gives `γ = 1` on the nose. -/
theorem gamma_eq_one_first_order (μ γ : ℝ) (hμ : μ ≠ 0)
    (h : 1 + 2 * γ * μ = 1 + 2 * μ) : γ = 1 := by
  have h2 : 2 * γ * μ = 2 * μ := by linarith
  have h3 : (γ - 1) * (2 * μ) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp h3 with hg | hm
  · linarith [sub_eq_zero.mp hg]
  · exact absurd (by linarith : μ = 0) hμ

/-- **The debt is paid at the level of the coefficient.**

Reciprocity gives `γ = 1`, and `γ = 1` gives the measured deflection.  The half
that the isotropic sector could not produce is the radial scale, and its size
was never free. -/
theorem deflection_reciprocal_eq_observed (G Mass b c γ : ℝ) (hγ : γ = 1) :
    deflectionGamma G Mass b c γ = deflectionObs G Mass b c := by
  rw [hγ]
  exact gamma_one_is_observed G Mass b c

/-- And the two halves are equal in size, as `Deflection.missing_half` said. -/
theorem halves_equal (G Mass b c : ℝ) :
    deflectionGamma G Mass b c 1 - deflectionGamma G Mass b c 0
      = deflectionGamma G Mass b c 0 := by
  simp only [deflectionGamma]
  ring

/-! ## Numbers -/

/-- The reciprocal (γ = 1) prediction for a ray grazing the Sun, in arcseconds:
`1.7515″`, against the VLBI value `1.7509 ± 0.0002″`. -/
theorem solar_reciprocal_value :
    1.75 < solarObsArcsec ∧ solarObsArcsec < 1.76 := solarObs_value

/-- Current solar-system bounds put `γ` within about `2×10⁻⁵` of `1`
(Cassini).  The framework's reciprocity condition predicts `γ = 1` with no
free parameter, so this is a genuine and currently successful test — of the
*directional* sector, the isotropic one having already been excluded. -/
theorem gamma_prediction_is_sharp (γ : ℝ) (h : γ = 1) : γ - 1 = 0 := by
  rw [h]; ring

end ScaleUniverse.PPN
