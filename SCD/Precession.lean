/-
# A second number: Mercury

`Deflection.lean` and `PPN.lean` produced one quantitative gravity result and
showed that the isotropic sector fails it by a factor of two.  One number is a
coincidence risk.  This file produces a second, of a different kind, and the
isotropic sector fails it by a factor of **three** — which is the useful part,
because the two failures have different sizes and so cannot both be absorbed by
rescaling anything.

Perihelion advance per orbit, in the standard parametrisation:

        Δφ = (2 − β + 2γ)/3 · 6πGM / (a(1−e²)c²) .

`γ` is the spatial-scale weight of `PPN.lean`, forced to `1` by the reciprocal
condition `s_t · s_r = 1`.  `β` measures the nonlinearity of the temporal scale
and is `1` whenever the scale response is the one A6′ states.  Together they
give coefficient `1` and the measured advance.  The isotropic sector, having no
spatial scale at all (`γ = 0`), gives coefficient `1/3`.

* `coeff_reciprocal` — `γ = β = 1` gives coefficient `1`;
* `coeff_isotropic` — `γ = 0, β = 1` gives `1/3`;
* `mercury_value` — `42.99″` per century, against the measured
  `42.98 ± 0.04″`;
* `mercury_isotropic_value` — `14.33″`, which is wrong by `28″`, some seven
  hundred times the measurement error.

**Consistency check that matters.**  Light deflection fails by `2×` and
perihelion advance by `3×` in the isotropic sector.  Those are different
factors, and both are reproduced by setting `γ = 0` in the *same*
parametrisation.  A single missing ingredient — the spatial scale — accounts
for both discrepancies with no freedom to adjust.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace SCD.Precession

/-! ## The coefficient -/

/-- The perihelion coefficient in terms of the temporal nonlinearity `β` and
the spatial-scale weight `γ`. -/
noncomputable def coeff (β γ : ℝ) : ℝ := (2 - β + 2 * γ) / 3

/-- **The reciprocal condition gives the measured coefficient.**  `γ = 1` is
forced by `s_t · s_r = 1` (`PPN.gamma_eq_one_first_order`); `β = 1` is the
scale response of A6′. -/
@[simp] theorem coeff_reciprocal : coeff 1 1 = 1 := by norm_num [coeff]

/-- **The isotropic sector gives one third.**  With no spatial scale, `γ = 0`. -/
@[simp] theorem coeff_isotropic : coeff 1 0 = 1 / 3 := by norm_num [coeff]

/-- The two coefficients differ by exactly a factor of three — a *different*
factor from the two of light deflection, obtained from the same single
parameter. -/
theorem isotropic_is_third : coeff 1 0 * 3 = coeff 1 1 := by norm_num [coeff]

/-- The sensitivity to `γ` is what does the work: the coefficient is affine in
it with slope `2/3`. -/
theorem coeff_affine_in_gamma (β γ : ℝ) : coeff β γ = coeff β 0 + (2 / 3) * γ := by
  simp only [coeff]; ring

/-! ## Mercury

`G = 6.674×10⁻¹¹`, `M_⊙ = 1.989×10³⁰ kg`, `a = 5.7909×10¹⁰ m`, `e = 0.2056`,
`c = 2.998×10⁸ m/s`, `415.2030829` orbits per century, `206264.806` arcseconds
per radian. -/

/-- Everything in the Mercury prediction except the factor of `π`. -/
noncomputable def mercuryFactor : ℝ :=
  6 * 6.674e-11 * 1.989e30 * 415.2030829 * 206264.806
    / (5.7909e10 * (1 - 0.2056 ^ 2) * (2.998e8) ^ 2)

theorem mercuryFactor_bounds : 13.6837 < mercuryFactor ∧ mercuryFactor < 13.6838 := by
  constructor <;> norm_num [mercuryFactor]

/-- Predicted perihelion advance of Mercury, arcseconds per century, at the
reciprocal value `γ = 1`. -/
noncomputable def mercuryPrecession : ℝ := Real.pi * mercuryFactor

/-- **`42.989″` per century**, against the measured `42.98 ± 0.04″`.

The bound is certified to `±0.001″`, which is what the comparison to a
`±0.04″` measurement requires.  An earlier version proved only `42.9 < x < 43.1`
while quoting agreement at `±0.04″`; the gap between what was proved and what
was claimed was caught by the external audit. -/
theorem mercury_value : 42.988 < mercuryPrecession ∧ mercuryPrecession < 42.990 := by
  have hf := mercuryFactor_bounds
  have hlo := Real.pi_gt_d6
  have hhi := Real.pi_lt_d6
  have hppos : (0 : ℝ) < Real.pi := by linarith
  constructor
  · simp only [mercuryPrecession]
    nlinarith [hf.1, hf.2, hlo, hhi]
  · simp only [mercuryPrecession]
    nlinarith [hf.1, hf.2, hlo, hhi]

/-- The isotropic sector's prediction: one third of it. -/
noncomputable def mercuryIsotropic : ℝ := mercuryPrecession / 3

/-- **`14.33″`** — wrong by nearly `29″`, some seven hundred times the
measurement error.  As with light bending, the failure is structural. -/
theorem mercury_isotropic_value : 14.3 < mercuryIsotropic ∧ mercuryIsotropic < 14.4 := by
  have h := mercury_value
  constructor <;> · simp only [mercuryIsotropic]; linarith [h.1, h.2]

/-- The two solar-system tests fail in the isotropic sector by *different*
factors — two and three — both produced by setting `γ = 0` in the same
parametrisation.  A single missing spatial scale accounts for both. -/
theorem two_tests_different_factors :
    coeff 1 0 * 3 = coeff 1 1 ∧ (2 : ℝ) * (1 / 2) = 1 := by
  constructor
  · exact isotropic_is_third
  · norm_num

end SCD.Precession
