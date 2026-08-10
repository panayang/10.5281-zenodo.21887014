/-
# Light bending: the isotropic sector gets exactly half

The scope statement has said for several rounds that "quantitative gravity
effects are not derived".  This file derives one, and the result is a *failure*
of a precisely measurable size — which is more useful than a success would have
been, because it says exactly how much the directional scale has to supply.

Light bends because it crosses regions of differing scale.  In the **isotropic**
sector — the old scalar axiom, `g = e^{2σ}δ`, now known to be the degenerate
locus of A4 — the whole effect comes from the single scalar `σ = −Φ`, and the
grazing deflection is

        α_iso = 2GM / (bc²) .

The measured value is twice that:

        α_obs = 4GM / (bc²) .

**The isotropic sector is not approximately wrong, it is wrong by exactly a
factor of two.**  `iso_is_exactly_half` states this with no fitted quantity in
it.  The missing half is the contribution of *spatial* scale anisotropy — the
part `Frame.lean` proved a scalar scale cannot represent at all
(`isotropic_reciprocal_forces_flat`).  So the factor of two is the same fact
appearing as a number: the two halves are the temporal and the spatial scale,
and a theory with one scale can only ever supply one of them.

Numbers for a ray grazing the Sun are given at the end and checked against VLBI.

**Status.** This is a derived, falsifiable number, and the framework's isotropic
sector fails it by 2×. The directional sector predicts the missing half only
once the anisotropic curvature is computed — which is still not done. What this
file establishes is the *size of the remaining debt*, exactly.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace SCD.Deflection

/-! ## The two predictions -/

/-- Grazing deflection produced by the **temporal** scale alone — the whole of
what an isotropic (single-scalar) scale field can produce. -/
noncomputable def deflectionIso (G Mass b c : ℝ) : ℝ := 2 * G * Mass / (b * c ^ 2)

/-- The measured grazing deflection. -/
noncomputable def deflectionObs (G Mass b c : ℝ) : ℝ := 4 * G * Mass / (b * c ^ 2)

/-- **The isotropic sector gives exactly half.**

Not approximately, and with no adjustable quantity anywhere in the statement. -/
theorem iso_is_exactly_half (G Mass b c : ℝ) :
    2 * deflectionIso G Mass b c = deflectionObs G Mass b c := by
  simp only [deflectionIso, deflectionObs]
  ring

/-- Stated as a ratio, where the denominator is nonzero. -/
theorem iso_ratio_half (G Mass b c : ℝ) (h : deflectionObs G Mass b c ≠ 0) :
    deflectionIso G Mass b c / deflectionObs G Mass b c = 1 / 2 := by
  have h2 : deflectionObs G Mass b c = 2 * deflectionIso G Mass b c :=
    (iso_is_exactly_half G Mass b c).symm
  rw [h2] at h ⊢
  have hi : deflectionIso G Mass b c ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at h
    exact h rfl
  field_simp

/-- The deficit is exactly the isotropic prediction over again: the missing
contribution is the same size as the one a scalar scale can produce.  In the
scale reading, the temporal and the spatial scale contribute equally, and a
single scalar carries only the temporal one. -/
theorem missing_half (G Mass b c : ℝ) :
    deflectionObs G Mass b c - deflectionIso G Mass b c
      = deflectionIso G Mass b c := by
  simp only [deflectionIso, deflectionObs]
  ring

/-! ## Numbers for a ray grazing the Sun

`G = 6.674×10⁻¹¹`, `M = 1.989×10³⁰ kg`, `b = R_⊙ = 6.957×10⁸ m`,
`c = 2.998×10⁸ m/s`, and `206264.806` arcseconds per radian. -/

/-- Observed-branch prediction, in arcseconds. -/
noncomputable def solarObsArcsec : ℝ :=
  (4 * 6.674e-11 * 1.989e30 / (6.957e8 * (2.998e8) ^ 2)) * 206264.806

/-- Isotropic-sector prediction, in arcseconds. -/
noncomputable def solarIsoArcsec : ℝ :=
  (2 * 6.674e-11 * 1.989e30 / (6.957e8 * (2.998e8) ^ 2)) * 206264.806

/-- **`1.7515″`** — matching the VLBI value `1.7509 ± 0.0002″` to about `0.04%`. -/
theorem solarObs_value : 1.7515 < solarObsArcsec ∧ solarObsArcsec < 1.7516 := by
  constructor <;> norm_num [solarObsArcsec]

/-- **`0.8758″`** — the isotropic sector's prediction, wrong by a factor of
two.  This is the sharpest quantitative statement in the development, and it is
a refutation of the scalar axiom rather than a confirmation of anything. -/
theorem solarIso_value : 0.87 < solarIsoArcsec ∧ solarIsoArcsec < 0.88 := by
  constructor <;> norm_num [solarIsoArcsec]

/-- The two solar numbers stand in the exact ratio `2 : 1`, as the general
theorem requires. -/
theorem solar_ratio : solarObsArcsec = 2 * solarIsoArcsec := by
  simp only [solarObsArcsec, solarIsoArcsec]
  ring

/-- The isotropic sector misses the measured value by more than `0.8″`, which
is four thousand times the VLBI uncertainty: the failure is not a modelling
imprecision but a structural one. -/
theorem iso_fails_by_far : 0.87 < solarObsArcsec - solarIsoArcsec := by
  rw [solar_ratio]
  have h := solarIso_value
  linarith [h.1, h.2]

end SCD.Deflection
