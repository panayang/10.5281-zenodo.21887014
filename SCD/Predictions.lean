/-
# Testable predictions

A framework that only reproduces known structures is not yet physics.  This
file extracts numbers.

Two kinds of statement appear.

**(a) A falsifiable formula.**  Generalise A6 from `ε̇ = −λε` to a power law
`ε̇ = −λε^q`.  The single dimensionless exponent `q` then fixes the dark-energy
equation of state exactly:

        w = (2q − 5)/3 ,        equivalently   q = (3w + 5)/2 .

`q = 1` gives `w = −1` — the exponential dissipation of `DarkEnergy.lean`, i.e.
exact de Sitter with no freedom at all.  This is the framework's sharpest
exposure: **if `w = −1` is excluded by observation, pure exponential
dissipation is dead**, and the surviving theory must have `q ≠ 1`, with `q`
read off the data by the inversion formula above.  The acceleration condition
is `q < 2`.

**(b) Arithmetic checks.**  Three formulas the framework reproduces, evaluated
against measured constants and verified by `norm_num` — muon time dilation,
the Pound–Rebka redshift, and the dark-energy density.  These are checks, not
new predictions: they confirm the framework lands on the right numbers where
the physics is already known.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SCD.Predictions

/-! ## (a) The equation of state from the dissipation exponent

For power-law dissipation `ε̇ = −λε^q` with scale factor `a = 1/ε`, the chain
rule gives `ε̈ = λ²q ε^{2q−1}`.  We carry `Eq := ε^q` as an explicit quantity so
that the argument is pure algebra and no real exponentiation is needed. -/

/-- The acceleration `ä` of `a = 1/ε` has the sign of `2ε̇² − εε̈`.  This is the
quotient rule, stated as the identity that will be specialised below. -/
theorem accel_numerator (ε ε' ε'' : ℝ) (hε : 0 < ε) :
    (2 * ε' ^ 2 - ε * ε'') / ε ^ 3 > 0 ↔ 2 * ε' ^ 2 - ε * ε'' > 0 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h3 : (0:ℝ) < ε ^ 3 := by positivity
    nlinarith [div_nonpos_of_nonpos_of_nonneg hc (le_of_lt h3)]
  · intro h
    have h3 : (0:ℝ) < ε ^ 3 := by positivity
    exact div_pos h h3

/-- **Power-law dissipation: the acceleration numerator.**

With `ε' = −λ·Eq` and `ε'' = λ²q·Eq²/ε` (the chain rule for `Eq = ε^q`),

    `2ε'² − εε'' = λ²Eq²(2 − q)` .

Hence expansion accelerates precisely when `q < 2`, for any dissipation rate. -/
theorem powerlaw_accel_numerator (lam q ε Eq ε' ε'' : ℝ) (hε : 0 < ε)
    (hd1 : ε' = -(lam * Eq))
    (hd2 : ε'' = lam ^ 2 * q * Eq ^ 2 / ε) :
    2 * ε' ^ 2 - ε * ε'' = lam ^ 2 * Eq ^ 2 * (2 - q) := by
  rw [hd1, hd2]
  field_simp

/-- **Acceleration ⟺ `q < 2`.** -/
theorem accelerates_iff (lam q Eq : ℝ) (hlam : lam ≠ 0) (hEq : Eq ≠ 0) :
    lam ^ 2 * Eq ^ 2 * (2 - q) > 0 ↔ q < 2 := by
  have hpos : 0 < lam ^ 2 * Eq ^ 2 := by positivity
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ### The equation of state

`H = λa^{1−q}` gives `ρ ∝ H² ∝ a^{2(1−q)}`, while the continuity equation gives
`ρ ∝ a^{−3(1+w)}`.  Matching exponents fixes `w`. -/

/-- The dark-energy equation of state predicted by dissipation exponent `q`. -/
noncomputable def eos (q : ℝ) : ℝ := (2 * q - 5) / 3

/-- The inversion: an observed `w` determines the dissipation exponent. This is
how a measurement is converted into the theory's single free parameter. -/
noncomputable def dissipationExponent (w : ℝ) : ℝ := (3 * w + 5) / 2

@[simp] theorem eos_dissipationExponent (w : ℝ) : eos (dissipationExponent w) = w := by
  simp only [eos, dissipationExponent]; ring

@[simp] theorem dissipationExponent_eos (q : ℝ) : dissipationExponent (eos q) = q := by
  simp only [eos, dissipationExponent]; ring

/-- **Exponential dissipation predicts a cosmological constant exactly.**
`q = 1 ⟹ w = −1`, with no adjustable parameter. -/
@[simp] theorem eos_one : eos 1 = -1 := by norm_num [eos]

/-- `w = −1` happens *only* at `q = 1`: the prediction is sharp, not generic. -/
theorem eos_eq_neg_one_iff (q : ℝ) : eos q = -1 ↔ q = 1 := by
  simp only [eos]
  constructor
  · intro h; linarith [(div_eq_iff (by norm_num : (3:ℝ) ≠ 0)).mp h]
  · intro h; rw [h]; norm_num

/-- Acceleration in terms of the observable: `w < −1/3 ⟺ q < 2`.  The two
criteria agree, as they must. -/
theorem eos_lt_third_iff (q : ℝ) : eos q < -(1/3) ↔ q < 2 := by
  simp only [eos]
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 3)]
  constructor <;> intro h <;> linarith

/-- The phantom boundary: `w < −1 ⟺ q < 1`. -/
theorem eos_lt_neg_one_iff (q : ℝ) : eos q < -1 ↔ q < 1 := by
  simp only [eos]
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 3)]
  constructor <;> intro h <;> linarith

/-- Worked inversion: an observed `w = −0.95` corresponds to `q = 1.075`,
a mild departure from pure exponential dissipation. -/
theorem worked_inversion : dissipationExponent (-0.95) = 1.075 := by
  norm_num [dissipationExponent]

/-! ## (b) Arithmetic checks against measurement

Constants are exact SI definitions or CODATA values, entered as rationals. -/

/-! ### Muon time dilation

`Particles.lifetime` gives `τ = γτ₀`.  CERN muon storage ring (1977):
`γ = 29.327`, proper lifetime `τ₀ = 2.19703 μs`. -/

/-- Predicted dilated muon lifetime, in microseconds. -/
noncomputable def muonLifetime : ℝ := 29.327 * 2.19703

/-- The framework predicts `64.43 μs`; the measured value is
`64.378 ± 0.026 μs` — agreement at the `10⁻³` level. -/
theorem muon_lifetime_value : |muonLifetime - 64.4323| < 0.001 := by
  rw [abs_lt]
  constructor <;> norm_num [muonLifetime]

theorem muon_matches_experiment : |muonLifetime - 64.378| < 0.06 := by
  rw [abs_lt]
  constructor <;> norm_num [muonLifetime]

/-! ### Gravitational redshift (Pound–Rebka)

A3 gives `ε = e^Φ`, so to first order the fractional frequency shift over a
height `h` is `z = gh/c²`.  Harvard tower: `h = 22.5 m`. -/

/-- Fractional redshift over the Pound–Rebka tower, in units of `10⁻¹⁵`. -/
noncomputable def poundRebka : ℝ := (9.80665 * 22.5 / (299792458 ^ 2)) * 10 ^ 15

/-- The framework gives `z = 2.455 × 10⁻¹⁵`; the 1965 Pound–Snider measurement
is `(2.46 ± 0.03) × 10⁻¹⁵`. -/
theorem poundRebka_value : 2.45 < poundRebka ∧ poundRebka < 2.46 := by
  constructor <;> norm_num [poundRebka]

/-! ### Dark-energy density

`DarkEnergy.lean` gives exact de Sitter with `H = λ`.  Identifying `λ` with the
asymptotic Hubble rate `H_∞ = H₀√Ω_Λ ≈ 1.8077 × 10⁻¹⁸ s⁻¹` and using
`ρ_Λ = 3λ²/(8πG)` with `G = 6.674 × 10⁻¹¹`: -/

/-- Predicted dark-energy density, in units of `10⁻²⁷ kg/m³`. -/
noncomputable def darkEnergyDensity : ℝ :=
  (3 * (1.8077) ^ 2 / (8 * 3.14159265 * 6.674)) * 10 ^ 2

/-- The framework gives `≈ 5.84 × 10⁻²⁷ kg/m³`; Planck 2018 gives
`≈ 5.86 × 10⁻²⁷ kg/m³`. -/
theorem darkEnergyDensity_value : 5.8 < darkEnergyDensity ∧ darkEnergyDensity < 5.9 := by
  constructor <;> norm_num [darkEnergyDensity]

/-! ## Discrete scale invariance and a geometric mass tower

If the continuous scale symmetry A5 is broken not completely but to a discrete
subgroup — invariance under `σ ↦ σ + Δ` only for integer multiples of `Δ` —
then the set of admissible scales is closed under adding `Δ`.  Masses, being
`e^{-σ}` by A3, then form a *geometric* rather than arithmetic tower.

This is a structural prediction and a genuinely different route from the
Standard Model, which fixes masses by Yukawa couplings with no relation among
them.  It does **not** reproduce the observed spectrum; what it says is that a
scale-based theory predicts constant *ratios*, which is a falsifiable shape. -/

/-- Log-scales admissible under discrete scale invariance with step `Δ`. -/
noncomputable def logScale (μ₀ Δ : ℝ) (k : ℕ) : ℝ := μ₀ + k * Δ

/-- **The tower is geometric.**  Successive levels differ by a constant *ratio*
`e^Δ`, never by a constant amount. -/
theorem logScale_step (μ₀ Δ : ℝ) (k : ℕ) :
    logScale μ₀ Δ (k + 1) - logScale μ₀ Δ k = Δ := by
  simp only [logScale]; push_cast; ring

/-- The ratio of consecutive masses is the same at every level — the content
that could be tested against a spectrum. -/
theorem logScale_ratio_const (μ₀ Δ : ℝ) (k l : ℕ) :
    (logScale μ₀ Δ (k + 1) - logScale μ₀ Δ k)
      = (logScale μ₀ Δ (l + 1) - logScale μ₀ Δ l) := by
  rw [logScale_step, logScale_step]

/-- Closure under the discrete symmetry: the tower, once started, is infinite
upward.  A scale-based theory therefore predicts a *tower*, not a finite list —
which is the sharpest qualitative difference from the Standard Model. -/
theorem logScale_closed (μ₀ Δ : ℝ) (k : ℕ) :
    logScale μ₀ Δ k + Δ = logScale μ₀ Δ (k + 1) := by
  simp only [logScale]; push_cast; ring

end SCD.Predictions
