/-
# Particle scales: thresholds and the momentum dependence of lifetime

Two consequences of taking A3 (`ε · s = 1`) seriously for excitations.

**Thresholds.**  An excitation of log-scale `μ` is a configuration whose own
energy scale is `e^{-μ}`.  It can be produced only where that much energy is
available, so it simply does not exist as a degree of freedom below its
threshold.  This is what `RG.active` formalises: the particle content is a
function of scale, and the "different particles at different energies" of
effective field theory is the theory reporting its own structure.

**Lifetime.**  A decaying excitation carries its own clock, whose unit is set
by its rest energy `m`.  The laboratory uses a different unit, set by the total
energy `E = √(p² + m²)`.  A lifetime is a pure number of internal ticks; what
the laboratory reports is that number re-expressed in *its* unit, so it is
multiplied by the ratio of the two scales, `γ = E/m`.

Time dilation is therefore not a statement about clocks running slow.  It is
the scale ratio of A3, read twice.  We prove that the reported lifetime is at
least the proper one and grows with momentum.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity

namespace ScaleUniverse.Particles

open Real

/-! ## The scale ratio between an excitation and the laboratory -/

/-- The total energy of an excitation of rest scale `m` carrying momentum `p`.
Dimensionless throughout: all three are measured against the same fiducial. -/
noncomputable def energy (m p : ℝ) : ℝ := Real.sqrt (p ^ 2 + m ^ 2)

/-- The ratio between the laboratory's energy scale for the excitation and the
excitation's own.  This is the only content of the Lorentz factor here. -/
noncomputable def scaleRatio (m p : ℝ) : ℝ := energy m p / m

theorem energy_pos {m : ℝ} (hm : 0 < m) (p : ℝ) : 0 < energy m p := by
  simp only [energy]
  apply Real.sqrt_pos.mpr
  positivity

theorem energy_ge {m : ℝ} (hm : 0 < m) (p : ℝ) : m ≤ energy m p := by
  simp only [energy]
  calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm.le).symm
    _ ≤ Real.sqrt (p ^ 2 + m ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg p])

/-- The scale ratio is at least one: the laboratory never assigns an
excitation a *smaller* scale than its own rest scale. -/
theorem one_le_scaleRatio {m : ℝ} (hm : 0 < m) (p : ℝ) : 1 ≤ scaleRatio m p := by
  simp only [scaleRatio]
  rw [le_div_iff₀ hm, one_mul]
  exact energy_ge hm p

/-- The scale ratio grows with momentum. -/
theorem scaleRatio_mono {m : ℝ} (hm : 0 < m) {p q : ℝ} (h : p ^ 2 ≤ q ^ 2) :
    scaleRatio m p ≤ scaleRatio m q := by
  simp only [scaleRatio, energy]
  gcongr
  all_goals linarith

/-! ## Lifetime -/

/-- The lifetime a laboratory reports: the excitation's own number of internal
ticks `τ₀`, re-expressed in the laboratory's unit. -/
noncomputable def lifetime (τ₀ m p : ℝ) : ℝ := scaleRatio m p * τ₀

/-- **The reported lifetime is never shorter than the proper one.** -/
theorem lifetime_ge {m τ₀ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ₀) (p : ℝ) :
    τ₀ ≤ lifetime τ₀ m p := by
  simp only [lifetime]
  nlinarith [one_le_scaleRatio hm p]

/-- **Lifetime grows with momentum**, purely because the ratio of the
laboratory's scale to the excitation's own grows.  No dynamical assumption
about the decay is used. -/
theorem lifetime_mono {m τ₀ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ₀) {p q : ℝ}
    (h : p ^ 2 ≤ q ^ 2) : lifetime τ₀ m p ≤ lifetime τ₀ m q := by
  simp only [lifetime]
  exact mul_le_mul_of_nonneg_right (scaleRatio_mono hm h) hτ

/-- At rest the two scales coincide and the reported lifetime is the proper
one: the normalisation is fixed with nothing left over. -/
@[simp] theorem lifetime_at_rest {m τ₀ : ℝ} (hm : 0 < m) :
    lifetime τ₀ m 0 = τ₀ := by
  simp only [lifetime, scaleRatio, energy]
  rw [show (0 : ℝ) ^ 2 + m ^ 2 = m ^ 2 by ring, Real.sqrt_sq hm.le,
    div_self (ne_of_gt hm), one_mul]

/-! ## Thresholds

An excitation of log-scale `μ` is available only at log-energies `t ≥ μ`.  The
statement is trivial once written down — which is the point: in a theory whose
only variable is scale, the scale-dependence of the particle content is not an
extra hypothesis. -/

/-- An excitation is available exactly above its own log-threshold. -/
def Available (μ t : ℝ) : Prop := μ ≤ t

theorem available_mono {μ t t' : ℝ} (h : t ≤ t') (ha : Available μ t) : Available μ t' :=
  le_trans ha h

/-- Below its threshold an excitation is not a degree of freedom at all. -/
theorem not_available_of_lt {μ t : ℝ} (h : t < μ) : ¬ Available μ t :=
  not_le.mpr h

end ScaleUniverse.Particles
