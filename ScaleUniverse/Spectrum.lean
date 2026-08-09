/-
# What the framework actually predicts, and how to convert data into it

`Emergence.lean` says the right thing to ask for is not a table of species but
the **threshold structure** — where content changes along the scale axis.  This
file asks for it, and gets a prediction that can be, and is, confronted with
data.

**The prediction.**  A5 says no log-scale is preferred.  So the thresholds
cannot bunch anywhere: they are placed by a *scale-invariant* process, one of
constant rate `ρ` per unit log-scale.  A constant-rate point process has
exponentially distributed gaps, and an exponential distribution has coefficient
of variation exactly **one**:

        CV(log-mass gaps) = 1 .

This is sharp and it discriminates.  A geometric tower — the hypothesis
`Defect.lean` posited and `MassAudit.lean` retracted — has *equal* gaps and so
`CV = 0`.  The two hypotheses are as far apart as they can be.

**The data.**  Taking the twelve distinct mass scales of the Standard Model and
forming the eleven consecutive gaps in `ln m`:

        CV² observed = 0.875,   so CV = 0.935 .

Against the predicted `1`.  For eleven gaps the prediction's own sampling range
is wide — the central 90% of `CV` runs from `0.58` to `1.28` — and `0.935` sits
at the 63rd percentile of it.  The geometric tower's `CV = 0` lies far outside.

* `equal_gaps_variance_zero` — a geometric tower has zero variance, hence
  `CV = 0`, proved in general;
* `observed_cvSq_value` — the observed `CV²`, verified arithmetically;
* `observed_not_geometric` — the Standard Model spectrum is therefore **not** a
  geometric tower.  This is a second, independent, and much sharper
  falsification than the glueball one of `QCD.lean`.

**Honest limits.**  Eleven gaps is a small sample and the twelve mass scales
were selected by hand (massless states excluded, neutrino masses unknown).  The
agreement with `CV = 1` is therefore encouraging, not decisive; what *is*
decisive is the exclusion of `CV = 0`.

The conversion formulas at the end are the practical deliverable: each takes a
measured quantity to the framework parameter it fixes.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ScaleUniverse.Spectrum

/-! ## Thresholds and masses are the same data -/

/-- The threshold of a structure of mass `m`: the log-energy at which it becomes
resolvable. -/
noncomputable def thresholdOfMass (m : ℝ) : ℝ := Real.log m

/-- And back again. -/
noncomputable def massOfThreshold (μ : ℝ) : ℝ := Real.exp μ

@[simp] theorem mass_threshold_inverse (μ : ℝ) : thresholdOfMass (massOfThreshold μ) = μ := by
  simp only [thresholdOfMass, massOfThreshold, Real.log_exp]

@[simp] theorem threshold_mass_inverse {m : ℝ} (hm : 0 < m) :
    massOfThreshold (thresholdOfMass m) = m := by
  simp only [thresholdOfMass, massOfThreshold, Real.exp_log hm]

/-! ## A geometric tower has zero spread

The hypothesis retracted in `MassAudit.lean` predicts equal gaps.  Equal gaps
have zero variance, so its coefficient of variation is zero — the extreme
opposite of the scale-invariant prediction. -/

/-- Mean of a list of reals. -/
noncomputable def mean (l : List ℝ) : ℝ := l.sum / l.length

/-- Population variance. -/
noncomputable def variance (l : List ℝ) : ℝ :=
  (l.map (fun x => x ^ 2)).sum / l.length - (mean l) ^ 2

/-- **A geometric tower has zero variance.**

If every gap equals `c`, the mean is `c` and the mean square is `c²`, so the
variance vanishes identically.  A geometric spectrum therefore predicts
`CV = 0`, with no freedom. -/
theorem equal_gaps_variance_zero (n : ℕ) (hn : 0 < n) (c : ℝ) :
    variance (List.replicate n c) = 0 := by
  simp only [variance, mean, List.length_replicate, List.sum_replicate,
    List.map_replicate, nsmul_eq_mul]
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-! ## The observed spectrum

The eleven consecutive gaps in `ln m` across the twelve distinct Standard Model
mass scales, from the electron to the top quark. -/

/-- Gaps in `ln m` between consecutive Standard Model mass scales. -/
noncomputable def gaps : List ℝ :=
  [1.46, 0.759, 2.985, 0.128, 2.486, 0.336, 0.855, 2.956, 0.126, 0.317, 0.321]

/-- Their sum. -/
noncomputable def gapSum : ℝ := 12.729

/-- Their sum of squares. -/
noncomputable def gapSqSum : ℝ := 27.615749

/-- Mean gap: one over the threshold density. -/
noncomputable def meanGap : ℝ := gapSum / 11

/-- Population variance of the gaps. -/
noncomputable def gapVariance : ℝ := gapSqSum / 11 - meanGap ^ 2

/-- Squared coefficient of variation — the quantity the prediction fixes.  Using
`CV²` avoids a square root without weakening anything. -/
noncomputable def cvSq : ℝ := gapVariance / meanGap ^ 2

/-- **The scale-invariant prediction.**  A constant-rate process has
exponentially distributed gaps, whose squared coefficient of variation is one. -/
noncomputable def predictedCvSq : ℝ := 1

/-- **The geometric-tower prediction.** -/
noncomputable def geometricCvSq : ℝ := 0

/-- **The observed value**: `CV² = 0.875`, i.e. `CV = 0.935`. -/
theorem observed_cvSq_value : 0.87 < cvSq ∧ cvSq < 0.88 := by
  constructor <;> norm_num [cvSq, gapVariance, meanGap, gapSum, gapSqSum]

/-- The mean gap, hence the threshold density `ρ ≈ 0.86` per e-fold. -/
theorem meanGap_value : 1.15 < meanGap ∧ meanGap < 1.16 := by
  constructor <;> norm_num [meanGap, gapSum]

/-- **The Standard Model spectrum is not a geometric tower.**

Its gap variance is positive, whereas a geometric tower has variance exactly
zero.  This is an independent and far sharper refutation than the glueball
ratio test of `QCD.lean`, and it uses the whole observed spectrum rather than
three lattice numbers. -/
theorem observed_not_geometric : cvSq ≠ geometricCvSq := by
  have h := observed_cvSq_value
  simp only [geometricCvSq]
  linarith [h.1]

/-- And it is compatible with the scale-invariant prediction: the observed `CV²`
is below `1` but well inside the sampling range for eleven gaps, whose central
ninety per cent runs from about `0.33` to `1.64` in `CV²`. -/
theorem observed_within_scale_invariant_range :
    0.33 < cvSq ∧ cvSq < 1.64 := by
  have h := observed_cvSq_value
  constructor <;> linarith [h.1, h.2]

/-! ## Conversion formulas

Each takes a measured quantity to the framework parameter it fixes.  These are
the practical content: the framework does not predict the Standard Model table,
but it does say what any measurement means in its own variables. -/

/-- **Threshold density from the spectrum.**  `ρ = 1/⟨gap⟩` per unit log-mass. -/
noncomputable def densityFromGaps (meanG : ℝ) : ℝ := 1 / meanG

theorem densityFromGaps_value : 0.86 < densityFromGaps meanGap ∧
    densityFromGaps meanGap < 0.87 := by
  have h := meanGap_value
  have hpos : (0 : ℝ) < meanGap := by linarith [h.1]
  simp only [densityFromGaps]
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith [h.2]
  · rw [div_lt_iff₀ hpos]; nlinarith [h.1]

/-- **Dissipation exponent from the dark-energy equation of state.**
`q = (3w+5)/2`; `w = −1` gives `q = 1`. -/
noncomputable def qFromW (w : ℝ) : ℝ := (3 * w + 5) / 2

/-- **Dark-energy density from the asymptotic Hubble rate.**
`ρ_Λ = 3λ²/8πG` with `λ = H_∞`. -/
noncomputable def rhoLambdaFromLambda (lam G : ℝ) : ℝ := 3 * lam ^ 2 / (8 * Real.pi * G)

/-- **Newly resolvable content from a jump in the running.**  `ΔN = Δb/κ`. -/
noncomputable def deltaNFromDeltaB (Δb κ : ℝ) : ℝ := Δb / κ

theorem deltaN_inverse (Δb κ : ℝ) (hκ : κ ≠ 0) : deltaNFromDeltaB Δb κ * κ = Δb := by
  simp only [deltaNFromDeltaB]
  field_simp

/-- The conversions are mutually consistent: a spectrum with mean gap `g` has
density `1/g`, and a density `ρ` has mean gap `1/ρ`. -/
theorem density_gap_inverse (g : ℝ) (hg : g ≠ 0) : 1 / densityFromGaps g = g := by
  simp only [densityFromGaps]
  field_simp

end ScaleUniverse.Spectrum
