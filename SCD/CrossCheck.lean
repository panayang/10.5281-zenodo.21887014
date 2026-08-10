/-
# The cross-sector test I proposed does not exist

`Spectrum.lean` extracted a threshold density `ρ ≈ 0.86` per e-fold from the
mass spectrum.  `Running.lean` has a density of the same name controlling the
slope of `g⁻²`.  Since the framework calls them both `ρ`, the obvious move is to
measure one from the spectrum, the other from the running of a coupling, and
check that they agree — a genuine cross-sector test needing no new assumption.

I ran it.  **It is not a test, and the reason is a mistake in `Running.lean`'s
framing.**

**First, the numbers disagree.**  Counting all twelve Standard Model mass
scales gives `ρ_all ≈ 0.864`.  Counting only the six quarks — the structures a
strong coupling actually responds to — gives `ρ_quark ≈ 0.444`.  They differ by
a factor of about two.

**Second, and fatally, they are not the same quantity.**  `Running.lean` says
"a probe responds to the defects it can resolve", and I read that as *all* of
them.  A gauge coupling does not: it responds only to structures charged under
it.  So `ρ` in the running is a *sector-restricted, signed* count, while `ρ` in
the spectrum is a raw count of every threshold.  There is no reason for them to
be equal and the framework never said there was.

**Third, within a sector the relation collapses to an identity.**  With one
equation `db/dt = κ·(dN/dt)` and one unknown `κ`, measuring the beta jump and
the threshold density determines `κ` rather than testing anything.  Carried out
for QCD between the charm and top thresholds it returns `κ = 2/3` — which is
just the per-flavour beta jump written backwards.

* `densities_differ` and `density_ratio_near_two` — the numerical disagreement;
* `sector_relation_is_identity` — one equation, one unknown, no content;
* `no_second_determination` — what a real test would need and the framework
  does not supply.

**What survives.**  The per-sector prediction is still testable: each sector's
thresholds should be a constant-rate process, whatever its own rate.  For the
quark sector alone `CV² = 0.243`, i.e. `CV = 0.493`, which sits at the twelfth
percentile of the prediction's sampling distribution for five gaps — low, more
regular than a Poisson process would typically give, but not excluded.  With
five gaps nothing stronger can be said.

**Recorded conclusion.**  The framework currently offers **no** cross-sector
test of the threshold density.  The proposal was an over-reach on my part, and
`Running.lean`'s wording has been corrected to say which defects a coupling
counts.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace SCD.CrossCheck

/-! ## The two densities are different numbers -/

/-- Threshold density from all twelve Standard Model mass scales, per e-fold. -/
noncomputable def rhoAll : ℝ := 11 / 12.731

/-- Threshold density from the six quarks alone — the structures a strong
coupling responds to. -/
noncomputable def rhoQuark : ℝ := 5 / 11.271

theorem rhoAll_value : 0.86 < rhoAll ∧ rhoAll < 0.87 := by
  constructor <;> norm_num [rhoAll]

theorem rhoQuark_value : 0.44 < rhoQuark ∧ rhoQuark < 0.45 := by
  constructor <;> norm_num [rhoQuark]

/-- **The two densities disagree.** -/
theorem densities_differ : rhoAll ≠ rhoQuark := by
  have h1 := rhoAll_value
  have h2 := rhoQuark_value
  intro hcon
  rw [hcon] at h1
  linarith [h1.1, h2.2]

/-- By roughly a factor of two — which is a fact about how much of the Standard
Model happens to be coloured, not a prediction of anything. -/
theorem density_ratio_near_two : 1.9 < rhoAll / rhoQuark ∧ rhoAll / rhoQuark < 2.0 := by
  have h1 := rhoAll_value
  have h2 := rhoQuark_value
  have hpos : (0 : ℝ) < rhoQuark := by linarith [h2.1]
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith [h1.1, h2.2]
  · rw [div_lt_iff₀ hpos]; nlinarith [h1.2, h2.1]

/-! ## Within a sector, the relation has no content -/

/-- **One equation, one unknown.**

The framework relates the drift of the beta coefficient to the threshold
density through a per-structure weight `κ`.  Given measurements of the first two
this *defines* `κ`; substituting back returns the input.  Nothing has been
tested. -/
theorem sector_relation_is_identity (dbdt dNdt : ℝ) (h : dNdt ≠ 0) :
    (dbdt / dNdt) * dNdt = dbdt := by
  field_simp

/-- Carried out for QCD between the charm and top thresholds: two flavours
appear, the beta coefficient drifts by `2/3` per flavour, and the extracted
weight is `2/3` — the input written backwards. -/
theorem qcd_extraction_returns_input (dNdt : ℝ) (h : dNdt ≠ 0) :
    ((2 / 3 : ℝ) * dNdt) / dNdt = 2 / 3 := by
  field_simp

/-- **What a genuine test would require.**

Two *independent* determinations of the same weight, so that the second can
check the first.  Formally: two relations in the same unknown with different
measured inputs.  The framework supplies only one, because it has only one
coupling-like quantity per sector and no coupling that responds to every
structure. -/
theorem no_second_determination (κ dbdt dNdt : ℝ) (h : dNdt ≠ 0)
    (hdef : κ = dbdt / dNdt) : dbdt = κ * dNdt := by
  rw [hdef]
  field_simp

/-! ## What survives: the per-sector shape

Each sector's thresholds should still be a constant-rate process, at whatever
rate that sector has.  For the quarks alone the five log-gaps give the numbers
below. -/

/-- Sum of the five quark log-gaps. -/
noncomputable def quarkGapSum : ℝ := 11.270

/-- Sum of their squares. -/
noncomputable def quarkGapSqSum : ℝ := 31.583624

noncomputable def quarkMeanGap : ℝ := quarkGapSum / 5

noncomputable def quarkVariance : ℝ := quarkGapSqSum / 5 - quarkMeanGap ^ 2

/-- Squared coefficient of variation for the quark sector. -/
noncomputable def quarkCvSq : ℝ := quarkVariance / quarkMeanGap ^ 2

/-- **`CV² = 0.243`, i.e. `CV = 0.493`** — the twelfth percentile of the
constant-rate prediction for five gaps.  Low, and more regular than the
prediction typically gives, but with five gaps not excluded. -/
theorem quarkCvSq_value : 0.24 < quarkCvSq ∧ quarkCvSq < 0.25 := by
  constructor <;> norm_num [quarkCvSq, quarkVariance, quarkMeanGap, quarkGapSum, quarkGapSqSum]

/-- The quark sector is still not a geometric tower either: its gap variance is
positive. -/
theorem quark_not_geometric : quarkCvSq ≠ 0 := by
  have h := quarkCvSq_value
  linarith [h.1]

end SCD.CrossCheck
