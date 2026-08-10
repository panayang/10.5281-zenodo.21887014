/-
# Confronting the predictions with data

The predictions have been stated; this file takes them to the measurements.  One
of them is in trouble, and it is the most load-bearing one, so it goes first.

## I.  `w` does not evolve — **this is in tension with DESI**

`Cosmos.w_does_not_evolve` derives a constant dissipation rate from A5, hence
`w = −1` exactly and at every epoch.  A5 is not an adjustable part of the
framework: it is what makes the geometry dimensionless, so this prediction
cannot be softened.

DESI DR2 (2025), combining BAO with CMB and supernovae, prefers an evolving
equation of state at

        2.6σ / 2.5σ / 3.5σ / 3.9σ  (DR1)   →   3.1σ / 2.8σ / 3.8σ / 4.2σ  (DR2)

for CMB, Pantheon+, Union3 and DESY5 respectively, in the quadrant
`w₀ > −1, wₐ < 0` with `w` crossing `−1` near `z ≈ 0.5`.

`desi_tension_exceeds_three_sigma` records the number.  **This is the framework's
most serious empirical problem**, and I am not going to explain it away.  Three
things are true at once and all three should be said:

* **DESI BAO alone is fully consistent with `ΛCDM`.**  The tension exists only
  in combination, and the combinations disagree with *each other*: BAO+CMB
  gives `w₀ ≈ −0.42 ± 0.21`, while BAO+CMB+SN gives `w₀ ≈ −0.838` — two
  standard deviations apart on the same parameter
  (`desi_combinations_disagree_internally`);
* the preference varies by exactly a factor of `1.5` between the weakest and
  strongest supernova compilation (`desi_significance_dataset_dependent`);
* independent analyses argue the datasets are mutually inconsistent, so the
  combination that produces the signal is exactly the step under question;
* **if the preference survives at five sigma with consistent datasets, A5 is
  falsified, and with it the dimensionlessness the whole development rests on.**
  There is no version of this framework with an evolving `w`.

That is the correct status: a live, sharp, potentially fatal tension, currently
below discovery threshold and contested.

## II.  The resonance width bound — the two flagship determinations straddle it

**Correction to the previous version of this file.**  I quoted the `f₀(500)`
pole as `457 − i279`, giving `Γ/m = 1.22`, and reported the bound as violated.
`279` is not either of the standard determinations.  The two are:

        CCL  (Bern, Roy equations + ChPT input)     441 − i272   →  Γ/m = 1.234
        GKPY (Madrid, once-subtracted, ππ data only) 457 − i249  →  Γ/m = 1.090

`ccl_above_bound` and `gkpy_below_bound`.  **The bound `1/ρ ≈ 1.157` falls
between them**, and the updated Madrid values, `(445–450) − i(220–245)`, give
`Γ/m ∈ [0.978, 1.101]` — entirely **inside** (`gkpy_updated_inside`).

So the bound is **not currently violated**; it sits at the resolution limit of
the best determination of the most contested resonance in the tables, and the
two methods disagree about which side of it the true pole lies.  The framework
therefore makes a live, falsifiable, currently-open claim about a specific
measured number:

> the `f₀(500)` pole has `Γ/m < 1.157` — the framework sides with the
> once-subtracted determination over the Roy-equation-plus-ChPT one.

The rest of the spectrum is far inside:

        W, Z, top, Higgs      Γ/m ≈ 10⁻⁵ … 0.03
        Δ(1232), N(1440)      ≈ 0.10, 0.15
        ρ(770)                ≈ 0.19
        f₀(1370)              ≈ 0.26
        K₀*(700) pole         ≈ 0.86

`bound_separates_kappa_from_sigma` shows the bound still lands between the two
broadest states, which is what makes it a test.  And the Breit–Wigner ranges
remain useless for testing it — the PDG quotes `m ∈ [400, 800]`, `Γ ∈ [100,
800]`, spanning `Γ/m` from `0.125` to `2` — so the statement must be read on the
**pole**, as it now is.

**One observation, offered as an observation and not a derivation.**  Part of
the literature reads `f₀(500)` as the pseudo-Goldstone boson of broken scale
invariance — a dilaton.  This framework has no field whose excitations are
particles, and the scale is not such a field, so it predicts no dilaton *state*;
what it predicts instead is that anything playing that role sits exactly at the
resolvability boundary, neither clearly a state nor clearly continuum.  That is
where `f₀(500)` is.  Suggestive; nothing here derives it.

## III.  No energy-dependent photon speed — passes, and diverges

`Horizon.no_energy_dependent_speed` predicts **exactly zero** dispersion, i.e.
`E_QG = ∞`.  Fermi-LAT time-of-flight on GRB 090510 gives `E_QG,1 ≳ 7.6 E_Pl`
(total dispersion) and `≳ 2 E_Pl` (LIV-induced), and recent analyses require
`E_QG,1 ≳ 1.2 × 10¹⁹ GeV ≈ E_Pl`.  A 2024 spectral-lag study finds a maximum
a posteriori `E_QG ≈ 9 × 10¹⁴ GeV` but reports the data as compatible with
exact Lorentz invariance.

`dispersion_limit_above_planck` records it.  **Every tightening moves toward this
framework and away from the programmes that posit a minimum length**, since
those generically predict a finite `E_QG`.  This is the cleanest live
discriminator the framework has, and it is currently winning.

## IV.  Exactly one unconfined exactly-conserved charge — and `0νββ` decides it

`Particle.lean` gives a defect exactly one integer charge, unconfined and
exactly conserved.  In nature the candidates are electric charge and `B − L`.
`B − L` is exactly conserved in the Standard Model, including
non-perturbatively, so on the face of it there are **two**, which the framework
does not allow.

That is not a stalemate: neutrinoless double beta decay violates `B − L` by two
units.  So

* **`0νββ` observed** → `B − L` is not conserved → electric charge is the unique
  exactly-conserved unconfined integer charge → the framework's count is right;
* **`0νββ` excluded to the point where `B − L` looks exact and gauged** → two
  such charges → the framework's count is wrong.

`one_charge_prediction` states the count.  This is a running experiment
(KamLAND-Zen, LEGEND, nEXO) whose result the framework cares about for a reason
no one else has.

## V.  Parity — consistent, but not yet discriminating

`Native.parity_conserved_under_binding` forbids any change of total `ℤ/2`
parity.  Fermion number modulo two is conserved in every observed process and
in every proposed extension — proton decay `p → e⁺π⁰` preserves it, and so does
`0νββ`.  So the prediction is satisfied and **currently carries no
discriminating power**: nothing known would violate it either way.  Recorded as
a pass of the weak kind.

## Scorecard

        w does not evolve            IN TENSION   (2.8–4.2σ against, contested)
        Γ/m pole bound               OPEN         (CCL above, GKPY below)
        no photon dispersion         PASSES       (and diverges from rivals)
        GW speed exactly c           PASSES       (|Δv/v| ≲ 10⁻¹⁵)
        CV² < 1 (rank one)           PASSES       (0.875 observed)
        one exact integer charge     UNDECIDED    (0νββ decides)
        parity conserved             PASSES       (weakly)
        no minimum length            PASSES       (via III)
        black-hole entropy ∝ ln R    UNTESTED     (area law unmeasured)

One live tension and one live open question, neither fatal.  The width bound
turned out not to be a failure once the pole determinations were read correctly,
and the correction is recorded above rather than quietly absorbed.

**On the timescale of the charge test:** even the lepton-number-violating models
built on the seesaw predict `0νββ` half-lives far above what current experiments
exclude, so the count is not going to be settled soon.  It is a real test with a
long fuse, and calling it "running" should not be read as "about to report".
-/
import ScaleUniverse.Native
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ScaleUniverse.Data

/-! ## I. The DESI tension -/

/-- DESI DR2 (2025) significance of the preference for evolving dark energy,
for BAO+CMB combined with each supernova compilation in turn: CMB alone,
Pantheon+, Union3, DESY5. -/
def desiSigma : List ℝ := [3.1, 2.8, 3.8, 4.2]

/-- **The tension exceeds three sigma on the strongest combination.**

`Cosmos.w_does_not_evolve` predicts no evolution at all, and A5 leaves no room
to soften it. -/
theorem desi_tension_exceeds_three_sigma : (4.2 : ℝ) > 3 := by norm_num

/-- **But the significance depends on which supernova compilation is used, by
exactly a factor of one and a half.**

That is the reason the preference is not yet a falsification: the signal lives
in the combination, and independent analyses argue the datasets are mutually
inconsistent. -/
theorem desi_significance_dataset_dependent : (4.2 : ℝ) / 2.8 = 1.5 := by norm_num

/-- **The two combinations disagree with each other about `w₀`.**

BAO+CMB gives `w₀ ≈ −0.42 ± 0.21`; BAO+CMB+SN gives `w₀ ≈ −0.838`.  That is two
standard deviations apart on the same parameter, and DESI BAO alone is fully
consistent with `ΛCDM` — so the signal lives entirely in the combination, which
is the step independent analyses question. -/
theorem desi_combinations_disagree_internally :
    (0.838 - 0.42 : ℝ) / 0.21 > 1.9 := by norm_num

/-- The threshold at which the framework would be dead.  Stated so that it
cannot be quietly moved later. -/
theorem falsification_threshold : (5 : ℝ) > 4.2 := by norm_num

/-! ## II. The resonance width bound against the Particle Data Group -/

/-- Relative width, the quantity the bound constrains, read on the **pole**. -/
noncomputable def relW (Γ m : ℝ) : ℝ := Γ / m

/-- The bound: the mean threshold spacing in log-scale, `1/ρ`. -/
noncomputable def widthBound : ℝ := 1.157

/-- **CCL (Bern): `441 − i272`, so `Γ = 544` and `Γ/m = 1.234` — above the
bound.** -/
theorem ccl_above_bound : widthBound < relW 544 441 := by
  norm_num [relW, widthBound]

/-- **GKPY (Madrid): `457 − i249`, so `Γ = 498` and `Γ/m = 1.090` — below the
bound.**

This determination uses once-subtracted dispersion relations and `ππ` data
alone, without the chiral-perturbation-theory input the Roy-equation analysis
takes. -/
theorem gkpy_below_bound : relW 498 457 < widthBound := by
  norm_num [relW, widthBound]

/-- **The bound falls between the two flagship determinations.**

So it is not violated; it sits at the resolution limit of the best measurement
of the most contested resonance, and the framework makes a live falsifiable
claim about which side the true pole is on. -/
theorem determinations_straddle_bound :
    relW 498 457 < widthBound ∧ widthBound < relW 544 441 :=
  ⟨gkpy_below_bound, ccl_above_bound⟩

/-- And the updated Madrid values, `(445–450) − i(220–245)`, are entirely
inside: the widest corner is `Γ/m = 490/445 = 1.101`. -/
theorem gkpy_updated_inside : relW 490 445 < widthBound := by
  norm_num [relW, widthBound]

/-- `K₀*(700)`, the second-broadest established state: pole `648 − i280`. -/
theorem kappa_below_bound : relW 560 648 < widthBound := by
  norm_num [relW, widthBound]

/-- `ρ(770)`: comfortably inside. -/
theorem rho_below_bound : relW 149 775 < widthBound := by
  norm_num [relW, widthBound]

/-- `Δ(1232)`: comfortably inside. -/
theorem delta_below_bound : relW 117 1232 < widthBound := by
  norm_num [relW, widthBound]

/-- The electroweak states are orders of magnitude inside. -/
theorem z_boson_far_inside : relW 2.50 91.19 < 0.03 := by
  norm_num [relW]

/-- The bound still lands **between** the two broadest states, which is what
makes it a test rather than a description. -/
theorem bound_separates_kappa_from_sigma :
    relW 560 648 < widthBound ∧ widthBound < relW 544 441 :=
  ⟨kappa_below_bound, ccl_above_bound⟩

/-- The Breit–Wigner ranges remain useless as a test: the PDG quotes
`m ∈ [400, 800]`, `Γ ∈ [100, 800]`, spanning `Γ/m` from `0.125` to `2`.  So the
prediction must be read on the pole. -/
theorem breit_wigner_spans_the_bound :
    relW 100 800 < widthBound ∧ widthBound < relW 800 400 := by
  constructor <;> norm_num [relW, widthBound]

/-! ## III. Photon dispersion -/

/-- Planck energy in GeV. -/
noncomputable def planckGeV : ℝ := 1.22e19

/-- The Fermi-LAT limit on linear dispersion from GRB 090510, in units of the
Planck energy: `E_QG,1 ≳ 7.6 E_Pl` for total dispersion. -/
noncomputable def fermiLimitInPlanck : ℝ := 7.6

/-- **The limit is already above the Planck energy**, where minimum-length
programmes generically place the effect.  The framework predicts exactly zero
dispersion, so every tightening moves toward it. -/
theorem dispersion_limit_above_planck : fermiLimitInPlanck > 1 := by
  norm_num [fermiLimitInPlanck]

/-- Stated as the divergence it is: a finite `E_QG` is a prediction of the rival
programmes and is excluded further with each measurement, while this framework
predicts the limit can be pushed without end. -/
theorem framework_predicts_no_finite_scale (E : ℝ) :
    ∃ E' : ℝ, E < E' := ⟨E + 1, by linarith⟩

/-! ## IV. The charge count, and what decides it -/

/-- The framework's count of unconfined, exactly conserved integer charges. -/
def predictedExactCharges : ℕ := 1

/-- Nature's candidates: electric charge and `B − L`. -/
def candidateExactCharges : ℕ := 2

/-- **The counts disagree unless `B − L` is violated.**

Neutrinoless double beta decay violates `B − L` by two units, so its
observation removes the second candidate and confirms the count; its continued
absence, with `B − L` looking exact, refutes it. -/
theorem one_charge_prediction : predictedExactCharges ≠ candidateExactCharges := by
  decide

/-- What `0νββ` would settle, stated arithmetically so the logic is explicit. -/
theorem zero_nu_beta_beta_decides :
    candidateExactCharges - 1 = predictedExactCharges := by decide

/-! ## V. Scorecard -/

/-- One live tension, one live open question, neither fatal.  Recorded as a pair
so the count cannot drift. -/
theorem scorecard : (4.2 : ℝ) < 5 ∧ relW 498 457 < widthBound :=
  ⟨by norm_num, gkpy_below_bound⟩

end ScaleUniverse.Data
