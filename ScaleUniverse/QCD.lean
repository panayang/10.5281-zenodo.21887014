/-
# The strong sector: a scale out of nothing

A5 says no scale is preferred: the theory is dimensionless and a global shift
of the fiducial is unobservable.  Yet the strong interaction manifestly *has* a
scale — hadrons have definite masses.  If the framework cannot account for
that, it fails at exactly the place where scale physics is hardest.

It accounts for it, and the mechanism is the one phenomenon in the Standard
Model that is purely about scale: **dimensional transmutation**.  A coupling
that is a pure number, running under A5's fiducial flow, secretes an invariant
scale `Λ` that appears nowhere in the axioms.  Scale invariance is not violated
by fiat; it is broken by the *solutions* of a scale-covariant equation.

Proved here, from one-loop running `dg/dt = −bg³` with `b > 0`:

* `running_inv_sq` — the exact solution `g⁻²(t) = g⁻²(0) + 2bt`;
* `asymptotic_freedom` — `g → 0` at high scale, so the strong sector becomes
  free where the scale is small;
* `lambda_invariant` — **`Λ = exp(t − g⁻²/2b)` is constant along the flow**.
  A dimensionless coupling has produced a scale, and by A5 no fiducial choice
  can move it;
* `hadron_mass_ratio` — since `Λ` is the only scale available, every hadron
  mass is a pure number times `Λ`, so **all mass ratios are parameter-free**.

The last point is where the framework meets data, and it is confronted with
lattice glueball masses at the end of the file — including a ratio test that
the simplest version of the geometric tower of `Defect.lean` **fails**.  That
failure is reported rather than hidden: it is the most informative number in
this development.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ScaleUniverse.QCD

open Real

/-! ## One-loop running -/

/-- **Exact solution of the one-loop equation.**

From `dg/dt = −bg³` alone, `g⁻²` is linear in the log-scale with slope `2b`.
No perturbative expansion is used; the statement is exact for the given flow. -/
theorem running_inv_sq (b : ℝ) (g : ℝ → ℝ) (hne : ∀ t, g t ≠ 0)
    (hd : ∀ t, HasDerivAt g (-b * (g t) ^ 3) t) (t : ℝ) :
    ((g t) ^ 2)⁻¹ = ((g 0) ^ 2)⁻¹ + 2 * b * t := by
  set u : ℝ → ℝ := fun r => ((g r) ^ 2)⁻¹ - 2 * b * r with hu_def
  have hderiv : ∀ r, HasDerivAt u 0 r := by
    intro r
    have hg := hne r
    have hsqne : (g r) ^ 2 ≠ 0 := pow_ne_zero 2 hg
    have h := (hd r).pow 2
    have heq : ((2 : ℕ) : ℝ) * (g r) ^ (2 - 1) * (-b * (g r) ^ 3)
        = -(2 * b * (g r) ^ 4) := by
      norm_num
      ring
    rw [heq] at h
    have hsq : HasDerivAt (fun x => (g x) ^ 2) (-(2 * b * (g r) ^ 4)) r := h
    have hval : -(-(2 * b * (g r) ^ 4)) / ((g r) ^ 2) ^ 2 = 2 * b := by
      rw [div_eq_iff (pow_ne_zero 2 hsqne)]
      ring
    have hinv : HasDerivAt (fun x => ((g x) ^ 2)⁻¹) (2 * b) r := by
      have h2 := hsq.inv hsqne
      rwa [hval] at h2
    have hlin : HasDerivAt (fun r : ℝ => 2 * b * r) (2 * b) r := by
      simpa using (hasDerivAt_id r).const_mul (2 * b)
    have hcomb := hinv.sub hlin
    have hz : (2 * b : ℝ) - 2 * b = 0 := by ring
    rwa [hz] at hcomb
  have hconst : ∀ x y, u x = u y :=
    is_const_of_deriv_eq_zero (fun r => (hderiv r).differentiableAt)
      (fun r => (hderiv r).deriv)
  have h0 := hconst t 0
  simp only [hu_def] at h0
  linarith [h0]

/-- **Asymptotic freedom.**  The coupling tends to zero at high log-scale: the
strong sector becomes free precisely where the local scale is small.  This is
the behaviour A3 demands, since small scale is high energy. -/
theorem asymptotic_freedom (b : ℝ) (hb : 0 < b) (g : ℝ → ℝ) (hne : ∀ t, g t ≠ 0)
    (hd : ∀ t, HasDerivAt g (-b * (g t) ^ 3) t) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t, T < t → (g t) ^ 2 < ε := by
  refine ⟨(1 / ε - ((g 0) ^ 2)⁻¹) / (2 * b), fun t ht => ?_⟩
  have hsol := running_inv_sq b g hne hd t
  have hx : (0 : ℝ) < (g t) ^ 2 := by
    have := hne t
    positivity
  have hxinv : (g t) ^ 2 * ((g t) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hx)
  have h2b : (0 : ℝ) < 2 * b := by linarith
  rw [div_lt_iff₀ h2b] at ht
  have hbig : 1 / ε < ((g t) ^ 2)⁻¹ := by
    rw [hsol]; nlinarith [ht]
  have key : (g t) ^ 2 * (1 / ε) < (g t) ^ 2 * ((g t) ^ 2)⁻¹ :=
    mul_lt_mul_of_pos_left hbig hx
  rw [hxinv, mul_one_div, div_lt_one hε] at key
  exact key

/-! ## Dimensional transmutation

Here is the point of the file.  The flow equation contains no scale.  Its
solutions do. -/

/-- The scale secreted by the running coupling. -/
noncomputable def Lambda (b : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (t - ((g t) ^ 2)⁻¹ / (2 * b))

/-- **Dimensional transmutation.**

`Λ` is *constant along the flow*: a theory whose only input is a dimensionless
number has produced a scale, and by A5 no choice of fiducial can shift it.

This is how a scale-invariant axiom system comes to describe a world with
definite hadron masses.  The invariance is not broken in the axioms — it is
broken by the solution, which is the only way it could be broken in a theory
that has no dimensionful parameter to break it with. -/
theorem lambda_invariant (b : ℝ) (hb : b ≠ 0) (g : ℝ → ℝ) (hne : ∀ t, g t ≠ 0)
    (hd : ∀ t, HasDerivAt g (-b * (g t) ^ 3) t) (t : ℝ) :
    Lambda b g t = Lambda b g 0 := by
  simp only [Lambda]
  congr 1
  rw [running_inv_sq b g hne hd t]
  field_simp
  ring

/-- The strong scale is genuinely positive: it is a scale, not a formal
symbol. -/
theorem lambda_pos (b : ℝ) (g : ℝ → ℝ) (t : ℝ) : 0 < Lambda b g t :=
  Real.exp_pos _

/-! ## Consequences for the spectrum

`Λ` is the only scale in the strong sector.  By A3 mass is inverse scale, so
every hadron mass must be a pure number times `Λ`. -/

/-- A hadron mass: a pure number times the transmuted scale. -/
noncomputable def hadronMass (c Λ : ℝ) : ℝ := c * Λ

/-- **All mass ratios in the strong sector are parameter-free.**

The ratio of any two hadron masses is a ratio of pure numbers, independent of
`Λ` — hence independent of every input to the theory.  This is the sharpest
prediction the framework makes about the strong sector, and it is the reason
glueballs are the right place to test it: their masses involve no quark mass,
so `Λ` is genuinely the only scale in play. -/
theorem hadron_mass_ratio (c₁ c₂ Λ : ℝ) (hΛ : Λ ≠ 0) (hc₂ : c₂ ≠ 0) :
    hadronMass c₁ Λ / hadronMass c₂ Λ = c₁ / c₂ := by
  simp only [hadronMass]
  field_simp

/-- Rescaling `Λ` moves every mass together: the spectrum has one overall
normalisation and no other freedom. -/
theorem spectrum_rigid (c Λ k : ℝ) : hadronMass c (k * Λ) = k * hadronMass c Λ := by
  simp only [hadronMass]; ring

/-! ## Confrontation with lattice glueball masses

Quenched lattice QCD gives, in MeV:
`0⁺⁺ ≈ 1710`, `2⁺⁺ ≈ 2390`, `0⁻⁺ ≈ 2560`.

`Defect.lean` predicts a *geometric* tower: consecutive mass ratios equal.  We
test that against these three states. -/

/-- Ratio of the first two lattice glueball masses. -/
noncomputable def ratio₁ : ℝ := 2390 / 1710

/-- Ratio of the next two. -/
noncomputable def ratio₂ : ℝ := 2560 / 2390

/-- **The simplest geometric tower fails.**

The two consecutive ratios differ by more than `0.3` — they are `1.398` and
`1.071`.  A single geometric tower across all glueball states is therefore
excluded by lattice data.

What exactly is refuted matters, and an audit narrowed it.  The geometric
tower follows from the *posited* mass law of `Defect.mass`, which
`MassAudit.mass_law_underdetermined` shows is not fixed by the topology.  So
this result refutes **that hypothesis**, not the defect picture and not the
framework.  A defect spectrum with, say, strain energy quadratic in the winding
has non-constant ratios and is untouched by this test
(`MassAudit.massQuad_ratio_not_constant`).

What survives independently: the parameter-free ratio statement
`hadron_mass_ratio`, which uses no mass law at all. -/
theorem geometric_tower_fails : 0.3 < |ratio₁ - ratio₂| := by
  rw [abs_of_pos (by norm_num [ratio₁, ratio₂])]
  norm_num [ratio₁, ratio₂]

/-- For the record, the two ratios, bracketed. -/
theorem ratio₁_value : 1.39 < ratio₁ ∧ ratio₁ < 1.40 := by
  constructor <;> norm_num [ratio₁]

theorem ratio₂_value : 1.07 < ratio₂ ∧ ratio₂ < 1.08 := by
  constructor <;> norm_num [ratio₂]

/-- The surviving prediction, in the form to be tested: with `Λ ≈ 332 MeV`
the lightest glueball sits at `m/Λ ≈ 5.15`, a pure number the framework must
eventually compute rather than fit. -/
noncomputable def lightestGlueballInLambda : ℝ := 1710 / 332

theorem lightestGlueballInLambda_value :
    5.1 < lightestGlueballInLambda ∧ lightestGlueballInLambda < 5.2 := by
  constructor <;> norm_num [lightestGlueballInLambda]

end ScaleUniverse.QCD
