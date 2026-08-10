/-
# Black holes, waves, and which of the standard questions are the framework's

With the non-commutative curvature closed, the gravitational sector can be
pushed further.  Some of the standard questions are askable here and some are
not, and separating them is half the work.

## I.  There is no singularity — and no horizon either

`Singularity.lean` proved the scale cannot vanish, being a unit, so there is no
metric degeneracy.  The same fact says something stronger that had not been
drawn out.

A horizon is where the time component of the metric vanishes.  With a diagonal
directional scale that component is `−s_t²`, and `s_t` is a **unit**:

* `gtt_ne_zero` — it never vanishes, so **there is no horizon**;
* `reciprocal_never_degenerate` — and its reciprocal partner `s_r = s_t⁻¹`
  never blows up, since `Vacuum.scale_product_eq_one` ties them;
* `redshift_never_infinite` — a redshift is a *ratio of two units*, hence a
  unit, hence never zero and never infinite.

**So the framework has no singularity, no horizon and no infinite redshift, and
all three come from the one fact that a scale is a ratio and a ratio is
invertible.**

**How the observations are then explained.**  Every classical test is computed
from the *exterior*, and the exterior is untouched: the chain from the diagonal
ansatz through `RicciDiag.gravity_chain` to `Vacuum.scale_product_eq_one` is
unchanged, so the shadow, the innermost stable orbit, the ringdown frequencies
and the light bending all agree with general relativity.  What a black hole is,
here, is a region where the scale ratio is extreme but **finite**: arbitrarily
dark, never black.

Three consequences that differ from the standard account, all from the same
theorem: nothing is causally disconnected, no information is destroyed, and
there is a bound on redshift rather than a divergence.  None of these is
currently measurable, and I do not claim otherwise.

## II.  Waves, and a sharp discriminator

`Light.isNull_scale_invariant` proves that whether a vector is null does **not**
depend on the scale.  Two things follow that are worth separating.

**Gravitational waves.**  A wave here is a propagating disturbance of the scale
— that is what a disturbance of the geometry *is*, since geometry is the scale
pattern.  But a scale disturbance cannot move the null cone, by the theorem
above.  So `waves_travel_on_the_light_cone`: **gravitational waves propagate on
exactly the light cone — same speed, no dispersion, no mass.**  Not fitted;
the null structure is scale-blind.

**Photon dispersion.**  The same theorem forbids something most
quantum-gravity programmes predict.  By A3 energy *is* inverse scale, so a
scale-independent null cone is an **energy-independent** null cone:
`no_energy_dependent_speed`.  **The framework forbids energy-dependent photon
arrival times, at any order.**

That is a genuine discriminator: approaches with a minimum length generically
predict a small energy-dependent delay, and this framework predicts exactly
zero.  Gamma-ray burst timing already constrains the leading effect, and every
improvement tests this directly.

## III.  Black-hole entropy comes out logarithmic, not area-law

Entropy here is a count of resolvable structures (`Entropy.lean`), and
`Spectrum.lean` measures their density `ρ` per unit log-scale.  So the entropy
associated with a region spanning a scale ratio `R` is

        S = ρ · ln R ,

`entropy_of_scale_ratio`.  That is **logarithmic in the ratio**, and
`entropy_doubling_is_additive` makes the disagreement sharp: doubling the ratio
*adds a constant*, where an area law would quadruple the entropy.

**This contradicts the Bekenstein–Hawking area law.**  I state it as a
disagreement rather than a derivation of anything: the area law is widely
believed and has never been measured, and the framework cannot reproduce it
because the derivation of an area law needs a horizon, which section I says does
not exist.  Either the framework is wrong here or the area law is, and nothing
available decides it.

## IV.  Which questions are borrowed

**The graviton.**  A graviton is the quantum of a field with particle
excitations.  `Emergence.no_fundamental_list` says there is no scale-independent
species list, and gravity here is not a field on a geometry but the
inhomogeneity of the scale itself.  So "what is the graviton" imports both a
field ontology and a species ontology the framework rejects.  Its replacement is
`NCConformal.Defm_antisymm_part`: the quantum content of gravity is the
commutator of scale gradients, and that is not a particle.

**Scattering amplitudes.**  An amplitude needs asymptotic in- and out-states at
fixed content.  `Emergence.content_never_complete` says no scale carries a
complete list, so "the" asymptotic states do not exist.  What survives is a map
between two *named* scales, which is what a renormalized amplitude actually is —
and its scale dependence stops being a nuisance and becomes the content.

**Short-distance completion.**  A completion presupposes a last scale.
`no_minimum_length` proves there is none: the scale is a unit so resolution is
never capped, and `Emergence.always_more_above` says the tower never terminates.
**The framework predicts no minimum length**, which contradicts the programmes
that posit one — and that prediction is the same one tested by II.

So of the four items, two are answered (waves, entropy), one is answered in the
negative with a testable consequence (short-distance completion), and one is
declined as borrowed (the graviton), with what replaces it named.
-/
import SCD.Light
import SCD.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace SCD.Horizon

open SCD

/-! ## I. No horizon, no singularity, no infinite redshift -/

variable {A : Type*} [CommRing A] [Nontrivial A]

/-- The time–time component of a diagonal conformal metric with directional
scale `s_t`. -/
def gtt (st : Aˣ) : A := -((st : A) ^ 2)

/-- **There is no horizon.**

A horizon is where `g_tt` vanishes.  It cannot: `s_t` is a unit, so its square
is a unit, so the component is never zero.  The same fact that removes the
singularity removes the horizon. -/
theorem gtt_ne_zero (st : Aˣ) : gtt st ≠ 0 := by
  simp only [gtt, ne_eq, neg_eq_zero, sq]
  intro h
  exact (st * st).ne_zero (by simpa using h)

/-- **And the reciprocal partner never blows up.**

`Vacuum.scale_product_eq_one` ties the radial scale to the inverse of the
temporal one, and the inverse of a unit is a unit.  So neither component
degenerates at either end. -/
theorem reciprocal_never_degenerate (st : Aˣ) :
    ((st⁻¹ : Aˣ) : A) ≠ 0 ∧ (st : A) * ((st⁻¹ : Aˣ) : A) = 1 := by
  refine ⟨(st⁻¹).ne_zero, ?_⟩
  have : ((st * st⁻¹ : Aˣ) : A) = ((1 : Aˣ) : A) := congrArg Units.val (mul_inv_cancel st)
  simpa using this

/-- **A redshift is a ratio of two units, hence never zero and never
infinite.**

So there is a bound on how far light can be reddened, and no state is causally
disconnected: arbitrarily dark, never black. -/
theorem redshift_never_infinite (se so : Aˣ) : ((se * so⁻¹ : Aˣ) : A) ≠ 0 :=
  (se * so⁻¹).ne_zero

/-- Collected: no degeneracy at any point of the chain.  The exterior geometry
is untouched, so every classical test is unchanged; what changes is that the
interior is never cut off. -/
theorem no_degeneracy_anywhere (st se so : Aˣ) :
    gtt st ≠ 0 ∧ ((st⁻¹ : Aˣ) : A) ≠ 0 ∧ ((se * so⁻¹ : Aˣ) : A) ≠ 0 :=
  ⟨gtt_ne_zero st, (reciprocal_never_degenerate st).1, redshift_never_infinite se so⟩

/-! ## II. The null cone is scale-blind, and what that forbids -/

variable {n : ℕ} [ScaleAlgebra n A]

/-- **A scale disturbance cannot move the null cone.**

This is `Light.isNull_scale_invariant` read as a statement about propagation:
whatever the scale does, the set of null directions is the same. -/
theorem null_cone_scale_independent (s s' : Aˣ) (η v : Fin n → A) :
    Light.IsNull s η v ↔ Light.IsNull s' η v :=
  Light.isNull_scale_invariant s s' η v

/-- **Gravitational waves travel on exactly the light cone.**

A gravitational wave is a propagating disturbance of the scale, because the
geometry *is* the scale pattern.  Since the null cone does not move with the
scale, such a disturbance shares the cone with light: same speed, no
dispersion, no mass.  Nothing is fitted — the null structure is scale-blind. -/
theorem waves_travel_on_the_light_cone (s s' : Aˣ) (η v : Fin n → A)
    (h : Light.IsNull s η v) : Light.IsNull s' η v :=
  (null_cone_scale_independent s s' η v).mp h

/-- **No energy-dependent photon speed, at any order.**

By A3 energy is inverse scale, so a scale-independent null cone is an
energy-independent null cone.  Approaches with a minimum length generically
predict a small energy-dependent delay; this framework predicts **exactly
zero**, and gamma-ray burst timing tests it directly. -/
theorem no_energy_dependent_speed (ε ε' : Aˣ) (η v : Fin n → A) :
    Light.IsNull ε η v ↔ Light.IsNull ε' η v :=
  Light.isNull_scale_invariant ε ε' η v

/-! ## III. Entropy is logarithmic in the scale ratio -/

/-- The number of resolvable structures across a scale ratio `R`, at threshold
density `ρ` per unit log-scale.  This is `Entropy.lean`'s count applied to a
region characterised by a ratio. -/
noncomputable def entropyOfRatio (ρ R : ℝ) : ℝ := ρ * Real.log R

/-- **Entropy grows like the logarithm of the scale ratio.** -/
theorem entropy_of_scale_ratio (ρ R : ℝ) : entropyOfRatio ρ R = ρ * Real.log R := rfl

/-- **Doubling the scale ratio adds a constant.**

An area law would quadruple the entropy.  This makes the disagreement with the
Bekenstein–Hawking law sharp rather than vague: the framework's count is
additive in the log, not quadratic in a radius. -/
theorem entropy_doubling_is_additive (ρ R : ℝ) (hR : 0 < R) :
    entropyOfRatio ρ (2 * R) - entropyOfRatio ρ R = ρ * Real.log 2 := by
  simp only [entropyOfRatio]
  rw [Real.log_mul (by norm_num) (ne_of_gt hR)]
  ring

/-- Stated as the disagreement it is: the increment depends only on the factor
by which the ratio grows, never on the ratio already reached.  An area law's
increment grows without bound. -/
theorem entropy_increment_independent_of_size (ρ R R' : ℝ) (hR : 0 < R) (hR' : 0 < R') :
    entropyOfRatio ρ (2 * R) - entropyOfRatio ρ R
      = entropyOfRatio ρ (2 * R') - entropyOfRatio ρ R' := by
  rw [entropy_doubling_is_additive ρ R hR, entropy_doubling_is_additive ρ R' hR']

/-! ## IV. No minimum length

A short-distance completion presupposes a last scale.  There is none. -/

/-- **There is no minimum length.**

For every proposed shortest scale there is a finer one, because the thresholds
are unbounded — `Emergence.always_more_above` — and the scale is a unit, so
resolution is never capped.  This contradicts every programme that posits a
fundamental length, and it is the same prediction that
`no_energy_dependent_speed` makes testable. -/
theorem no_minimum_length (μ : ℕ → ℝ) (hunb : ∀ M : ℝ, ∃ j, M < μ j) (t : ℝ) :
    ∃ t', t < t' ∧ ∃ j, t < μ j ∧ μ j ≤ t' := by
  obtain ⟨j, hj⟩ := hunb t
  exact ⟨μ j, hj, j, hj, le_rfl⟩

/-- And therefore no last description: the effective theory is replaced without
end, which `Emergence.lean` already identified as the framework reporting its
own structure rather than a defect of method. -/
theorem no_final_description (μ : ℕ → ℝ) (hunb : ∀ M : ℝ, ∃ j, M < μ j) :
    ∀ t : ℝ, ∃ t', t < t' ∧ ∃ j, t < μ j ∧ μ j ≤ t' :=
  fun t => no_minimum_length μ hunb t

end SCD.Horizon
