/-
# The scanning hypothesis: what it says, what it reduces to, and what it does not

`Scanning.lean` labels `λ = κρ` a proposal and everything downstream of it a
theorem.  This file goes after the proposal.  It does not close it, and the
useful part is *where* it fails to close, because that turns out to be a precise
place.

## I.  What the hypothesis actually says

`Scanning.scanRate κ ρ t := κ · ρ(t)` is a **definition**, so nothing downstream
of it can be evidence for it.  The physical content is elsewhere, and writing it
out isolates it exactly.

The accumulated dissipation `D` and the accumulated threshold count `N` are two
functions on the scale axis.  The hypothesis is that the first sees the second
and nothing else:

> **`FactorsThroughCount D N κ` : `D t − D t′ = κ (N t − N t′)` for all `t, t′`.**
>
> *The response depends on the thresholds only through their number.*

Given that, and given `Running.resolvedCount`'s uniform count `N t = ρ(t − t₀)`,
the rate is `κρ` — `rate_is_kappa_rho`, and it is the chain rule, not a
hypothesis.  So **`λ = κρ` is not itself the assumption**; the assumption is
factorisation through the count, and `λ = κρ` is what it gives.

This is worth having because factorisation is a statement one can argue about and
`λ = κρ` is not.  It is also **falsifiable** as an abstract condition
(`factorisation_is_falsifiable`), so it is a restriction and not bookkeeping.

## II.  It is the same statement that makes gravity universal — in form

`Index.lean`'s source is `ν`, and `Attraction.lean` argues `ν` must be a
**count** rather than a signed winding, because a signed source would make
antimatter antigravitate.  `Anchor.signed_source_is_distinguished` records that
this identification is *anchored*: the two readings differ observably and
antihydrogen selects between them.

Factorisation through the count is the same shape of statement — *the response
sees only how many, not which* — applied to the dissipation instead of to the
geometry.  That is a **reduction, not a derivation**, and the difference matters:
two statements of the same form about different quantities are not one statement.
What has been gained is that the scanning hypothesis is no longer a free-standing
proposal; it is the scanning sector's instance of a pattern the framework already
uses and has one anchored case of.

## III.  An argument that looks like it closes it, and does not

Here is the tempting move.  A per-threshold response must be **weight zero**
under `σ ↦ cσ` — `Weight.invSqCoupling_invariant` computes exactly that for the
gauge sector's `κ`.  It must also be **fiducial-invariant** by A5, so it can
depend on threshold positions only through differences
(`Expressive.invariant_iff_diffPattern`).  Weight zero kills the differences too,
since a difference has weight one.  What is left is the bare count — so
factorisation follows.

**It does not.**  Weight zero does not kill a *ratio* of differences.
`weight_zero_does_not_force_constancy` exhibits a per-threshold weight built from
three consecutive threshold positions,

        w(x, y, z) = (z − y) / (y − x) ,

which is invariant under `σ ↦ cσ`, invariant under the fiducial shift, and **not
constant**.  A response weighted by the local spacing ratio satisfies every
constraint the framework imposes and does not factor through the count.

So A5 and the weight grading — the two tools that have settled most questions of
this kind in the development — are jointly insufficient here, and that is the
sharp statement of the gap.  Something must forbid the response from seeing the
local spacing, and nothing in the framework currently does.

## IV.  And a downstream claim is weaker than advertised

`Scanning.two_anomalies_one_number` — the `w₀wₐ` tension and the `H₀` tension are
one number — holds **for every** density function `ρ`
(`two_anomalies_holds_for_every_density`).  A statement uniform in `ρ` cannot be
evidence about `ρ`: all it does is cancel `κ` between the numerator and the
denominator of a fraction, which is arithmetic on the definition of `scanRate`.

The physical content sits in two identifications that are not formalised
anywhere: that a `w₀wₐ` fit measures the fractional evolution of `D`, and that
the ladder-versus-ruler discrepancy measures the fractional variation of `ρ`.
Both are plausible and neither is a theorem.

So the "one mechanism, two anomalies" claim should be read as: **given
factorisation and given those two identifications**, the two anomalies are one
number.  That is still a real and falsifiable claim — if `w` evolves and the
ladders agree, the picture dies — but it is three inputs deep, not one, and
`Anchor.lean` was right not to count it among the framework's predictions.

## V.  Summary

* `λ = κρ` is the chain rule given factorisation through the count; the
  hypothesis is factorisation;
* factorisation is the scanning sector's instance of "the source is a count",
  which is anchored in the gravitational sector and not here;
* A5 plus the weight grading do **not** force it — the local spacing ratio is a
  counterexample, and that is the precise gap;
* the two-anomalies claim is uniform in `ρ` and therefore not evidence for the
  hypothesis.

Nothing is promoted from proposal to theorem.  What changes is that the proposal
now has one sentence, one anchored analogue, and one named obstruction.
-/
import SCD.Scanning
import SCD.Running
import SCD.Anchor

namespace SCD.Response

open SCD

/-! ## I. The hypothesis, written out -/

/-- **The response sees only the number.**

`D` is the accumulated dissipation along the scale axis and `N` the accumulated
threshold count.  Factorisation says every increment of `D` is `κ` times the
increment of `N` — the thresholds enter through their number and through nothing
else about them.

This is the scanning hypothesis.  `λ = κρ` is its consequence, not its
statement. -/
def FactorsThroughCount (D N : ℝ → ℝ) (κ : ℝ) : Prop :=
  ∀ t t', D t - D t' = κ * (N t - N t')

/-- **Given factorisation, `λ = κρ` is the chain rule.**

With `Running.resolvedCount`'s uniform count `N t = ρ(t − t₀)`, the increment of
the response over any interval is `κρ` times the interval.  No hypothesis is
used beyond factorisation itself. -/
theorem rate_is_kappa_rho (D : ℝ → ℝ) (κ rho t₀ : ℝ)
    (h : FactorsThroughCount D (fun t => Running.resolvedCount rho t₀ t) κ)
    (t t' : ℝ) :
    D t - D t' = κ * rho * (t - t') := by
  rw [h t t']
  simp only [Running.resolvedCount]
  ring

/-- **And the average rate is exactly `Scanning.scanRate`.**

So the object `Scanning.lean` defined is recovered rather than posited, once
factorisation is granted. -/
theorem average_rate_is_scanRate (D : ℝ → ℝ) (κ rho t₀ : ℝ)
    (h : FactorsThroughCount D (fun t => Running.resolvedCount rho t₀ t) κ)
    (t t' : ℝ) (hne : t - t' ≠ 0) :
    (D t - D t') / (t - t') = Scanning.scanRate κ (fun _ => rho) t := by
  rw [rate_is_kappa_rho D κ rho t₀ h t t']
  simp only [Scanning.scanRate]
  field_simp

/-- **Factorisation is a restriction, not bookkeeping.**

A response quadratic in the scale axis against a linear count fails it.  So the
hypothesis has content — which is what makes §III's failure to derive it a real
gap rather than a formality. -/
theorem factorisation_is_falsifiable :
    ∃ (D N : ℝ → ℝ) (κ : ℝ), ¬ FactorsThroughCount D N κ := by
  refine ⟨fun t => t ^ 2, fun t => t, 1, ?_⟩
  intro h
  have h2 := h 2 0
  norm_num at h2

/-! ## II. The argument that does not close

A per-threshold response must be weight zero under `σ ↦ cσ` and fiducial
invariant under A5.  It is tempting to conclude that it can therefore depend on
nothing but the count.  The following says otherwise. -/

/-- The local spacing **ratio** of three consecutive thresholds. -/
noncomputable def spacingRatio (x y z : ℝ) : ℝ := (z - y) / (y - x)

/-- It is weight zero: rescaling the log-scale leaves it alone. -/
theorem spacingRatio_weight_zero (c x y z : ℝ) (hc : c ≠ 0) :
    spacingRatio (c * x) (c * y) (c * z) = spacingRatio x y z := by
  simp only [spacingRatio]
  rw [show c * z - c * y = c * (z - y) by ring, show c * y - c * x = c * (y - x) by ring]
  exact mul_div_mul_left _ _ hc

/-- And fiducial invariant: shifting every scale together leaves it alone. -/
theorem spacingRatio_fiducial_invariant (b x y z : ℝ) :
    spacingRatio (x + b) (y + b) (z + b) = spacingRatio x y z := by
  simp only [spacingRatio]
  congr 1 <;> ring

/-- But it is **not constant**. -/
theorem spacingRatio_not_constant :
    ∃ x y z x' y' z' : ℝ, spacingRatio x y z ≠ spacingRatio x' y' z' := by
  refine ⟨0, 1, 2, 0, 1, 3, ?_⟩
  simp only [spacingRatio]
  norm_num

/-- **So A5 and the weight grading do not force factorisation.**

A per-threshold response weighted by the local spacing ratio is invariant under
everything the framework imposes and still varies from threshold to threshold, so
the accumulated response does not depend on the count alone.

The two tools that have settled most questions of this kind in the development
are jointly insufficient here.  **That is the precise gap**: something must forbid
the response from seeing the local spacing, and nothing currently does. -/
theorem weight_zero_does_not_force_constancy :
    (∀ c x y z : ℝ, c ≠ 0 →
        spacingRatio (c * x) (c * y) (c * z) = spacingRatio x y z)
    ∧ (∀ b x y z : ℝ, spacingRatio (x + b) (y + b) (z + b) = spacingRatio x y z)
    ∧ (∃ x y z x' y' z' : ℝ, spacingRatio x y z ≠ spacingRatio x' y' z') :=
  ⟨fun c x y z hc => spacingRatio_weight_zero c x y z hc,
   spacingRatio_fiducial_invariant, spacingRatio_not_constant⟩

/-! ## III. The downstream claim, weighed -/

/-- **`two_anomalies_one_number` holds for every density.**

Stated with the density universally quantified inside, which is how it is
actually proved: `κ` cancels between numerator and denominator whatever `ρ` is.

A statement uniform in `ρ` cannot be evidence about `ρ`.  Its content is the two
unformalised identifications — that a `w₀wₐ` fit measures the fractional
evolution of the response, and that the ladder-versus-ruler discrepancy measures
the fractional variation of the density — not the algebra. -/
theorem two_anomalies_holds_for_every_density (κ : ℝ) (hκ : κ ≠ 0) (t t' : ℝ) :
    ∀ rho : ℝ → ℝ,
      (Scanning.scanRate κ rho t - Scanning.scanRate κ rho t') / Scanning.scanRate κ rho t'
        = (rho t - rho t') / rho t' :=
  fun rho => Scanning.two_anomalies_one_number κ hκ rho t t'

/-- **Collected: the hypothesis, its consequence, and the gap.**

Factorisation gives `λ = κρ`; factorisation is a genuine restriction; and the
framework's two invariance tools do not imply it. -/
theorem summary (D : ℝ → ℝ) (κ rho t₀ : ℝ)
    (h : FactorsThroughCount D (fun t => Running.resolvedCount rho t₀ t) κ)
    (t t' : ℝ) :
    (D t - D t' = κ * rho * (t - t'))
    ∧ (∃ (D' N' : ℝ → ℝ) (κ' : ℝ), ¬ FactorsThroughCount D' N' κ')
    ∧ (∃ x y z x' y' z' : ℝ, spacingRatio x y z ≠ spacingRatio x' y' z') :=
  ⟨rate_is_kappa_rho D κ rho t₀ h t t', factorisation_is_falsifiable,
   spacingRatio_not_constant⟩

end SCD.Response
