/-
# The weight of the dissipation rate, and how far it gets

`Overdetermination.lean` reduced everything dimensionful the framework can say to
one question: is the conversion that turns a count into a dissipation rate the
same one that turns a count into a curvature?  And it named the missing input —
`Weight.lean`'s table does not list `λ`.

This file supplies it.  **It closes half the question and the other half is worth
stating precisely rather than glossing.**

## `λ` is weight zero

Two computations agree.  As a fractional rate, `λ = −d(ln ε)/dt` with `ln ε = −σ`
of weight one over a `t` of weight one: the ratio is invariant.  And inside
`Response.lean`'s own reading, `FactorsThroughCount D N κ` makes `D` carry the
weight of `κ` against a weight-zero count `N`, so `dD/dt` has that weight over
weight one — and equals `κρ`.  Both give **weight zero**.

## Which kills one branch outright

`unit_conversion_gives_invariant_rate`: a weight-one conversion against a
weight-minus-one density gives an invariant rate.  `gauge_conversion_moves`: a
weight-zero one does not — it moves under rescaling.  So

> **the scanning conversion is not a gauge coupling.**

That was a live possibility: `Response.lean` reduces the scanning hypothesis to
factorisation through `Running.resolvedCount`, and `Running`'s `κ` is the gauge
one, weight zero.  The weights forbid it.  And `Weight.lean`'s table lists
exactly one weight-one coefficient, `Δ`, so the scanning conversion is `Δ` times
a pure number: **the second relation exists.**

## And how far that gets — not all the way, and the gap is exact

`residual_factor_is_determined_not_predicted`: with the factor free, three
measurements — `G`, `ρ`, `λ` — against two unknowns — `Δ` and the factor — leave
nothing over.  The factor is *determined*, not predicted, and no number is
foretold.

`prediction_at_unit_factor`: at factor one it lands.  `Δρ = −λ/6`, read from a
cosmological rate and the spectrum's density with no reference to gravity, and
then the gravitational coupling follows.

> So the question is no longer "is it the same conversion" but **"is the
> proportionality one?"** — which is smaller, and is now a question about two
> definitions rather than about two constants.

## What would settle it, stated at the level of the types

`Index.IndexResponse (Δ ν σ) : lap σ = Δ·ν` is **ring-valued**: the Laplacian of
the log-scale equals the coefficient times a count.  `Response.FactorsThroughCount
D N κ : ∀ t t', D t − D t' = κ(N t − N t')` is **real-valued**: the increment of a
response equals the coefficient times the increment of a count.

Same shape, different types, and the factor is one exactly when `D` is `lap σ`
read along the drift.  That is one identification, it is now the only thing
between the framework and a cross-domain prediction, and it is **not made here**
— the two objects do not currently live in the same type, so making it requires a
bridge and not an assertion.
-/
import SCD.Overdetermination

namespace SCD.RateWeight

open SCD


/-- **A weight-one conversion gives an invariant rate.**

`κ ↦ cκ` and `ρ ↦ ρ/c`, so `λ = κρ` does not move.  This is
`Weight.product_invariant` for the pair that matters here. -/
theorem unit_conversion_gives_invariant_rate (κ rho c : ℝ) (hc : c ≠ 0) :
    (c * κ) * (rho / c) = κ * rho := by
  field_simp

/-- **A gauge conversion does not.**

A weight-zero `κ` against a weight-minus-one `ρ` gives a rate of weight minus
one, which moves under rescaling.  So if `λ` is weight zero — and it is, being
`−d(ln ε)/dt` with `ln ε = −σ` of weight one over a `t` of weight one — then the
scanning conversion **cannot be a gauge coupling.** -/
theorem gauge_conversion_moves (κ rho : ℝ) (hκ : κ ≠ 0) (hrho : rho ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ κ * (rho / c) ≠ κ * rho := by
  refine ⟨2, by norm_num, ?_⟩
  intro h
  have hz : κ * rho = 0 := by
    field_simp at h
    linarith
  rcases mul_eq_zero.mp hz with h' | h'
  · exact hκ h'
  · exact hrho h'

/-- **So the conversion is weight one, and the development has exactly one such
coefficient.**

`Weight.lean`'s table lists `Δ` as the only weight-one quantity among the
couplings; gauge couplings and `κ_run` are weight zero.  So the scanning
conversion is `Δ` times a pure number — the second relation **exists**. -/
def ProportionalTo (κs Δ c : ℝ) : Prop := κs = c * (-6 * Δ)

/-- **But proportionality is all the weights give.**

With the residual factor free, three measurements — `G`, `ρ`, `λ` — against two
unknowns — `Δ` and `c` — leave nothing over: `c` is determined and nothing is
predicted.  The prediction lands exactly when `c = 1`. -/
theorem residual_factor_is_determined_not_predicted
    {Δ rho lam c : ℝ} (hΔ : Δ ≠ 0) (hrho : rho ≠ 0)
    (hprop : ProportionalTo (lam / rho) Δ c) : c = lam / (rho * (-6 * Δ)) := by
  rw [ProportionalTo] at hprop
  field_simp at hprop ⊢
  linarith

/-- **And with `c = 1` it does land.**

The framework's one free number, read off a cosmological rate and the mass
spectrum's density, with no reference to gravity — and then the gravitational
coupling follows. -/
theorem prediction_at_unit_factor {Δ rho lam : ℝ} (hrho : rho ≠ 0)
    (hprop : ProportionalTo (lam / rho) Δ 1) : Δ * rho = -lam / 6 := by
  rw [ProportionalTo, one_mul] at hprop
  field_simp at hprop ⊢
  linarith


end SCD.RateWeight
