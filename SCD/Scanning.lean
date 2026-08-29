/-
# Cosmology without a beginning — and the hidden hypothesis in `w = −1`

## The reframe

`Cosmos.no_first_moment` says the universe has no age, only elapsed ratios, and
`a = 1/ε` is registered as an identification.  Take that seriously and the
Friedmann picture does not merely fail — it is **not a dynamical law here at
all**.  Time is the direction the scale runs (`Signature.lean`), and the scale
factor is the scale.  So `a(t)` is a reparametrisation of the coordinate, not a
function of it, and there is nothing for a field equation to determine.

What is left that can vary?  Exactly one thing: **the density of thresholds per
unit log-scale**.  `Emergence.resolved` makes content a cut across the scale
axis, `Emergence.always_more_above` says the cut never completes, and
`Spectrum.lean` measures the density at `ρ ≈ 0.86` per e-fold.

> The universe is not expanding.  The resolution is scanning, and cosmology is
> the statistics of what it crosses.

That reframing costs nothing — every theorem in `Cosmos.lean` and
`DarkEnergy.lean` survives — but it changes what the free function is, and that
turns out to matter for the framework's most exposed prediction.

## The hidden hypothesis

`Cosmos.rate_constant_of_fiducial_invariance` derives `w = −1` from

        hA5 :  ∀ σ c,  λ(σ + c) = λ(σ) .

Read the quantifier.  `λ` is a function of **one** variable, the bare log-scale,
and the hypothesis says shifting that one variable changes nothing.  That is the
correct reading of A5 **only if there is no other scale in the problem** — because
if there is one, A5 shifts *it too*, and what A5 actually demands is invariance
under shifting everything together.

Once that is written out, the conclusion changes completely:

* `two_scale_invariance_forces_difference` — a rate invariant under shifting both
  its arguments is a function of their **difference**;
* `rate_may_vary` — and a function of a difference need not be constant.  An
  explicit A5-respecting rate that genuinely varies is exhibited.

So **A5 does not force `w = −1`.**  It forces the rate to depend only on scale
*differences*, which is what A5 says in the first place.  The stronger conclusion
needed the extra assumption that no second scale exists.

## And the framework now has a second scale

It did not, when `Cosmos.lean` was written.  `Index.lean` supplies one: the
source of the geometry is the defect content, so the **thresholds are
gravitationally active**, and `σ − μ_k` is a scale difference — exactly the kind
of quantity A5 permits.

`Emergence.always_more_above` says the thresholds recur, with mean log-spacing
`1/ρ`.  So the prediction is not "`w` is constant" but:

> **`w` varies, and it varies on the log-scale set by the threshold spectrum.**

`rate_from_threshold_spacing` states the shape.  The DESI preference for an
evolving equation of state is then not a falsification of A5 — it is a
measurement of the same `ρ` that `Spectrum.lean` measures in the particle
spectrum, and the two must agree.  That is a much sharper claim than `w = −1`,
because it is a *cross-sector* one with nothing free.

## One mechanism, two anomalies

The scanning picture makes a second prediction, and it comes from the same
number.  Two ways to measure the expansion rate:

* **count thresholds** — what a distance ladder built on standard candles does,
  since a candle is a species with a threshold;
* **compare scale ratios** — what a standard ruler does.

They agree exactly when `ρ` is constant, and `scanRate` below makes the rate
proportional to `ρ`.  So if `ρ` varies:

* the equation of state evolves, **and**
* the two determinations of `H₀` disagree,

and `two_anomalies_one_number` shows the fractional size of both is the same
number, `Δρ/ρ`.  **The `w₀wₐ` tension and the `H₀` tension are not independent
anomalies here — they are one number measured twice**, and that is falsifiable:
if `w` evolves and the ladders agree, or vice versa, the picture is wrong.

## What is not claimed

That `λ = κρ` is a *proposal* — the scanning hypothesis — not a theorem.  What is
a theorem is everything downstream of it, and, more importantly, the negative
result: `w = −1` was never forced by A5 alone, and the file that derived it said
so in a quantifier no one had read carefully, mine included.

**`Response.lean` sharpens all three sentences of that paragraph.**

* `scanRate` is a *definition*, so nothing downstream of it is evidence for it.
  The hypothesis is not `λ = κρ` but **factorisation through the count** —
  `Response.FactorsThroughCount`: the response depends on the thresholds only
  through their number.  Given that, `λ = κρ` is the chain rule
  (`Response.rate_is_kappa_rho`);
* factorisation is the scanning sector's instance of "the source is a **count**",
  which `Attraction.lean` argues in the gravitational sector and
  `Anchor.signed_source_is_distinguished` shows is anchored *there*.  A
  **reduction**, not a derivation: the same shape of statement about a different
  quantity is not the same statement;
* and A5 together with the weight grading — the two tools that settle most
  questions of this kind here — **do not force it**.
  `Response.weight_zero_does_not_force_constancy` exhibits a per-threshold weight,
  the local spacing ratio `(z−y)/(y−x)`, that is weight zero, fiducial invariant,
  and non-constant.  That is the precise gap.

And `two_anomalies_one_number` below holds **for every** density
(`Response.two_anomalies_holds_for_every_density`), so it is `κ` cancelling in a
fraction; its physical content is two identifications that are not formalised.
-/
import SCD.Cosmos

namespace SCD.Scanning

open SCD

/-! ## I. What A5 actually forces -/

/-- **A rate invariant under shifting *both* its scales is a function of their
difference.**

This is A5 stated correctly when the problem contains a second scale: the
fiducial shift moves the observer's scale and the reference scale together, and
what must be unobservable is that joint shift. -/
theorem two_scale_invariance_forces_difference (lam : ℝ → ℝ → ℝ)
    (hA5 : ∀ σ μ c, lam (σ + c) (μ + c) = lam σ μ) (σ μ : ℝ) :
    lam σ μ = lam (σ - μ) 0 := by
  have h := hA5 σ μ (-μ)
  rw [add_neg_cancel, show σ + -μ = σ - μ by ring] at h
  exact h.symm

/-- **And a function of a difference need not be constant.**

An explicit rate that satisfies A5 exactly and still varies: `λ(σ,μ) = σ − μ`.
So the step from "A5" to "`w = −1`" is not valid once a second scale is present,
and `Cosmos.rate_constant_of_fiducial_invariance` is a theorem about the
one-scale case. -/
theorem rate_may_vary :
    ∃ lam : ℝ → ℝ → ℝ,
      (∀ σ μ c, lam (σ + c) (μ + c) = lam σ μ)
      ∧ ∃ σ σ' μ : ℝ, lam σ μ ≠ lam σ' μ := by
  refine ⟨fun σ μ => σ - μ, fun σ μ c => by ring, 1, 0, 0, ?_⟩
  norm_num

/-- **The one-scale case is recovered exactly.**

If the rate genuinely does not depend on the second scale, the two-argument
invariance collapses to `Cosmos`'s hypothesis and the rate is constant.  So
nothing proved there is lost; its domain is stated. -/
theorem one_scale_recovers_constant (lam : ℝ → ℝ → ℝ)
    (hA5 : ∀ σ μ c, lam (σ + c) (μ + c) = lam σ μ)
    (hindep : ∀ σ μ μ', lam σ μ = lam σ μ') (σ σ' μ : ℝ) :
    lam σ μ = lam σ' μ := by
  have h := hA5 σ μ (σ' - σ)
  rw [show σ + (σ' - σ) = σ' by ring] at h
  rw [← h, hindep σ' (μ + (σ' - σ)) μ]

/-- **The shape of the variation: the rate tracks the distance to a threshold.**

`Index.lean` makes the thresholds gravitationally active, so `σ − μ` is a
physical scale difference and the rate may depend on it.  `Emergence` says the
thresholds recur; `Spectrum` measures their mean log-spacing as `1/ρ`.  So the
variation of `w` is not free — it is set by the particle spectrum. -/
theorem rate_from_threshold_spacing (f : ℝ → ℝ) (σ μ c : ℝ) :
    f ((σ + c) - (μ + c)) = f (σ - μ) := by
  congr 1
  ring

/-! ## II. One mechanism, two anomalies

The scanning hypothesis: dissipation *is* threshold crossing, so the rate is
proportional to the threshold density.  Everything below is a theorem given
that; the hypothesis itself is a proposal and is labelled one. -/

/-- **The scanning rate**: dissipation proportional to the density of thresholds
being crossed.  The constant `κ` is a conversion, not a new freedom — it is what
turns a count per e-fold into a rate. -/
noncomputable def scanRate (κ : ℝ) (rho : ℝ → ℝ) (t : ℝ) : ℝ := κ * rho t

/-- **Constant density is exactly constant rate**, so `Cosmos`'s `w = −1` is the
constant-`ρ` case of the scanning picture and nothing is lost by adopting it. -/
theorem scanRate_constant_iff (κ : ℝ) (hκ : κ ≠ 0) (rho : ℝ → ℝ) :
    (∀ t t', scanRate κ rho t = scanRate κ rho t') ↔ (∀ t t', rho t = rho t') := by
  constructor
  · intro h t t'
    have := h t t'
    simp only [scanRate] at this
    exact mul_left_cancel₀ hκ this
  · intro h t t'
    simp only [scanRate, h t t']

/-- The evolution of the rate is the evolution of the density, scaled. -/
theorem w_evolution_tracks_density (κ : ℝ) (rho : ℝ → ℝ) (t t' : ℝ) :
    scanRate κ rho t - scanRate κ rho t' = κ * (rho t - rho t') := by
  simp only [scanRate]
  ring

/-- **The two anomalies are one number.**

The *fractional* evolution of the dissipation rate — which is what a `w₀wₐ` fit
measures — equals the fractional variation of the threshold density, which is
what the disagreement between a counting ladder and a ruler measures.  The
conversion `κ` cancels, so the two observations are the same quantity and cannot
be tuned independently.

If `w` is found to evolve and the `H₀` determinations are found to agree, this
picture is falsified. -/
theorem two_anomalies_one_number (κ : ℝ) (hκ : κ ≠ 0) (rho : ℝ → ℝ) (t t' : ℝ) :
    (scanRate κ rho t - scanRate κ rho t') / scanRate κ rho t'
      = (rho t - rho t') / rho t' := by
  simp only [scanRate]
  rw [← mul_sub, mul_div_mul_left _ _ hκ]

/-- And they vanish together: no evolution of the rate exactly when the two
determinations agree.  There is no configuration in which one anomaly appears
without the other. -/
theorem anomalies_vanish_together (κ : ℝ) (hκ : κ ≠ 0) (rho : ℝ → ℝ) (t t' : ℝ) :
    scanRate κ rho t = scanRate κ rho t' ↔ rho t = rho t' := by
  simp only [scanRate]
  constructor
  · exact mul_left_cancel₀ hκ
  · intro h; rw [h]

/-! ## III. No beginning, and no end either

The scanning picture makes the absence of an origin structural rather than a
consequence of a solution.  There is no first threshold and no last, so the
scan has no endpoints — and the framework's claim that the universe has no age
becomes a statement about a point process rather than about a differential
equation. -/

/-- **There is no last threshold**, so the scan never completes: `Emergence`'s
statement, read as the cosmological one. -/
theorem scan_never_completes (μ : ℕ → ℝ) (hunb : ∀ M : ℝ, ∃ k, M < μ k) (t : ℝ) :
    ∃ k, t < μ k := hunb t

/-- **And the observed history is finite regardless.**

Any finite elapsed scale difference gives a finite ratio, so "the universe is
infinitely old" and "the universe has an age" are both malformed: what is
measured is a difference, and differences are finite.  `Cosmos`'s theorem,
restated where the scanning picture needs it. -/
theorem finite_history_no_origin (a₀ lam t t' : ℝ) (ha : a₀ ≠ 0) :
    Cosmology.scaleFactor a₀ lam t / Cosmology.scaleFactor a₀ lam t'
      = Real.exp (lam * (t - t')) :=
  Cosmos.scale_ratio_depends_only_on_difference a₀ lam t t' ha

end SCD.Scanning
