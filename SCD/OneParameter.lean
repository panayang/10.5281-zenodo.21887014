/-
# Are the size and `Δρ` the same freedom?

The register's open items sort into three kinds: those that are free **by
construction** (A5 and the grading make the origin and the unit unobservable),
those that are the **same request** — a conversion from counting to scale — and a
few genuinely separate things.  The middle group had six members and the claim
that they are one was a reading.  This file tests two of them against each other.

## The decomposition

A uniform size is `ρ(t − t₀)`, and `affine_size_determined` says those two numbers
are all of it: evaluating at two points recovers both.

* `origin_is_a_fiducial_shift` and `uniform_size_one_observable` — the origin is
  **not an observable of the size**.  Changing it is reading the same size on a
  shifted axis, which is A5;
* so the size's only observable is its **slope**, which is `ρ`, of weight minus
  one;
* and `size_adds_no_freedom` is `Weight.product_invariant`: `ρ` pairs with the
  unit into `Δρ`, the unique weight-zero combination.

> **The size adds no freedom.**  Its slope is the `ρ` already counted and its
> origin is A5's.

## Which makes the uniform-density assumption something other than it looked

`Size.uniform_density_is_a_restriction` shows a size need not be affine, and a
non-affine size has its whole *shape* free.  So

> **uniform density is not an assumption standing beside `Δρ`.  It is the
> assumption that makes the size and `Δρ` one parameter.**

The register has carried it since the beginning as one of the assumed items,
without saying what it buys.  What it buys is the collapse.

And the shape is not free either where it matters: `Spectrum.lean` **predicts**
`CV² = 1` for it.  So the size's content is one measured number and one
prediction, and neither is a new input.

## What this does not collapse

Three of the six, not six.

* `Δρ`, the size, and uniform density are one item — that is what is proved here,
  and the cosmological rate follows since it is the size's derivative;
* **G4's weight is not shown to be the same number.**  `Valuation.lean` weighs
  *records* — sets of thresholds crossed — with a modular valuation, and nothing
  here relates that to a size on the scale axis.  They are the same *kind* of
  request; whether they are the same number is open;
* and **which label `ν` counts** is untouched: that is a question about the
  charge structure, not about a magnitude.

So the reading that the middle group is one item is **supported and not
established**.  Half of it is now a theorem and the rest is still a reading, and
the register should say which is which.
-/
import SCD.Valuation
import SCD.Weight

namespace SCD.OneParameter

open SCD


/-- **An affine size is pinned by its slope and its origin.**

Evaluating at two points recovers both, so a uniform size has exactly two
numbers in it and no more. -/
theorem affine_size_determined {ρ ρ' t₀ t₀' : ℝ} (hρ : ρ ≠ 0)
    (h : ∀ t : ℝ, ρ * (t - t₀) = ρ' * (t - t₀')) : ρ = ρ' ∧ t₀ = t₀' := by
  have h0 := h 0
  have h1 := h 1
  have hslope : ρ = ρ' := by nlinarith [h0, h1]
  refine ⟨hslope, ?_⟩
  rw [← hslope] at h0
  have : ρ * t₀ = ρ * t₀' := by linarith
  exact mul_left_cancel₀ hρ this

/-- **And the origin is exactly A5's fiducial shift.**

Moving the origin with the axis changes nothing: `t₀` is not an observable of the
size, it is the choice of where to start counting. -/
theorem origin_is_a_fiducial_shift (ρ t₀ c t : ℝ) :
    ρ * ((t + c) - (t₀ + c)) = ρ * (t - t₀) := by ring

/-- **So a uniform size contributes one number, and it is `ρ`.**

Two uniform sizes with the same slope differ only by where they start, hence by a
fiducial shift.  There is no second observable in a uniform size. -/
theorem uniform_size_one_observable {ρ t₀ t₀' : ℝ} :
    ∃ c : ℝ, ∀ t : ℝ, ρ * (t - t₀') = ρ * ((t + c) - t₀) := by
  refine ⟨t₀ - t₀', fun t => ?_⟩
  ring

/-- **And that number is the one already counted in `Δρ`.**

`Weight.product_invariant` says `Δρ` is the unique weight-zero combination of the
unit and the density.  The density is the uniform size's slope, so the size adds
**no new freedom**: its slope is the `ρ` already there, and its origin is A5's. -/
theorem size_adds_no_freedom (c Δ ρ : ℝ) (hc : c ≠ 0) :
    (c * Δ) * (ρ / c) = Δ * ρ :=
  Weight.product_invariant c Δ ρ hc


end SCD.OneParameter
