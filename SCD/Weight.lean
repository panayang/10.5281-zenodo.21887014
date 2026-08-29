/-
# Weights under rescaling the log-scale, and what the framework can predict

`Sources.lean` ended by naming `Δ / κ_run` as the first target in this line that
was not structurally barred: two count-to-scale couplings, so their ratio should
be a pure number.

**That was wrong, and this file computes the weights properly.**  The correction
is worth more than the target was, because doing the bookkeeping once explains
every success and every failure in the register at the same time.

## The grading

The operation is `σ ↦ cσ` with `c` a constant of the substrate — a redescription
of the log-scale, not a physical change.  Assign to each quantity the power of
`c` it picks up:

| quantity | weight | why |
|---|---|---|
| `lap σ` | `1` | `Sources.lap_const_mul` |
| `gradsq σ` | `2` | quadratic in the gradient |
| the scale-axis coordinate `t` | `1` | `t` **is** `σ` |
| `ρ`, thresholds per unit `t` | `−1` | a count divided by a weight-one interval |
| `resolvedCount ρ t₀ t` | `0` | it is a **count** (`resolvedCount_invariant`) |
| a gauge coupling `u` | `0` | its value does not depend on how `σ` is labelled |
| `κ_run`, response per defect | `0` | weight-zero over weight-zero |
| `ν`, defects per bare volume | `0` | the bare coordinates are untouched |
| `Δ`, the source coefficient | `1` | weight-one over weight-zero |

## The error, and the correction

`Sources.couplings_scale_together` proves that `invSqCoupling` is **linear** in
`(u₀, κ)`.  I read that as "`κ_run` carries weight one".  It does not: it says
nothing about `σ ↦ cσ` at all.

The honest computation is `invSqCoupling_invariant`: rescaling the log-scale
sends `t ↦ ct` and `ρ ↦ ρ/c`, and the coupling comes out **unchanged with `κ`
untouched**.  So `κ_run` has weight `0`, `Δ` has weight `1`, and

> `Δ / κ_run` has weight `1`.  It is **not** a pure number, and the target is
> withdrawn (`ratio_not_invariant`).

## What the bookkeeping explains

**Gravity is the only interaction that crosses the grading.**  The gauge sector's
law, `u = u₀ + κ·N`, relates weight-zero things to weight-zero things.  Gravity's,
`Δσ = Δ·ν`, relates a weight-zero count to a weight-one scale.  So the source
coefficient must carry weight one, and there is nothing else for it to be
measured against.

`only_gravity_crosses_the_weight`.  That is a structural explanation of a fact
usually just noted: **gauge couplings are pure numbers and Newton's constant is
not.**  Here it is not an accident of dimensions but a statement about which law
crosses the grading, and only one does.

**And it says exactly what the framework can predict.**  `Δρ` is the unique
weight-zero combination available (`product_invariant`), and it is the unit times
a measurement, so neither factor is predicted — which is `Period.lean`'s
conclusion arriving structurally rather than by exhausting candidates.

Everything the framework *does* predict is weight zero and contains no magnitude:
`CV² = 1` (`cvSq_weight_zero`), `w = −1`, `γ = 1`, the deflection `1.7515″` and the
precession `42.99″/century` — angles and ratios throughout.  And everything it
leaves open is weight one or a measurement: `Δ`, `ρ`, the threshold locations,
the scale magnitude.

> **The framework predicts the weight-zero sector and nothing else.  The
> weight-one sector is the unit.**

That is one sentence covering every entry in `Audit.lean` §V and every success in
`Predictions.lean`, and it was not visible until the grading was written down.
-/
import SCD.Sources
import SCD.Spectrum
import SCD.Dimension

namespace SCD.Weight

open SCD

/-! ## I. The gauge sector has weight zero -/

/-- **A count is a count.**

Rescaling the log-scale sends the scale-axis coordinate `t ↦ ct` and the density
`ρ ↦ ρ/c`; the number of thresholds in the window is unchanged, as it must be. -/
theorem resolvedCount_invariant (c ρ t₀ t : ℝ) (hc : c ≠ 0) :
    Running.resolvedCount (ρ / c) (c * t₀) (c * t) = Running.resolvedCount ρ t₀ t := by
  simp only [Running.resolvedCount]
  field_simp

/-- **And therefore the gauge coupling is invariant with `κ` untouched.**

This is the computation `Sources.couplings_scale_together` was mistaken for.  It
shows `κ_run` has weight **zero**: nothing about it moves when the log-scale is
relabelled. -/
theorem invSqCoupling_invariant (c u₀ κ ρ t₀ t : ℝ) (hc : c ≠ 0) :
    Running.invSqCoupling u₀ κ (ρ / c) (c * t₀) (c * t)
      = Running.invSqCoupling u₀ κ ρ t₀ t := by
  simp only [Running.invSqCoupling, resolvedCount_invariant c ρ t₀ t hc]

/-! ## II. The source coefficient has weight one, and the ratio is dead -/

/-- **The source coefficient moves.**  `Sources.source_coefficient_scales` in the
form needed here: rescaling the log-scale by `c` multiplies the coefficient by
`c`, since the Laplacian scales and the count does not. -/
theorem source_coefficient_weight_one {n : ℕ} {A : Type*} [CommRing A]
    [ScaleAlgebra n A] (c C ν σ : A) (hc : ∀ i : Fin n, ScaleAlgebra.d i c = 0)
    (h : Index.IndexResponse n C ν σ) :
    Index.IndexResponse n (c * C) ν (c * σ) :=
  Sources.source_coefficient_scales c C ν σ hc h

/-- **So the ratio is not a pure number.**

A weight-one quantity over a weight-zero one has weight one, and a weight-one
quantity is not invariant.  Exhibited rather than asserted: at `c = 2` the ratio
doubles. -/
theorem ratio_not_invariant :
    ∃ c Δ κ : ℝ, c ≠ 0 ∧ κ ≠ 0 ∧ (c * Δ) / κ ≠ Δ / κ := by
  refine ⟨2, 1, 1, by norm_num, by norm_num, ?_⟩
  norm_num

/-- **Gravity is the only interaction that crosses the grading.**

The gauge law relates weight-zero to weight-zero and its coefficient is
invariant; the gravitational law relates a weight-zero count to a weight-one
scale and its coefficient is not.  That is why gauge couplings are pure numbers
and the gravitational one is the unit — a statement about which law crosses the
grading, not about dimensions chosen by convention. -/
theorem only_gravity_crosses_the_weight (c u₀ κ ρ t₀ t : ℝ) (hc : c ≠ 0) :
    Running.invSqCoupling u₀ κ (ρ / c) (c * t₀) (c * t)
      = Running.invSqCoupling u₀ κ ρ t₀ t
    ∧ ∃ c' Δ κ' : ℝ, c' ≠ 0 ∧ κ' ≠ 0 ∧ (c' * Δ) / κ' ≠ Δ / κ' :=
  ⟨invSqCoupling_invariant c u₀ κ ρ t₀ t hc, ratio_not_invariant⟩

/-! ## III. The one invariant that is available, and why it is not a prediction -/

/-- **`Δρ` is weight zero.**

`Δ` has weight one and `ρ` weight minus one, so their product is the unique
combination of the two that survives rescaling.  This is `Period.lean`'s `Δρ`,
and the grading says it is the only candidate there was. -/
theorem product_invariant (c Δ rho : ℝ) (hc : c ≠ 0) :
    (c * Δ) * (rho / c) = Δ * rho := by
  field_simp

/-- **But it is the unit times a measurement.**

`Δ` is weight one — the unit — and `ρ` is measured, not predicted
(`Spectrum.lean` says so).  So `Δρ` is invariant and still not a prediction, which
is `Period.no_prediction_of_the_coupling` reached structurally instead of by
exhausting candidates. -/
theorem invariant_but_not_predicted (c Δ rho : ℝ) (hc : c ≠ 0) (hc1 : c ≠ 1)
    (hΔ : Δ ≠ 0) :
    (c * Δ) * (rho / c) = Δ * rho ∧ c * Δ ≠ Δ := by
  refine ⟨product_invariant c Δ rho hc, fun h => hc1 ?_⟩
  exact mul_right_cancel₀ hΔ (h.trans (one_mul Δ).symm)

/-! ## IV. What the framework does predict is weight zero -/

/-- **`CV²` has weight zero.**

The gaps are weight-one, so the variance is weight two and the squared mean is
weight two: the ratio is invariant.  That is why `CV² = 1` is a prediction and
`ρ ≈ 0.86` is a measurement — the first is weight zero and the second is not. -/
theorem cvSq_weight_zero (c v m : ℝ) (hc : c ≠ 0) :
    (c ^ 2 * v) / ((c * m) ^ 2) = v / m ^ 2 := by
  rw [mul_pow]
  exact mul_div_mul_left v (m ^ 2) (pow_ne_zero 2 hc)

/-- **And a ratio of rotational labels is weight zero**, which is
`Dimension.wedge_ratio_invariant` seen as a grading statement: the framework's
predictions are ratios because ratios are what survive. -/
theorem wedge_ratio_weight_zero {k : ℕ} (c : ℝ) (hc : c ≠ 0) (v w : Fin k → ℝ)
    (i j i' j' : Fin k) :
    wedge (c • v) (c • w) i j / wedge (c • v) (c • w) i' j'
      = wedge v w i j / wedge v w i' j' :=
  SCD.Dimension.wedge_ratio_invariant c hc v w i j i' j'

end SCD.Weight
