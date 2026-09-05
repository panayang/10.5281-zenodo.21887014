/-
# The directional scalar curvature does not exist, and what a scale wave is

Two tasks.  The first was to do `RscE_eq` for a **directional** scale — §V.aw's
one remaining obstruction.  It turns out the target is not a hard computation but
an **absent object**, and saying why is worth more than the computation would
have been.

## I.  Why there is no directional `RscE_eq`

`Conformal.RscBare`'s docstring states the design: *the true scalar curvature of
`g` is `e^{−2σ}` times this; we keep **the** conformal factor explicit so that no
invertibility hypothesis is ever needed.*  Singular — one factor.

With a scale per direction the metric is `met η w`, so the scalar curvature is
`dirTrace η w Ric = ∑_b η_b w_b⁻¹ R_bb`.  `dirTrace_isotropic` shows the factor
comes out when all `w_b` agree, and `dirTrace_factors_iff` shows that is the only
case: if `∑_b η_b w_b⁻¹ R_b = c⁻¹ ∑_b η_b R_b` for every `R`, then `w_b = c` for
every `b`.

> **There is no "bare" scalar curvature off the isotropic locus, because there is
> no single conformal factor to keep explicit.**

And that is not a gap in `EtaTrace.lean` — it is a property of A6′.  The law reads
`e^{2σ}R = κρ`, and `e^{2σ}` is **one** factor.  **A6′'s form presupposes an
isotropic scale**, and A4′ provides a directional one.

Confirmed by inspection: `Index.IndexResponse` takes `σ : A`, a scalar, and
nothing in the development states a source law for a `DirField`.  That absence is
not an oversight.

## So §V.aw's obstruction changes character

The bridge is not missing a **span** — a computation someone could do — it is
missing a **pier**.  The anisotropic sector has a curvature and no law to equate
it to, and the law it would need cannot have A6′'s shape.  That is a better
description of the disconnect than "one obstruction remains", and it means the
work is to write a source law for a directional scale, not to grind out a tensor
identity.

## II.  What a scale wave is

§V.aw showed the source law is hyperbolic with null characteristics.  So ask what
propagates.

**`σ` is the unit of measure**, and `Light.michelson_morley_null` says an
interferometer compares rod lengths against light times while the scale sets
both, so it **cancels — for every scale pattern, at any precision**.  So:

> **No interferometer can see a scale wave.  It is not a strain.**

That is not a weakness argued around; it is a theorem the development already
had, and it disposes of the obvious reading of "scale wave" before it is made.

**What does change is content.**  `Weight.lean` gives counts weight zero: a count
does not rescale with the wave, so when `σ` moves, the resolved set genuinely
moves with it.  `emerges_between` says exactly which structures cross:
`{k | t < μ k ≤ t'}`.

And `resolved_eq_iff_no_threshold_between` is the sharp form:

> **A scale wave has no continuous observable.  It acts only where it crosses a
> threshold, so its effect is quantised by the threshold spectrum.**

A wave of half an amplitude does not produce half an effect; it produces none, if
no threshold lies in the interval.  That is unlike every classical wave and it is
forced by what `Emergence.resolved` is.

**So a scale wave is a wave of emergence** — a null front across which structures
come into and go out of resolution — rather than a disturbance of geometry that
something rigid could register.

## III.  And it makes the autonomy question unavoidable

`Attraction.lean` leaves the source `ν` as a **threshold count**, and
`Emergence.resolved` makes the count a function of `σ`.  With `□σ = Δ·ν` that is

        □σ = Δ·ν(σ) ,

an **autonomous** equation: the field sources itself through what it resolves.
This file does not write that law — nothing here proves `ν` must be evaluated at
the local `σ` — but the wave reading makes the question sharper than it was, since
a propagating `σ` carries its own source along with it.

## Limits, stated

`Emergence.resolved` takes `μ` as **free data**, and §V.x records that nothing
connects `μ` to a measurement.  So "observable" here means *the resolved set
changes*, not *instrument X registers it*.  The quantisation result inherits that
scope: it says the effect is carried by the threshold spectrum, and the framework
still does not say what the threshold spectrum is.
-/
import SCD.Hyperbolic
import SCD.Emergence

namespace SCD.Directional

open SCD ScaleAlgebra Finset

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]


/-- The metric trace of a diagonal tensor against `met η w`.

`g^{bb} = η_b w_b⁻¹`, since `η_b² = 1`. -/
def dirTrace (η : Fin n → A) (w : Fin n → Aˣ) (R : Fin n → A) : A :=
  ∑ b, η b * (((w b)⁻¹ : Aˣ) : A) * R b

omit [ScaleAlgebra n A] in
/-- **On the isotropic locus the conformal factor comes out.** -/
theorem dirTrace_isotropic (η : Fin n → A) (w : Aˣ) (R : Fin n → A) :
    dirTrace η (fun _ => w) R = ((w⁻¹ : Aˣ) : A) * ∑ b, η b * R b := by
  simp only [dirTrace, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

omit [ScaleAlgebra n A] in
/-- **And only there.** -/
theorem dirTrace_factors_iff (η : Fin n → A) (hη : ∀ a, η a * η a = 1)
    (w : Fin n → Aˣ) (c : Aˣ) :
    (∀ R : Fin n → A, dirTrace η w R = ((c⁻¹ : Aˣ) : A) * ∑ b, η b * R b)
      ↔ ∀ b, (((w b)⁻¹ : Aˣ) : A) = ((c⁻¹ : Aˣ) : A) := by
  constructor
  · intro h b
    have hb := h (fun x => if x = b then 1 else 0)
    simp only [dirTrace, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hb
    linear_combination (η b) * hb
      + ((((c⁻¹ : Aˣ) : A)) - (((w b)⁻¹ : Aˣ) : A)) * hη b
  · intro h R
    simp only [dirTrace, h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring

/-! ## What a scale wave changes -/

/-- **Exactly the structures whose thresholds lie in the interval come into
resolution.** -/
theorem emerges_between (μ : ℕ → ℝ) (t t' : ℝ) :
    Emergence.resolved μ t' \ Emergence.resolved μ t = {k | t < μ k ∧ μ k ≤ t'} := by
  ext k
  simp only [Set.mem_sdiff, Emergence.mem_resolved, Set.mem_setOf_eq, not_le]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **And a wave that returns leaves nothing behind.** -/
theorem round_trip_resolves_nothing (μ : ℕ → ℝ) (t : ℝ) :
    Emergence.resolved μ t \ Emergence.resolved μ t = ∅ := by
  simp only [Set.sdiff_self]

/-- **A scale wave has no continuous effect: it acts only by crossing a
threshold.**

Two scale values resolve the same content exactly when no threshold lies
between them.  So the wave's observable is **quantised by the threshold
spectrum** — it is not a strain that grows smoothly with amplitude. -/
theorem resolved_eq_iff_no_threshold_between (μ : ℕ → ℝ) (t t' : ℝ) (h : t ≤ t') :
    Emergence.resolved μ t = Emergence.resolved μ t' ↔ ∀ k, ¬ (t < μ k ∧ μ k ≤ t') := by
  constructor
  · intro heq k ⟨h1, h2⟩
    have hk : k ∈ Emergence.resolved μ t' := h2
    rw [← heq] at hk
    exact absurd (hk : μ k ≤ t) (not_le.mpr h1)
  · intro hno
    ext k
    simp only [Emergence.mem_resolved]
    exact ⟨fun hk => le_trans hk h, fun hk => by
      by_contra hc
      exact hno k ⟨not_le.mp hc, hk⟩⟩

/-- **And the count is what changes.**  A count carries weight zero
(`Weight.lean`), so it does not rescale with the wave — it genuinely differs. -/
theorem content_grows_along_the_wave (μ : ℕ → ℝ) (t t' : ℝ) (h : t ≤ t') :
    Emergence.resolved μ t ⊆ Emergence.resolved μ t' :=
  Emergence.resolved_mono μ h


end SCD.Directional
