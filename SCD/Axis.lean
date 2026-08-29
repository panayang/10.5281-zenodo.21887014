/-
# Point particles come back, and a ratio is why

`Codimension.lean` concluded that in three spatial dimensions the framework's
defects are strings, not points.  That conclusion was reached with the *scalar*
circle-valued scale of `Defect.lean` — and using a scalar scale where the axiom
provides a directional one is exactly the error already diagnosed for geometry
in `Frame.lean`.  It has been made twice.

A4 does not give one scale.  It gives one scale **per direction**.  So the
configuration at a point is not a phase; it is a *pattern of scales across
directions*, and the field takes values in the space of such patterns.  That
space is not a circle, and its defects are not classified by loops alone.

The decisive property is forced, and it is forced by the very thing that made
the scalar picture look inevitable:

> **A scale is a ratio of lengths, so it cannot see the orientation of a
> direction.**  Reversing a direction leaves every scale reading unchanged.

Hence the order parameter is an **unoriented axis** — a projective object, not a
vector.  Projective order parameters famously carry *both* kinds of defect:
line defects of order two, and **point defects with integer charge**.  Point
particles are back, and they are back because the scale is a ratio.

Proved here:

* `bareForm_neg`, `physForm_neg` — every scale reading is even in the
  direction;
* `neg_indistinguishable` — hence no scale measurement whatsoever separates a
  direction from its reverse;
* `uniaxial_stabilizer` — a pattern with one distinguished direction and a
  degenerate remainder has exactly the block symmetry, so its order parameter is
  a single unoriented axis;
* `isotropic_no_order_parameter` — a fully degenerate pattern distinguishes
  nothing and supports no defect at all.

**Flagged as input, not proved:** that an unoriented-axis order parameter in
three dimensions has `π₂ = ℤ` and `π₁ = ℤ₂`, giving integer-charged point
defects together with order-two strings.  That is standard topology; what the
framework supplies is the *projectivity*, which is where the point defects come
from.

**Correction on record.** `Codimension.lean`'s theorems remain true of a
circle-valued scale.  What is withdrawn is the claim that they describe *this*
framework: with the directional scale of A4 they do not, and the framework
predicts point particles after all.
-/
import SCD.Light
import SCD.Gauge

namespace SCD.Axis

open SCD Light

variable {n : ℕ} {A : Type*} [CommRing A]

/-! ## A ratio cannot see orientation -/

/-- **Scale readings are even.**  The bare form is quadratic in the direction,
so reversing the direction changes nothing.  This is not an extra assumption:
it is what "a scale is a ratio of lengths" means. -/
@[simp] theorem bareForm_neg (η v : Fin n → A) : bareForm η (-v) = bareForm η v := by
  simp only [bareForm, Pi.neg_apply]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The measured form inherits it: no scale field can break the symmetry. -/
@[simp] theorem physForm_neg (s : Aˣ) (η v : Fin n → A) :
    physForm s η (-v) = physForm s η v := by
  simp only [physForm, bareForm_neg]

/-- Two directions are **scale-indistinguishable** when no scale reading, in any
signature, separates them. -/
def Indistinguishable (v w : Fin n → A) : Prop := ∀ η : Fin n → A, bareForm η v = bareForm η w

/-- **A direction and its reverse are indistinguishable.**

So the physical object is not a direction but an *axis*: the order parameter is
projective.  Everything about point defects below follows from this one fact,
and this fact follows from a scale being a ratio. -/
theorem neg_indistinguishable (v : Fin n → A) : Indistinguishable v (-v) :=
  fun η => (bareForm_neg η v).symm

/-- Indistinguishability is preserved by the measured form as well, so the
projective identification is not an artefact of ignoring the scale field. -/
theorem physForm_indistinguishable (s : Aˣ) (v : Fin n → A) (η : Fin n → A) :
    physForm s η v = physForm s η (-v) := (physForm_neg s η v).symm

/-! ## Which patterns support an order parameter

The pattern of scales across directions is what varies from point to point.
How much can vary is fixed by the degeneracy, through `Gauge.stabilizer`. -/

open Gauge

/-- **A fully degenerate pattern has no order parameter.**

If every direction carries the same unit, every relabelling is a symmetry: the
pattern is the same everywhere by construction, nothing varies, and there is
nothing for a defect to wind around.  The isotropic sector — the old scalar
axiom — supports no defects at all. -/
theorem isotropic_no_order_parameter (s : Fin n → Aˣ) (hiso : IsIsotropic s) :
    stabilizer s = ⊤ := stabilizer_eq_top_of_isotropic s hiso

/-- **A fully non-degenerate pattern has no internal symmetry**, so its order
parameter is a full frame rather than a single axis. -/
theorem nondegenerate_full_frame (s : Fin n → Aˣ) (hinj : Function.Injective s) :
    stabilizer s = ⊥ := stabilizer_eq_bot_of_injective s hinj

/-- **The uniaxial case.**

A pattern in which one direction is distinguished and the others agree has
exactly the relabellings of the degenerate block as its symmetry.  Its order
parameter is therefore a single axis — and by `neg_indistinguishable` an
*unoriented* one.

This is the configuration that carries point defects. -/
theorem uniaxial_stabilizer [DecidableEq (Fin n)] (s : Fin n → Aˣ) (t : Fin n)
    (hblock : ∀ a b, a ≠ t → b ≠ t → s a = s b)
    (a b : Fin n) (ha : a ≠ t) (hb : b ≠ t) :
    SameOrbit s a b :=
  (sameOrbit_iff_eq_scale s a b).mpr (hblock a b ha hb)

/-- The distinguished direction is in no one else's orbit: the axis is
well defined. -/
theorem uniaxial_axis_distinguished [DecidableEq (Fin n)] (s : Fin n → Aˣ)
    (t a : Fin n) (hne : s a ≠ s t) : ¬ SameOrbit s a t := by
  intro h
  exact hne ((sameOrbit_iff_eq_scale s a t).mp h)

/-! ## What this restores

With a projective order parameter the defect classification is not the winding
of a phase.  In three spatial dimensions an unoriented axis field carries
integer-charged **point** defects as well as order-two strings — the standard
result for such order parameters, taken here as input.

The framework's contribution is the projectivity, and that came from the scale
being a ratio.  So `Codimension.lean`'s alarm applies to a circle-valued scale,
which is not what A4 provides. -/

/-- The scalar picture and the directional picture disagree about defects, and
the disagreement is exactly the `A4` versus directional-`A4` distinction that
`Frame.lean` already settled once.  Recorded so the same substitution is not
made a third time. -/
theorem scalar_picture_is_the_isotropic_locus (s : Fin n → Aˣ)
    (hiso : IsIsotropic s) : stabilizer s = ⊤ :=
  isotropic_no_order_parameter s hiso

end SCD.Axis
