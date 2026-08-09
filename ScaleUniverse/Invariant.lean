/-
# The bookkeeping metric is not postulated either

The audit's first entry was the worst: A1 declares the Kronecker `δ` to be
"pure bookkeeping, carrying no physics", and then `Conformal.lean` uses it to
raise indices and to define the contraction that produces Ricci.  A flat metric
was being handed over for free and then doing real work.

`Foundation.lean` showed the scale/rotation split is not a choice.  The same
question can be put to `δ`: **is there anything canonical on the comparison
algebra that could serve as the bookkeeping form?**

There is, and it needs far less than a metric.  Suppose the algebra carries a
*trace* — one linear functional with `τ(xy) = τ(yx)`.  That is a much weaker
object than an inner product; it is canonical on any matrix algebra, and it is
the only thing needed:

* `form_symm` — `κ(x,y) := τ(xy)` is symmetric, from the trace property alone;
* `form_invariant` — `κ([z,x],y) + κ(x,[z,y]) = 0`, so the form is invariant
  under the very transports whose commutators are the curvature
  (`Connection.comm_covD`).  That invariance is exactly the job `δ` was doing;
* `form_ad_skew` — equivalently, every `ad z` is skew for `κ`, which is the
  infinitesimal statement that transport preserves the bookkeeping.

So the flat form is not an extra postulate.  It is `τ(xy)` for whatever trace
the algebra has, and its invariance — the one property `Conformal.lean` relies
on — is a theorem, not an assumption.

**What this does and does not achieve.**  Three separate inputs — a set of
directions, a flat metric `δ`, and a signature `η` — are now down to one: a
comparison algebra with a trace.  The signature came out of dissipation
(`Signature.lean`), the split out of abelianization (`Foundation.lean`), and
the form out of the trace here.  The *dimension* is still whatever the algebra's
is, and that remains an input; compression is not derivation, and this file does
not pretend otherwise.
-/
import ScaleUniverse.Quantum
import Mathlib.Tactic.NoncommRing

namespace ScaleUniverse.Invariant

open ScaleUniverse Quantum

variable {M : Type*} [Ring M]

/-! ## A trace is all that is needed -/

/-- A **trace** on the comparison algebra: additive, and blind to the order of
a product.  This is strictly weaker than a metric — no positivity, no
non-degeneracy, no choice of basis — and it is canonical on matrix algebras. -/
structure Trace (M : Type*) [Ring M] where
  /-- The trace functional. -/
  τ : M → M
  map_add : ∀ x y, τ (x + y) = τ x + τ y
  /-- Blindness to order: the defining property. -/
  cyclic : ∀ x y, τ (x * y) = τ (y * x)

namespace Trace

variable (T : Trace M)

@[simp] theorem map_zero : T.τ 0 = 0 := by
  have h : T.τ (0 + 0) = T.τ 0 + T.τ 0 := T.map_add 0 0
  rw [add_zero] at h
  have h' : T.τ 0 + 0 = T.τ 0 + T.τ 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

/-- Additivity packaged so that `map_sub` is available. -/
def hom : M →+ M where
  toFun := T.τ
  map_zero' := T.map_zero
  map_add' := T.map_add

@[simp] theorem map_sub (x y : M) : T.τ (x - y) = T.τ x - T.τ y :=
  _root_.map_sub T.hom x y

/-- The **bookkeeping form** induced by a trace.  This is what `δ` was. -/
def form (x y : M) : M := T.τ (x * y)

/-- **The form is symmetric**, from the trace property alone. -/
theorem form_symm (x y : M) : T.form x y = T.form y x := T.cyclic x y

theorem form_add_left (x y z : M) : T.form (x + y) z = T.form x z + T.form y z := by
  simp only [form, add_mul]
  exact T.map_add _ _

theorem form_add_right (x y z : M) : T.form x (y + z) = T.form x y + T.form x z := by
  simp only [form, mul_add]
  exact T.map_add _ _

/-! ## Invariance — the property `δ` was actually supplying -/

/-- **The form is invariant under transport.**

`κ([z,x], y) + κ(x, [z,y]) = 0`.

The transports whose commutators *are* the curvature preserve this form.  That
is precisely the role the postulated flat metric was playing in
`Conformal.lean`, and here it is a theorem about any trace. -/
theorem form_invariant (z x y : M) :
    T.form (ad z x) y + T.form x (ad z y) = 0 := by
  simp only [form, ad, sub_mul, mul_sub]
  rw [T.map_sub, T.map_sub]
  have hA : T.τ (z * x * y) = T.τ (x * (y * z)) := by
    rw [mul_assoc z x y]
    have hc := T.cyclic z (x * y)
    rw [hc, mul_assoc]
  have hB : T.τ (x * (z * y)) = T.τ (x * z * y) := by rw [mul_assoc]
  rw [hA, hB]
  abel

/-- Equivalently: every transport generator is **skew** for the form.  This is
the infinitesimal statement that transport preserves the bookkeeping. -/
theorem form_ad_skew (z x y : M) :
    T.form (ad z x) y = -T.form x (ad z y) := by
  have h := T.form_invariant z x y
  rw [← sub_eq_zero, sub_neg_eq_add]
  exact h

/-- The form of a commutator against the same element is antisymmetric, so
nothing new is smuggled in by using the form to contract indices. -/
theorem form_commutator_self (z x : M) :
    T.form (ad z x) x + T.form x (ad z x) = 0 :=
  T.form_invariant z x x

end Trace

end ScaleUniverse.Invariant
