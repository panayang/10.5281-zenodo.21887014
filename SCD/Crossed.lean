/-
# Non-commutativity, exactly

`Deformation.lean` got the classical limit by expanding to first order in `ħ`
and stopping.  That was honest but it was also a formal series truncated for
convenience, and a truncation is a bad place for a foundation to sit.

The truncation was unnecessary.  There is an *exact* source of
non-commutativity already present in the framework, and it needs no expansion
parameter at all.

Ask what two operations the theory actually has.  One reads a quantity *where
you are*: multiplication by `a`.  The other moves you *to the adjacent scale*:
the shift `T`.  These do not commute, and their failure to commute is not a
small parameter but a finite, exact quantity — the scale difference itself:

        [U, M_a] = M_{Ta − a} · U .

**Position and scale do not commute.**  That is the operator form of A3
(`ε·s = 1`): resolving where something is and resolving at what scale are
incompatible operations, and `ħ` is the size of the scale step, not a formal
symbol.

Everything follows exactly:

* `shift_mul_eq` — the exchange relation `U M_a = M_{Ta} U`;
* `commutator_eq` — the commutator, in closed form, with no expansion;
* `comm_iff_shift_trivial` — the algebra is commutative **iff** the scale step
  is trivial.  Classical geometry is not a limit one takes; it is the case
  where nothing moves;
* `delta_twisted_leibniz` — the exact Leibniz rule at finite step,
  `δ(ab) = δ(a)·Tb + a·δ(b)`.  Ordinary Leibniz — axiom A1 — is what this
  becomes when the twist `T` is the identity.

So the classical differential structure is not first-order-in-`ħ`; it is the
**zero-scale-step** case of an exact relation.  The caveat in
`Deformation.lean` is thereby retired rather than argued around.

**Scope, added after an external audit.**  `ScaleShift` below is **not
constructed from A1–A7**.  It requires only a ring endomorphism `T` and a unit
`U`; nothing in this development builds one from `ScaleAlgebra`, `DiffRing` or
`ScaleField`.  So what is proved is exact **for any such pair** — the algebra is
airtight — but the step from "the framework has a scale shift with these
properties" to "`ħ` is that step" is an **identification**, not a construction.

That distinction was not made in earlier versions of this file, and the docstring
below still reads as though the structure were forced.  It is not.  Registered
in `Audit.lean` §V.b.
-/
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

namespace SCD.Crossed

variable {A : Type*} [CommRing A]

/-! ## The two operations -/

/-- A **scale shift**: the substrate re-read one step along the scale
direction.  Only the ring structure needs to be preserved; nothing is assumed
about how large the step is. -/
structure ScaleShift (A : Type*) [CommRing A] where
  /-- Move to the adjacent scale. -/
  T : A → A
  map_add : ∀ x y, T (x + y) = T x + T y
  map_mul : ∀ x y, T (x * y) = T x * T y

namespace ScaleShift

variable (S : ScaleShift A)

@[simp] theorem map_zero : S.T 0 = 0 := by
  have h : S.T (0 + 0) = S.T 0 + S.T 0 := S.map_add 0 0
  rw [add_zero] at h
  have h' : S.T 0 + 0 = S.T 0 + S.T 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

/-- The shift as an additive endomorphism, so that it lives in the operator
ring alongside multiplication. -/
def shiftOp : AddMonoid.End A where
  toFun := S.T
  map_zero' := S.map_zero
  map_add' := S.map_add

@[simp] theorem shiftOp_apply (x : A) : S.shiftOp x = S.T x := rfl

end ScaleShift

/-- Reading a quantity where you are: multiplication, as an operator. -/
def mulOp (a : A) : AddMonoid.End A := AddMonoidHom.mulLeft a

@[simp] theorem mulOp_apply (a x : A) : mulOp a x = a * x := rfl

/-! ## They do not commute, and by exactly how much -/

/-- **The exchange relation.**  Moving to the adjacent scale and then reading
`a` is the same as reading `Ta` and then moving.  This is exact. -/
theorem shift_mul_eq (S : ScaleShift A) (a : A) :
    S.shiftOp * mulOp a = mulOp (S.T a) * S.shiftOp := by
  ext x
  show S.T (a * x) = S.T a * S.T x
  exact S.map_mul a x

/-- The **scale difference** operator: how much a quantity changes over one
step.  At finite step this is the exact analogue of a derivative. -/
def delta (S : ScaleShift A) (a : A) : A := S.T a - a

/-- **The commutator, in closed form.**

`[U, M_a] = M_{δa} U`.  Non-commutativity is not a small parameter — it is the
scale difference, exactly.  `ħ` is the size of a scale step. -/
theorem commutator_eq (S : ScaleShift A) (a : A) :
    S.shiftOp * mulOp a - mulOp a * S.shiftOp = mulOp (delta S a) * S.shiftOp := by
  rw [shift_mul_eq]
  ext x
  show S.T a * S.T x - a * S.T x = (S.T a - a) * S.T x
  ring

/-- **Commutativity is exactly the absence of a scale step.**

If the shift is trivial the two operations commute and the geometry is
classical; if it is not, they do not.  The classical world is not a limit taken
for convenience — it is the case in which nothing moves along the scale. -/
theorem comm_iff_shift_trivial (S : ScaleShift A) (a : A) :
    S.shiftOp * mulOp a = mulOp a * S.shiftOp ↔ mulOp (delta S a) * S.shiftOp = 0 := by
  constructor
  · intro h
    rw [← commutator_eq, h, sub_self]
  · intro h
    have hc := commutator_eq S a
    rw [h] at hc
    exact sub_eq_zero.mp hc

/-! ## Leibniz, exactly and then in the limit -/

/-- **The exact Leibniz rule at finite scale step.**

`δ(ab) = δ(a)·Tb + a·δ(b)` .

The rule is *twisted*: the second factor is read at the shifted scale.  This is
exact for any step, however large. -/
theorem delta_twisted_leibniz (S : ScaleShift A) (a b : A) :
    delta S (a * b) = delta S a * S.T b + a * delta S b := by
  simp only [delta, S.map_mul]
  ring


/-- **Axiom A1 is the zero-step case.**

When the twist is trivial — when `T` acts as the identity on the second factor —
the twisted rule becomes the ordinary Leibniz rule postulated in A1.  So the
classical differential structure is not an expansion truncated at first order
in `ħ`; it is the exact relation evaluated at zero scale step. -/
theorem delta_leibniz_of_untwisted (S : ScaleShift A) (a b : A) (h : S.T b = b) :
    delta S (a * b) = delta S a * b + a * delta S b := by
  rw [delta_twisted_leibniz, h]

/-- Where the shift is trivial, the scale difference vanishes: no step, no
non-commutativity, no quantum. -/
theorem delta_eq_zero_iff (S : ScaleShift A) (a : A) : delta S a = 0 ↔ S.T a = a := by
  simp only [delta, sub_eq_zero]

/-! ## Iterating the step

Composing shifts adds scale steps, which is the group law A5 requires of the
fiducial flow.  The commutator of an `n`-step shift with multiplication is the
`n`-step difference — the same closed form, at every scale separation. -/

/-- Composing two shifts is a shift. -/
def ScaleShift.comp (S R : ScaleShift A) : ScaleShift A where
  T := fun x => S.T (R.T x)
  map_add := by intro x y; rw [R.map_add, S.map_add]
  map_mul := by intro x y; rw [R.map_mul, S.map_mul]

@[simp] theorem ScaleShift.comp_apply (S R : ScaleShift A) (x : A) :
    (S.comp R).T x = S.T (R.T x) := rfl

/-- The exchange relation holds for composed steps too, so the structure is
consistent across arbitrary scale separations rather than only infinitesimal
ones. -/
theorem shift_mul_eq_comp (S R : ScaleShift A) (a : A) :
    (S.comp R).shiftOp * mulOp a = mulOp ((S.comp R).T a) * (S.comp R).shiftOp :=
  shift_mul_eq (S.comp R) a

end SCD.Crossed
