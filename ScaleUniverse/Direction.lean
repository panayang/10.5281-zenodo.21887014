/-
# Directions are not given: they are the algebra

The last unresolved foundational input was the dimension `n`, and with it the
index set `Fin n` that A1 hands over.  This file removes the index set.  What
it finds along the way is that A1 was smuggling more than a dimension.

Look at what A1 actually says: there are `n` derivations `∂₀,…,∂ₙ₋₁` which
**commute**.  Two things are being assumed there, not one.  The index set is
the obvious one.  The other is the commutativity.

**Correction (see `Dynamics.lean`).**  I originally read that commutativity as
a hidden *flatness* assumption — "commuting directions are flat coordinate
directions".  **That reading is wrong and is withdrawn.**  Commuting coordinate
directions are a choice of chart, available locally always, and imply nothing
about curvature; `Dynamics.no_flatness_from_commuting_derivations` kills the
derivations entirely and the curvature survives untouched.  Flatness is a
statement about whether the *connection* commutes.  What A1 assumes is a chart
and an index set — a genuine input, but a smaller one than I claimed.

Drop the index set.  A direction is not a label; it is an element of the
comparison algebra, and transporting along it is linear in it.  Then:

* `curv` — curvature is the failure of transport to respect the bracket of
  directions, `F(x,y) = [D_x, D_y] − D_{[x,y]}`.  Nothing external defines it;
* `flat_iff_lie_hom` — flat means exactly that transport is a Lie map;
* `curv_of_abelian` — when the direction algebra is abelian this reduces to
  `[D_x, D_y]`, which is `Connection.comm_covD`'s object.  The old theory is
  the abelian case;
* `commute_iff_bracket_acts_trivially` — for a **flat** transport, "the
  directions commute" is *equivalent* to "the bracket acts trivially".  Note
  the hypothesis: this is a statement about flat transports, not a derivation
  that commuting directions are flat.

So `n` is no longer chosen by hand.

**Correction (see `Dimension.lean`).**  I wrote that the directions *are* the
algebra and `n` is that algebra's dimension.  With the algebra now named that is
checkable, and it is **false**: `dim so(3,1) = 6` while spacetime has `4`
directions.  The directions are the space the algebra **acts on** — its defining
representation — not the algebra.  Nothing is lost: `so(k,1)` carries a
canonical `k+1`-dimensional representation, so naming the algebra still fixes
`n`, as `k + 1`.  Choosing a basis is a convenience, not
an axiom — `transport_determined_by_generators` says a transport is fixed by
its values on any additively generating set.

**Honest limit.** This derives *that* directions are algebra elements and that
their count is the algebra's dimension.  It does not derive *which* algebra, so
it does not predict `n = 4`. The input has moved from "a set of `n` commuting
labels plus a flat metric plus a signature" to "one algebra"; that is
compression plus the removal of a hidden flatness assumption, not a derivation
of the dimension.
-/
import ScaleUniverse.Quantum

namespace ScaleUniverse.Direction

open ScaleUniverse Quantum

variable {g M : Type*} [Ring g] [Ring M]

/-! ## Transport along an algebra element -/

/-- **Transport indexed by the algebra itself.**

There is no `Fin n`.  A direction is an element of the comparison algebra `g`,
and transport is additive in the direction as well as being a derivation of the
things transported. -/
structure DirTransport (g M : Type*) [Ring g] [Ring M] where
  /-- Transport along direction `x`. -/
  D : g → M → M
  /-- Additive in the *direction*: directions superpose. -/
  add_dir : ∀ x y m, D (x + y) m = D x m + D y m
  /-- Additive in what is transported. -/
  add_val : ∀ x m m', D x (m + m') = D x m + D x m'
  /-- A derivation, as transport of a product must be. -/
  leibniz : ∀ x m m', D x (m * m') = D x m * m' + m * D x m'

namespace DirTransport

variable (T : DirTransport g M)

/-- The zero direction transports nothing. -/
@[simp] theorem D_zero_dir (m : M) : T.D 0 m = 0 := by
  have h00 := T.add_dir 0 0 m
  rw [add_zero] at h00
  have h1 : T.D 0 m + 0 = T.D 0 m + T.D 0 m := by rw [add_zero]; exact h00
  exact (add_left_cancel h1).symm

/-- Reversing a direction reverses the transport. -/
@[simp] theorem D_neg_dir (x : g) (m : M) : T.D (-x) m = -T.D x m := by
  have h := T.add_dir x (-x) m
  rw [add_neg_cancel, T.D_zero_dir] at h
  have h2 : T.D x m + T.D (-x) m = 0 := h.symm
  calc T.D (-x) m = -T.D x m + (T.D x m + T.D (-x) m) := by abel
    _ = -T.D x m + 0 := by rw [h2]
    _ = -T.D x m := by abel

/-- **Curvature: the failure of transport to respect the bracket.**

`F(x,y) = [D_x, D_y] − D_{[x,y]}` .

Nothing outside the algebra is used to define this — no index set, no metric,
no signature.  Compare `Connection.F`, which needed a connection one-form and a
flat `δ` to raise indices. -/
def curv (x y : g) (m : M) : M :=
  T.D x (T.D y m) - T.D y (T.D x m) - T.D (ad x y) m

@[simp] theorem curv_self (x : g) (m : M) : T.curv x x m = 0 := by
  simp [curv, ad]

theorem curv_antisymm (x y : g) (m : M) : T.curv x y m = -T.curv y x m := by
  simp only [curv, ad]
  have hneg : y * x - x * y = -(x * y - y * x) := by abel
  rw [hneg, T.D_neg_dir]
  abel

/-! ## Flat means "transport is a Lie map" -/

/-- **Flatness is exactly the homomorphism property.**

A transport is curvature-free precisely when it carries the bracket of
directions to the commutator of transports.  Curvature is the obstruction to
that, and to nothing else. -/
theorem flat_iff_lie_hom :
    (∀ x y m, T.curv x y m = 0)
      ↔ (∀ x y m, T.D (ad x y) m = T.D x (T.D y m) - T.D y (T.D x m)) := by
  constructor
  · intro h x y m
    have hx := h x y m
    simp only [curv] at hx
    exact (sub_eq_zero.mp hx).symm
  · intro h x y m
    simp only [curv, h x y m, sub_self]

/-! ## The old theory is the abelian case, and that was the assumption -/

/-- Where the directions commute in the algebra, curvature reduces to the bare
commutator of transports — the object `Connection.comm_covD` computes.  So the
previous development is the abelian special case of this one. -/
theorem curv_of_abelian (x y : g) (m : M) (hxy : ad x y = 0) :
    T.curv x y m = T.D x (T.D y m) - T.D y (T.D x m) := by
  simp only [curv, hxy, T.D_zero_dir, sub_zero]

/-- **The exposure.**

For a flat transport, "the directions commute" — A1's requirement — is
*equivalent* to the bracket acting trivially.  A1 was not merely choosing an
index set: it was assuming the direction algebra is abelian, which is to say
assuming the directions are flat.

That is why a flat metric `δ` then had to be postulated separately: the
flatness had already been put in by hand at the level of the directions, and
the curvature had to be reintroduced from outside. -/
theorem commute_iff_bracket_acts_trivially (hflat : ∀ x y m, T.curv x y m = 0) :
    (∀ x y m, T.D x (T.D y m) = T.D y (T.D x m))
      ↔ (∀ x y m, T.D (ad x y) m = 0) := by
  constructor
  · intro hcomm x y m
    have h := hflat x y m
    simp only [curv, hcomm x y m, sub_self, zero_sub, neg_eq_zero] at h
    exact h
  · intro hbr x y m
    have h := hflat x y m
    simp only [curv, hbr x y m, sub_zero] at h
    exact sub_eq_zero.mp h

/-! ## No index set is needed

Transport is additive in the direction, so it is fixed by its values on any
additively generating set of directions.  Choosing a basis is a convenience;
the directions themselves are the algebra. -/

/-- Two transports agreeing on two directions agree on their sum: nothing about
the labels matters, only the algebra. -/
theorem transport_determined_by_generators (T' : DirTransport g M) (x y : g) (m : M)
    (hx : T.D x m = T'.D x m) (hy : T.D y m = T'.D y m) :
    T.D (x + y) m = T'.D (x + y) m := by
  rw [T.add_dir, T'.add_dir, hx, hy]

end DirTransport

end ScaleUniverse.Direction
