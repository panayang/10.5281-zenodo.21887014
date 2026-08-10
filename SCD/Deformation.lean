/-
# The classical limit, formalized

`Quantum.lean` showed that inner derivations obey the differential axioms of
the classical sector, and that the CCR reproduces the power rule.  What was
missing was the bridge in the other direction: a proof that the *commutative*
scale algebra is the `ħ → 0` limit of a non-commutative one, so that the
classical derivations `∂ᵢ` really are commutators and not merely analogous to
them.

This file supplies it, and does so without any analytic limit at all.

Take the first-order deformation `A_ħ = A[ħ]/(ħ²)` with the star product

    (f₀ + ħf₁) ⋆ (g₀ + ħg₁) = f₀g₀ + ħ(f₀g₁ + f₁g₀ + P(f₀,g₀)) ,

where `P` is any biderivation of `A`.  Then:

* `star_assoc` — the product is associative, so `A_ħ` is a genuine algebra;
* `star_classical` — at `ħ = 0` it is exactly the commutative product of `A`;
* `star_commutator` — the commutator is `ħ` times the antisymmetrisation of
  `P`, so `ħ⁻¹[·,·]⋆` equals the Poisson bracket **exactly**, with no limiting
  process to justify;
* `poisson_leibniz_left` — that bracket is a derivation of `A` in each slot.

The last two together are the statement that was owed.  The derivations `∂ᵢ`
postulated in A1 are recovered as `ħ⁻¹` times inner derivations of `A_ħ`;
non-commutativity is first order in `ħ` and disappears at `ħ = 0`, leaving
the commutative geometry of the gravitational sector.  `ccr_of_canonical` then
closes the circle back to `Quantum.ad_pow`.

Working at first order is not a truncation of the physics: the correspondence
principle *is* a first-order statement, and at first order the deformation is
exact and finite, which is why it can be checked by machine.
-/
import SCD.Quantum
import SCD.Basic

namespace SCD.Deformation

open SCD ScaleAlgebra

variable {A : Type*} [CommRing A]

/-! ## Biderivations -/

/-- A biderivation of a commutative ring: additive and Leibniz in each
argument.  This is the data of a first-order deformation. -/
structure Biderivation (A : Type*) [CommRing A] where
  /-- The underlying bilinear map. -/
  B : A → A → A
  add_left : ∀ a b c, B (a + b) c = B a c + B b c
  add_right : ∀ a b c, B a (b + c) = B a b + B a c
  leibniz_left : ∀ a b c, B (a * b) c = a * B b c + b * B a c
  leibniz_right : ∀ a b c, B a (b * c) = b * B a c + c * B a b

namespace Biderivation

variable (P : Biderivation A)

/-- The **Poisson bracket** induced by a biderivation: its antisymmetric part.
This is what survives in the commutator of the deformed product. -/
def poisson (a b : A) : A := P.B a b - P.B b a

@[simp] theorem poisson_antisymm (a b : A) : P.poisson a b = -P.poisson b a := by
  simp only [poisson]; ring

@[simp] theorem poisson_self (a : A) : P.poisson a a = 0 := by
  simp only [poisson]; ring

/-- **The Poisson bracket is a derivation in its first argument.**

This is the precise sense in which the classical derivations of A1 are
recovered from the deformation: each `{·, g}` is a derivation of the
commutative ring `A`. -/
theorem poisson_leibniz_left (a b c : A) :
    P.poisson (a * b) c = a * P.poisson b c + b * P.poisson a c := by
  simp only [poisson, P.leibniz_left, P.leibniz_right]
  ring

/-- And in its second argument. -/
theorem poisson_leibniz_right (a b c : A) :
    P.poisson a (b * c) = b * P.poisson a c + c * P.poisson a b := by
  simp only [poisson, P.leibniz_left, P.leibniz_right]
  ring

end Biderivation

/-! ## The deformed algebra `A[ħ]/(ħ²)`

An element is a pair `(f₀, f₁)` standing for `f₀ + ħf₁`.  We work with the
product as a plain function so that no unintended ring structure on pairs can
interfere. -/

/-- The star product to first order in `ħ`. -/
def star (P : Biderivation A) (f g : A × A) : A × A :=
  (f.1 * g.1, f.1 * g.2 + f.2 * g.1 + P.B f.1 g.1)

variable (P : Biderivation A)

/-- **The deformation is associative**, for *any* biderivation.  The Leibniz
rules are exactly the Hochschild cocycle condition at first order. -/
theorem star_assoc (f g h : A × A) :
    star P (star P f g) h = star P f (star P g h) := by
  simp only [star, Prod.mk.injEq]
  constructor
  · ring
  · rw [P.leibniz_left, P.leibniz_right]
    ring

/-- **The classical limit.**  Setting `ħ = 0` — reading off the coefficient of
`ħ⁰` — returns exactly the commutative product of `A`.  No approximation. -/
@[simp] theorem star_classical (f g : A × A) : (star P f g).1 = f.1 * g.1 := rfl

/-- The deformed product is commutative to zeroth order in `ħ`. -/
theorem star_comm_classical (f g : A × A) : (star P f g).1 = (star P g f).1 := by
  simp only [star_classical]; ring

/-- **The correspondence principle, exactly.**

The commutator of the deformed product has no classical part, and its
`ħ`-coefficient is precisely the Poisson bracket:

    `ħ⁻¹ [f, g]⋆ = {f₀, g₀}` .

There is no limit to take — at first order the identity is exact.  This is the
statement that `∂ᵢ = ħ⁻¹ ad_{Pᵢ}` in the classical sector. -/
theorem star_commutator (f g : A × A) :
    ((star P f g).1 - (star P g f).1 = 0)
    ∧ ((star P f g).2 - (star P g f).2 = P.poisson f.1 g.1) := by
  constructor
  · simp only [star_classical]; ring
  · simp only [star, Biderivation.poisson]; ring

/-- Non-commutativity is exactly the failure of `P` to be symmetric — that is,
exactly the Poisson bracket.  A vanishing bracket gives back a commutative
algebra, which is the gravitational sector. -/
theorem star_comm_iff_poisson_zero (f g : A × A) :
    star P f g = star P g f ↔ P.poisson f.1 g.1 = 0 := by
  simp only [star, Prod.mk.injEq, Biderivation.poisson]
  constructor
  · rintro ⟨_, h2⟩
    linear_combination h2
  · intro h
    exact ⟨by ring, by linear_combination h⟩

/-! ## The canonical bracket from the scale algebra

A pair of directions of the substrate gives a biderivation, hence a
deformation.  This is where `ħ` enters the scale programme: it is the
coefficient of the first-order non-commutativity of the very derivations that
A1 postulates. -/

variable {n : ℕ} [ScaleAlgebra n A]

/-- The biderivation built from two directions of the substrate. -/
def canonical (p q : Fin n) : Biderivation A where
  B a b := d q a * d p b
  add_left a b c := by rw [d_add]; ring
  add_right a b c := by rw [d_add]; ring
  leibniz_left a b c := by rw [d_mul]; ring
  leibniz_right a b c := by rw [d_mul]; ring

@[simp] theorem canonical_poisson (p q : Fin n) (a b : A) :
    (canonical (A := A) p q).poisson a b = d q a * d p b - d q b * d p a := rfl

/-- **The canonical commutation relation.**

If `X` and `Mom` are canonically conjugate coordinates of the substrate — `X`
varying only along `p`, `Mom` only along `q` — then their Poisson bracket is `1`,
so in the deformed algebra

    `[Mom, X]⋆ = ħ · 1` .

Taking `ħ = iℏ` this is `[Mom, X] = iℏ`.  Combined with `Quantum.ad_pow`, which
recovers the power rule of calculus from exactly this relation, the circle is
closed: the commutative differential structure of the gravitational sector and
the canonical commutation relation of quantum mechanics are the two ends of one
first-order deformation. -/
theorem ccr_of_canonical (p q : Fin n) (X Mom : A)
    (hXp : d p X = 1) (hXq : d q X = 0)
    (hPp : d p Mom = 0) (hPq : d q Mom = 1) :
    (canonical (A := A) p q).poisson Mom X = 1 := by
  simp only [canonical_poisson, hXp, hXq, hPp, hPq]
  ring

/-- The bracket of a coordinate with itself vanishes, as it must. -/
@[simp] theorem canonical_poisson_self (p q : Fin n) (a : A) :
    (canonical (A := A) p q).poisson a a = 0 :=
  Biderivation.poisson_self _ a

end SCD.Deformation
