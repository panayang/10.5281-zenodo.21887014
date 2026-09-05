/-
# The founding statement needs a group; the ring is for the geometry

The framework's founding statement is **scale × energy = constant**, and A2–A3
encode it: `s` is a unit, `ε = s⁻¹`, `s·ε = 1`.  Everything was then built in a
commutative ring, and the development never asked whether that is the right home
for the statement.  This file asks, and the answer separates two things that have
been travelling as one.

## I.  The log-derivative is a group homomorphism, and nobody had written it

`Gradient.lean` proved `logDeriv_spec` and `logDeriv_closed` and stopped.
`logDeriv_mul` is new here — the founding statement made functorial.  With it:

* `logDeriv_one` — the trivial scale has no gradient;
* `logDeriv_inv` — **`logDeriv s⁻¹ = − logDeriv s`**.

The second is A3.  *Scale × energy = constant* says the energy's gradient is minus
the scale's, and that is **not an extra axiom** — it is inversion in a group.  Once
A2 is read as "the scales form a group and the gradient is a homomorphism", A3's
content beyond naming `ε` is discharged.

## II.  The axiom's minimal home

`ScaleHom`: a group `G`, an abelian group `M`, and `D : G → Mⁿ` with
`D(st) = D s + D t`.  `map_one` and `map_inv` come free, and `ofScaleAlgebra`
shows every scale algebra is one.

**No ring, no commutativity, no multiplication anywhere in the signature.**  That
is the whole of what the founding statement needs.

## III.  Where the ring actually enters, exactly

`sig_add` — the gradient is additive in the log-scale.  The axiom is **linear**.

`gradsq_add` —

        gradsq(σ+τ) = gradsq σ + gradsq τ + 2 ∑ᵢ sig σ ᵢ · sig τ ᵢ .

The geometry is **quadratic**, and its failure to be a homomorphism is exactly a
**symmetric bilinear pairing of gradients**.  `gradsq`, `Chr`, `Rm`, `Ric` are all
built from that pairing and from nothing else the group has.

> **The axiom is a homomorphism.  The geometry is a bilinear form.  A commutative
> ring supplies both at once — which is why it was chosen — and it was never
> recorded that these are two commitments rather than one.**

## IV.  What the framework actually needs, listed so each piece can be attacked

Not one structure but three, and a commutative ring with commuting derivations
hands over all three in a single move:

1. a **group** of scales, with the gradient a homomorphism — the founding
   statement, and all `ScaleHom` needs;
2. an abelian group of gradients carrying **`n` commuting derivations**, because
   `hess` differentiates a gradient again — `ScaleHom` does not supply this;
3. a **symmetric bilinear pairing** on that group — the geometry, by
   `gradsq_add`.

## What is claimed, and what is not

**Not claimed:** that the commutative ring is wrong, or that a replacement exists.
Nothing here exhibits a model that satisfies (1)–(3) and is not a ring.

**Claimed:** that (1)–(3) are separable, that only (1) is the founding statement,
and that the register has been carrying ring structure as if it were axiomatic
when most of it is a modelling choice made for the geometry.

**And the sharp form of the worry.**  In a ring, the multiplication that defines
the unit group `Aˣ` and the multiplication that supplies the geometric pairing
are **the same operation**.  Nothing in *scale × energy = constant* says they
should be.  That coincidence is a substantive commitment; it has never been
stated; and it is where "the mathematical form may be wrong" would have to bite
if it bites anywhere.
-/
import SCD.Gradient

namespace SCD.Reduction

open SCD ScaleAlgebra

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]


/-! ## I. The log-derivative is a group homomorphism -/

/-- **The log-derivative is a group homomorphism.**

`(st)⁻¹ d(st) = s⁻¹ ds + t⁻¹ dt` by Leibniz.  This is the founding statement made
functorial, and `Gradient.lean` never wrote it. -/
theorem logDeriv_mul (s t : Aˣ) (i : Fin n) :
    Gradient.logDeriv (s * t) i = Gradient.logDeriv s i + Gradient.logDeriv t i := by
  have hs : ((s⁻¹ : Aˣ) : A) * (s : A) = 1 := s.inv_mul
  have ht : ((t⁻¹ : Aˣ) : A) * (t : A) = 1 := t.inv_mul
  simp only [Gradient.logDeriv, Units.val_mul, d_mul, mul_inv_rev]
  linear_combination (((s⁻¹ : Aˣ) : A) * d i (s : A)) * ht
    + (((t⁻¹ : Aˣ) : A) * d i (t : A)) * hs

/-- **The trivial scale has no gradient.** -/
theorem logDeriv_one (i : Fin n) : Gradient.logDeriv (1 : Aˣ) (n := n) i = 0 := by
  simp only [Gradient.logDeriv, Units.val_one, d_one, mul_zero]

/-- **A3, as a theorem.**

*Scale × energy = constant* with `ε = s⁻¹` says the energy's gradient is minus the
scale's.  That is inversion in a group and not an independent axiom. -/
theorem logDeriv_inv (s : Aˣ) (i : Fin n) :
    Gradient.logDeriv s⁻¹ i = - Gradient.logDeriv (n := n) s i := by
  have h := logDeriv_mul s s⁻¹ i
  rw [mul_inv_cancel, logDeriv_one] at h
  linear_combination -h

/-! ## II. The geometry is not a homomorphism, and the defect is bilinear -/

/-- **The axiom is linear**: the gradient is additive in the log-scale. -/
theorem sig_add (σ τ : A) (i : Fin n) : sig (σ + τ) i = sig σ i + sig τ i := by
  simp only [sig, d_add]

/-- **The geometry is quadratic, and the defect is a bilinear pairing.**

Polarisation.  The gradient's additivity does not survive into `gradsq`, and what
it fails by is exactly a symmetric bilinear form on gradients — which is the one
thing the ring supplies that `ScaleHom` does not. -/
theorem gradsq_add (σ τ : A) :
    gradsq n (σ + τ) = gradsq n σ + gradsq n τ + 2 * ∑ i : Fin n, sig σ i * sig τ i := by
  simp only [gradsq, sig_add]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## III. The axiom's minimal home -/

/-- **The founding statement's minimal home**: a group of scales, an abelian
group of gradients, and a homomorphism between them.

No ring, no commutativity, no multiplication in the signature. -/
structure ScaleHom (n : ℕ) (G : Type*) [Group G] (M : Type*) [AddCommGroup M] where
  D : G → (Fin n → M)
  map_mul : ∀ s t, D (s * t) = D s + D t

namespace ScaleHom

/-- The trivial scale has no gradient — free from the homomorphism law. -/
theorem map_one {n : ℕ} {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    (H : ScaleHom n G M) : H.D 1 = 0 := by
  have h := H.map_mul 1 1
  rw [one_mul] at h
  have : H.D 1 + H.D 1 - H.D 1 = H.D 1 - H.D 1 := by rw [← h]
  simpa using this

/-- **And inversion is negation**, which is *scale × energy = constant* with no
ring in sight. -/
theorem map_inv {n : ℕ} {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    (H : ScaleHom n G M) (s : G) : H.D s⁻¹ = - H.D s := by
  have h := H.map_mul s s⁻¹
  rw [mul_inv_cancel, H.map_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end ScaleHom

/-- **Every scale algebra gives one**, and the map is the log-derivative. -/
def ofScaleAlgebra : ScaleHom n Aˣ A where
  D s := Gradient.logDeriv s
  map_mul s t := funext fun i => logDeriv_mul s t i

end SCD.Reduction
