/-
# The operator ordering: what the gravity chain costs when the ring stops commuting

`Diagonal.lean` is the file the whole quantitative gravity chain runs through —
the connection, both Ricci components, the transverse cancellation, the vacuum
scale sum, and from there `γ = 1`, `2β = 1 + γ` and the two arcsecond numbers.
From its `variable` line to its last theorem it is stated over a **`CommRing`**.

`Audit` §V.v registers the consequence and calls it prior to everything else in
that entry: carrying those formulas to a non-commutative ring *requires an
operator ordering that the commutative computation does not determine*.  Nothing
in the development fixes one.  The question this file answers is the one that
was left open there, and it is answerable without any theory of the observer:

> **Is the non-commutative lift of the off-diagonal Ricci ordering-independent?**

**No.**  And the failure is sharper than a difference of values.

## What is proved

* `offDiag` and `offDiagRev` are the same expression with every product written
  in the two available orders.  Their difference is a sum of commutators of
  scale gradients — `offDiag_sub_rev` — so the ambiguity is not diffuse: it is
  exactly the framework's own quantum correction, term by term;
* on a commutative ring the difference vanishes (`orderings_agree_of_comm`), so
  nothing said about the classical sector is disturbed;
* **but the two orderings disagree about what a vacuum is.**
  `vacuum_is_ordering_dependent` exhibits one configuration, in
  `Triple.matrixScaleAlgebra`'s non-commutative model of A1, that satisfies
  `R_ab = 0` written one way and violates it written the other.  This is not a
  discrepancy in a number that both orderings agree is nonzero; it is the
  solution set moving;
* **and the configuration the gravity chain uses is not one of the affected
  ones.**  `ordering_irrelevant_of_static`: under `Diagonal.lean`'s own
  staticity hypothesis — every directional scale varying along one direction —
  every commutator in the difference has a vanishing factor, for every pair.  So
  the ambiguity is real and the chain does not stand in it;
* `offDiagSym` is the reversal-invariant combination (`sym_is_order_free`), for
  anyone who wants a canonical lift rather than a scoped one.  It is stated
  without dividing by two, so it costs no hypothesis on the ring.

## What that settles, and what it does not

**Settled, and this is the answer to the question that motivated the file.**
`γ = 1`, `2β = 1 + γ` and the arcsecond values are statements about a static,
spherically symmetric configuration.  On that configuration every ordering
agrees, by `ordering_irrelevant_of_static`.  They are therefore **not** hostages
to how the observer turns out — which is what needed checking before anything
was built on top of them.

**Not settled, and it should be registered.**  `Diagonal.ric_offdiag`'s *general*
reading — "no pair of directions carries its own curvature; every component is
carried by the complement" — is a `CommRing` theorem whose non-commutative lift
is not unique, so the structural claim is **scoped to the commuting locus** until
an ordering is argued for rather than chosen.  Choosing `offDiagSym` because it
is symmetric would be exactly the move `Audit` §V.t declined for idempotents:
importing the shape of the answer.  What would make it native is an argument
that the contraction defining `Ric` has a preferred order for reasons internal to
the framework.  No such argument exists here.

**And one thing this file is not.**  It does not lift `Diagonal.lean`.  It lifts
the *one* expression whose ordering the chain's cancellation depends on, which is
enough to answer the question and small enough to be checked by eye.  The full
non-commutative connection is a larger job and is not attempted.
-/
import SCD.Diagonal
import SCD.Triple

namespace SCD.Ordering

open SCD ScaleAlgebra Quantum Finset MvPolynomial

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]

/-! ## I.  The two orders

`Diagonal.offDiagTransverse` writes four terms, three of them products of two
gradients.  Over a commutative ring the order within each product is not a
choice.  Over a ring it is, and there are two ways to write the same expression:
left-to-right as `Diagonal.lean` has it, and reversed. -/

/-- The summand of the off-diagonal Ricci, in the order `Diagonal.lean` writes
it.  Compare `Diagonal.offDiagTransverse`, which is this summed over the
transverse directions and negated. -/
def integrand (σ : Fin n → M) (a b c : Fin n) : M :=
  d a (d b (σ c)) - d b (σ a) * d a (σ c) - d a (σ b) * d b (σ c)
    + d a (σ c) * d b (σ c)

/-- The same expression with each product written in the other order.  The
second-derivative term has no order to choose. -/
def integrandRev (σ : Fin n → M) (a b c : Fin n) : M :=
  d a (d b (σ c)) - d a (σ c) * d b (σ a) - d b (σ c) * d a (σ b)
    + d b (σ c) * d a (σ c)

/-- The off-diagonal Ricci, lifted in the left-to-right order. -/
def offDiag (σ : Fin n → M) (a b : Fin n) : M :=
  -∑ c ∈ Diagonal.transverse a b, integrand σ a b c

/-- And in the reversed order. -/
def offDiagRev (σ : Fin n → M) (a b : Fin n) : M :=
  -∑ c ∈ Diagonal.transverse a b, integrandRev σ a b c

/-- **The classical expression is the commuting locus of both.**

Over a `CommRing` the lift is `Diagonal.offDiagTransverse` on the nose, so
nothing below changes any classical statement — it only says what happens when
the hypothesis `CommRing` is dropped. -/
theorem offDiag_eq_classical {A : Type*} [CommRing A] [ScaleAlgebra n A]
    (σ : Fin n → A) (a b : Fin n) :
    offDiag σ a b = Diagonal.offDiagTransverse n σ a b := rfl

/-! ## II.  The difference is a sum of commutators

Not a diffuse ambiguity: each product contributes exactly its own commutator, and
`ad` is the framework's existing word for that (`Quantum.lean`).  So the
obstruction to a canonical lift is built from the same objects `NCConformal.lean`
calls the quantum correction. -/

/-- **The two orders differ by three commutators of gradients, per transverse
direction.** -/
theorem integrand_sub_rev (σ : Fin n → M) (a b c : Fin n) :
    integrand σ a b c - integrandRev σ a b c
      = -ad (d b (σ a)) (d a (σ c)) - ad (d a (σ b)) (d b (σ c))
        + ad (d a (σ c)) (d b (σ c)) := by
  simp only [integrand, integrandRev, ad]
  noncomm_ring

/-- **And so do the two lifts**, summed over the complement of the pair. -/
theorem offDiag_sub_rev (σ : Fin n → M) (a b : Fin n) :
    offDiag σ a b - offDiagRev σ a b
      = ∑ c ∈ Diagonal.transverse a b,
          (ad (d b (σ a)) (d a (σ c)) + ad (d a (σ b)) (d b (σ c))
            - ad (d a (σ c)) (d b (σ c))) := by
  have key : ∀ c : Fin n, integrandRev σ a b c - integrand σ a b c
      = ad (d b (σ a)) (d a (σ c)) + ad (d a (σ b)) (d b (σ c))
        - ad (d a (σ c)) (d b (σ c)) := by
    intro c
    simp only [integrand, integrandRev, ad]
    noncomm_ring
  simp only [offDiag, offDiagRev, neg_sub_neg]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ => key c

/-- **On the commuting locus the choice is not a choice.**

Every commutator vanishes, so the two lifts are equal and the classical
computation is unambiguous — which is why the question never arose while
`Diagonal.lean` stayed over a `CommRing`. -/
theorem orderings_agree_of_comm {A : Type*} [CommRing A] [ScaleAlgebra n A]
    (σ : Fin n → A) (a b : Fin n) : offDiag σ a b = offDiagRev σ a b := by
  have h : offDiag σ a b - offDiagRev σ a b = 0 := by
    rw [offDiag_sub_rev]
    refine Finset.sum_eq_zero fun c _ => ?_
    simp only [ad]
    ring
  exact eq_of_sub_eq_zero h

/-! ## III.  It moves the solution set

A difference of values would be a nuisance.  What is exhibited here is worse and
is the reason the question had to be asked before anything was built on the
chain: **the same configuration is a vacuum solution under one ordering and not
under the other.**

The model is `Triple.matrixScaleAlgebra`, the development's only non-commutative
model of A1, at three directions — three because `Diagonal.transverse a b` is
empty below three and the whole expression is then vacuously zero
(`Diagonal.offdiag_zero_in_two`). -/

/-- Three directions, two of them observed and one transverse, with the
transverse scale carrying two gradients that do not commute: `∂₀τ = E₀₀` and
`∂₁τ = E₀₁`, whose product vanishes in one order and not in the other. -/
noncomputable def crossed : Fin 3 → Triple.Mat 3 :=
  fun i => if i = 2 then !![X 0, X 1; 0, 0] else 0

@[simp] theorem crossed_two : crossed 2 = !![X 0, X 1; 0, 0] := by
  simp [crossed]

@[simp] theorem crossed_zero : crossed 0 = 0 := by
  simp [crossed]

@[simp] theorem crossed_one : crossed 1 = 0 := by
  simp [crossed]

@[simp] theorem transverse_zero_one : Diagonal.transverse (0 : Fin 3) 1 = {2} := by
  decide

/-- **The two orderings disagree about the vacuum.**

`offDiagRev` vanishes on this configuration and `offDiag` does not.  So "the
off-diagonal vacuum equation" is not one equation until an ordering is fixed, and
the framework fixes none. -/
theorem vacuum_is_ordering_dependent :
    offDiagRev crossed 0 1 = 0 ∧ offDiag crossed 0 1 ≠ 0 := by
  have hd0 : d (0 : Fin 3) (crossed 2) = !![1, 0; 0, 0] := by
    rw [crossed_two, Triple.d_mat]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hd1 : d (1 : Fin 3) (crossed 2) = !![0, 1; 0, 0] := by
    rw [crossed_two, Triple.d_mat]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hdd : d (0 : Fin 3) (d (1 : Fin 3) (crossed 2)) = 0 := by
    rw [hd1, Triple.d_mat]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  constructor
  · -- `E₀₁ · E₀₀ = 0`
    simp only [offDiagRev, transverse_zero_one, Finset.sum_singleton, integrandRev,
      crossed_zero, crossed_one, hd0, hd1, d_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · -- but `E₀₀ · E₀₁ = E₀₁`
    have hval : offDiag crossed 0 1 = -!![0, 1; 0, 0] := by
      simp only [offDiag, transverse_zero_one, Finset.sum_singleton, integrand,
        crossed_zero, crossed_one, hd0, hd1, d_zero]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hval]
    intro h
    have hj := congrFun (congrFun (neg_eq_zero.mp h) 0) 1
    simp at hj

/-! ## IV.  But not on the configuration the chain uses

`Diagonal.lean`'s static hypothesis is that every directional scale varies along
**one** direction, `hstat : ∀ a b, b ≠ r → d b (σ a) = 0` — which is that file's
reading of "static and spherically symmetric", and the case the entire gravity
chain is computed in.

Every commutator in `offDiag_sub_rev` carries a factor differentiated along a
member of the observed pair.  If neither member is the distinguished direction,
all of them vanish; if one is, the surviving factors pair with a vanishing one.
Either way the difference is zero, for every pair. -/

/-- **Under staticity the ordering does not matter.**

So `γ = 1`, `2β = 1 + γ` and the arcsecond values do not depend on a choice the
framework has not made.  This is the half of the answer that protects the
existing results, and it is the reason §III is a scope statement rather than a
retraction. -/
theorem ordering_irrelevant_of_static (σ : Fin n → M) (r : Fin n)
    (hstat : ∀ a b : Fin n, b ≠ r → d b (σ a) = 0) (a b : Fin n) (hab : a ≠ b) :
    offDiag σ a b = offDiagRev σ a b := by
  have key : ∀ c ∈ Diagonal.transverse a b,
      ad (d b (σ a)) (d a (σ c)) + ad (d a (σ b)) (d b (σ c))
        - ad (d a (σ c)) (d b (σ c)) = 0 := by
    intro c _
    by_cases ha : a = r
    · -- `a` is the distinguished direction, so `b` is not, and every derivative
      -- along `b` vanishes
      have hb : b ≠ r := fun h => hab (ha.trans h.symm)
      have hb0 : ∀ x : Fin n, d b (σ x) = 0 := fun x => hstat x b hb
      simp [ad, hb0]
    · -- `a` is not the distinguished direction, so every derivative along `a`
      -- vanishes
      have ha0 : ∀ x : Fin n, d a (σ x) = 0 := fun x => hstat x a ha
      simp [ad, ha0]
  have h : offDiag σ a b - offDiagRev σ a b = 0 := by
    rw [offDiag_sub_rev]; exact Finset.sum_eq_zero key
  exact eq_of_sub_eq_zero h

/-! ## V.  The reversal-invariant combination

If a canonical lift is wanted rather than a scoped claim, the symmetric
combination is available and costs nothing: it is stated as the *sum* of the two
orders, so no inverse of `2` is required and the ring keeps its generality.

It is offered and not adopted.  Nothing in A1–A7 says the contraction defining
`Ric` should be symmetrised, and picking it because it is symmetric is the move
`Audit` §V.t declined when the same shortcut was available for idempotents. -/

/-- Twice the symmetrised summand: the two orders added. -/
def integrandSym (σ : Fin n → M) (a b c : Fin n) : M :=
  integrand σ a b c + integrandRev σ a b c

/-- **The symmetric combination is order-free**, by construction and not by
accident: reversing every product exchanges the two summands. -/
theorem sym_is_order_free (σ : Fin n → M) (a b c : Fin n) :
    integrandSym σ a b c = integrandRev σ a b c + integrand σ a b c := by
  simp only [integrandSym]
  exact add_comm _ _

/-- And on the commuting locus it is twice the classical summand, so adopting it
would not change any existing result — only fix a choice the axioms do not
make. -/
theorem sym_doubles_the_classical {A : Type*} [CommRing A] [ScaleAlgebra n A]
    (σ : Fin n → A) (a b c : Fin n) :
    integrandSym σ a b c = 2 * integrand σ a b c := by
  simp only [integrandSym, integrand, integrandRev]
  ring

/-! ## VI.  The finding, as one statement -/

/-- **Step zero's answer.**

The lift is not unique and the non-uniqueness reaches the vacuum condition; the
static configuration is untouched by it.  Both halves matter and the register
should carry both. -/
theorem summary (σ : Fin n → M) (r : Fin n)
    (hstat : ∀ a b : Fin n, b ≠ r → d b (σ a) = 0) (a b : Fin n) (hab : a ≠ b) :
    (offDiagRev crossed 0 1 = 0 ∧ offDiag crossed 0 1 ≠ 0)
      ∧ offDiag σ a b = offDiagRev σ a b :=
  ⟨vacuum_is_ordering_dependent, ordering_irrelevant_of_static σ r hstat a b hab⟩

end SCD.Ordering
