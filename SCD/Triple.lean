/-
# Observer, observed, process — and where the quantum enters

Idempotents were the wrong candidate, and they were wrong for the reason
`Internal.lean` flagged: adopting them imports the quantum measurement postulate
rather than deriving one.  The better move is to **separate the three roles** —
what is observed, what observes, and the process between them — and let the
coupling be one the framework already has.

It already has one, and it has had it since `Determination.lean`.

## I.  The three-place structure was already there

`Determination.influence σ a b c` is a **three-place** object: the contribution of
direction `c` to the pair `(a, b)`.  Read it as

* **observed** — the pair `(a, b)`;
* **observer** — the direction `c`;
* **process** — `influence σ a b c` itself, which is a coupling of the two and is
  the framework's own notion of force.

`Diagonal.ric_offdiag` then says the observed pair's curvature is minus the sum of
every observer's contribution.  Nothing is added here.  What is new is that the
process is **algebra-valued**, where `Observer.Crossed` produced a `Prop` from an
order on `ℝ`.  That is the difference `Internal.lean` identified as the whole of
G3, and it is why this reading reaches where the crossed-set reading could not.

## II.  Bidirectionality, and the two swaps are not alike

There are two ways to reverse a three-place relation, and they behave completely
differently.

**Swapping the two members of the observed pair.**  Over a *commutative* ring,
`Determination.influence_symm`: reading `(a,b)` or `(b,a)` gives the same thing,
which is the third law as one expression read from either end.  Over a general
ring it **fails, by exactly one commutator**:

> **`influence_asymmetry` : `inf σ a b c − inf σ b a c = [∂_a σ_c , ∂_b σ_c]`.**

Every other term is symmetric — the second derivative by `d_comm`, and the two
cross terms because they simply exchange.  What survives is the product
`(∂_aσ_c)(∂_bσ_c)` against `(∂_bσ_c)(∂_aσ_c)`, and their difference is the
commutator.

So `influence_symm` is the **classical limit** of this, and:

> **The order in which an observation is read matters, and the discrepancy is
> exactly the quantum correction.**

By `Deformation.star_commutator` that commutator is `ħ` times a Poisson bracket.
Nothing was imported: the incompatibility of two readings is a theorem about
`Determination.influence` over a ring, and `Quantum.ad` was already the
framework's word for it.

**Swapping observer with observed** is a different matter and is **not** a
symmetry even classically — `observer_observed_not_symmetric` exhibits the
failure.  That is as it should be: which part is the record and which is recorded
is a real distinction, and it is a *classical* one.  The quantum asymmetry lives
entirely inside the observed pair.

## III.  The development had no non-commutative model, and now has one

Everything above is vacuous unless A1 has a non-commutative model, and **it did
not**.  All four models in the development — `Positivity.oneAxis`,
`Witness.polyScaleAlgebra`, `Newton.instScaleAlgebra`,
`Explanation.mvScaleAlgebra` — are commutative.  So the non-commutative sector
had been reasoned about for the whole development with **no witness**, which is
its own finding and is registered.

`matrixScaleAlgebra` supplies one: two-by-two matrices over polynomials, with the
partial derivatives acting entrywise.  Entrywise differentiation is a derivation
of a matrix ring, and the partials still commute, so A1 holds and the ring does
not.

And in it the asymmetry is not zero: `asymmetry_witness` takes
`σ_c = [[x₀, x₁], [0, 0]]`, whose two gradients are the matrix units `E₀₀` and
`E₀₁`, and `[E₀₀, E₀₁] = E₀₁ ≠ 0`.

## IV.  What this changes, and what it does not

**G3 is narrowed, not closed.**  The observer now reaches the algebra: an
observation is an element of a possibly non-commutative ring, two readings of one
observation need not agree, and the disagreement is a commutator.  That is
incompatibility of measurements, arrived at natively.

**But it is the subleading correction.**  By `NCSize.iso_commutator_star` the
commutator `[∂_aσ_c, ∂_bσ_c]` is `ħ` times a bracket of *gradients* — **four
derivatives in all**.  The framework's *leading* non-commutative object is
`[σ_a, σ_b]`, two derivatives (`NCSize.dir_commutator_star`), and **it does not
appear in `influence` at all**: every term there carries a single directional
scale `σ_c`, so no commutator between two different directional scales can
arise.

> **Observation sees the isotropic quantum correction and is still blind to the
> leading anisotropic one.**

That is a much sharper statement of what remains than `Observed.lean` §G3 had,
and it says where to look next: a coupling in which the observer's own scale
`σ_c` multiplies the observed pair's scales `σ_a`, `σ_b`, rather than only its own
gradients.  `Determination.influence` has no such term, and whether one is forced
is exactly the open question.

Nothing here is postulated.  `influence_asymmetry` is an identity, the model is a
construction, and the negative half — that `[σ_a, σ_b]` never appears — is read
off the definition and is stated as such.
-/
import SCD.Determination
import SCD.Quantum
import SCD.Explanation
import SCD.NCSize

namespace SCD.Triple

open SCD ScaleAlgebra Quantum MvPolynomial

/-! ## I. The three-place process, over a ring -/

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]

/-- **The observation process**: the contribution of the observer `c` to the
observed pair `(a, b)`.

This is `Determination.influence` with the commutativity hypothesis dropped.  The
expression is unchanged; only the ambient ring is weaker, and that is the whole
point — the value now lives in an algebra that need not commute. -/
def inf (σ : Fin n → M) (a b c : Fin n) : M :=
  d a (d b (σ c)) - d b (σ a) * d a (σ c)
    - d a (σ b) * d b (σ c) + d a (σ c) * d b (σ c)

/-- Over a commutative ring this is `Determination.influence` unchanged. -/
theorem inf_eq_influence {A : Type*} [CommRing A] [ScaleAlgebra n A]
    (σ : Fin n → A) (a b c : Fin n) :
    inf σ a b c = Determination.influence σ a b c := rfl

/-! ## II. The two swaps -/

/-- **Reading the observed pair the other way differs by exactly one
commutator.**

        inf σ a b c − inf σ b a c = [∂_a σ_c , ∂_b σ_c] .

The second derivative is symmetric by `d_comm` and the two cross terms merely
exchange; what is left is `(∂_aσ_c)(∂_bσ_c)` against its reverse.

`Determination.influence_symm` is the commutative case of this, so the third law
— action and reaction as one expression — is the **classical limit** of an
identity whose quantum content is a commutator.  By `Deformation.star_commutator`
that commutator is `ħ` times a Poisson bracket.

**The order in which an observation is read matters, and the discrepancy is the
quantum correction.**  Nothing is imported: `Quantum.ad` was already the
framework's word for this. -/
theorem influence_asymmetry (σ : Fin n → M) (a b c : Fin n) :
    inf σ a b c - inf σ b a c = ad (d a (σ c)) (d b (σ c)) := by
  simp only [inf, ad]
  rw [d_comm a b (σ c)]
  noncomm_ring

/-- **And in the commutative sector the two readings agree**, which recovers
`Determination.influence_symm` from the identity above rather than proving it
separately. -/
theorem readings_agree_of_comm {A : Type*} [CommRing A] [ScaleAlgebra n A]
    (σ : Fin n → A) (a b c : Fin n) :
    inf σ a b c - inf σ b a c = 0 := by
  rw [influence_asymmetry]
  simp only [ad, mul_comm, sub_self]

/-! ## III. The first non-commutative model of A1

Everything above is vacuous unless the axioms have a non-commutative model, and
the development had none: `Positivity.oneAxis`, `Witness.polyScaleAlgebra`,
`Newton.instScaleAlgebra` and `Explanation.mvScaleAlgebra` are all commutative. -/

/-- Two-by-two matrices over polynomials in `m` variables. -/
abbrev Mat (m : ℕ) := Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin m) ℝ)

/-- **A1 realised non-commutatively.**

Entrywise differentiation is a derivation of a matrix ring — the Leibniz rule
holds summand by summand in the matrix product — and the partials still commute.
So A1 holds while the ring does not, which is the first such witness in the
development. -/
noncomputable instance matrixScaleAlgebra (m : ℕ) : ScaleAlgebra m (Mat m) where
  d i := fun A => A.map (pderiv i)
  d_add i A B := Matrix.ext fun j k => by
    show pderiv i (A j k + B j k) = _
    simp [Matrix.map_apply]
  d_mul i A B := Matrix.ext fun j k => by
    show pderiv i ((A * B) j k) = _
    simp only [Matrix.mul_apply, map_sum, Matrix.add_apply, Matrix.map_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simpa using pderiv_mul (i := i) (f := A j l) (g := B l k)
  d_comm i j A := Matrix.ext fun a b => Explanation.pderiv_comm' i j (A a b)

@[simp] theorem d_mat {m : ℕ} (i : Fin m) (A : Mat m) :
    d i A = A.map (pderiv i) := rfl

/-- A directional scale whose two gradients are the matrix units `E₀₀` and
`E₀₁`, which do not commute. -/
noncomputable def crossedScale : Fin 2 → Mat 2 := fun _ => !![X 0, X 1; 0, 0]

/-- **The asymmetry is not zero.**

`[E₀₀, E₀₁] = E₀₁ ≠ 0`, so there is a configuration in which the two readings of
one observation genuinely disagree.  The incompatibility of §II is realised, not
merely permitted. -/
theorem asymmetry_witness :
    ad (d (0 : Fin 2) (crossedScale 0)) (d (1 : Fin 2) (crossedScale 0)) ≠ 0 := by
  intro h
  have hj := congrFun (congrFun h 0) 1
  simp [ad, crossedScale, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hj

/-- **So the two readings of one observation genuinely disagree.** -/
theorem readings_disagree :
    inf crossedScale 0 1 0 - inf crossedScale 1 0 0 ≠ 0 := by
  rw [influence_asymmetry]
  exact asymmetry_witness

/-! ## IV. The other swap is not a symmetry, and classically so -/

/-- **Exchanging observer with observed is not a symmetry**, even over a
commutative ring.

Which part is the record and which is recorded is a real distinction, and it is a
*classical* one.  Exhibited in `Explanation.lean`'s commutative three-direction
model, where the two orderings give different values. -/
theorem observer_observed_not_symmetric :
    Determination.influence Explanation.coupled 0 1 2
      ≠ Determination.influence Explanation.coupled 0 2 1 := by
  rw [Explanation.coupled_influence]
  intro h
  have hv := congrArg (eval (fun _ => (0 : ℝ))) h
  simp [Determination.influence, Explanation.coupled] at hv

/-- **Collected.**

The pair swap is quantum — it fails by a commutator, and the failure is realised
in a genuine non-commutative model.  The observer/observed swap fails already
classically.  Two different asymmetries, and only one of them carries `ħ`. -/
theorem summary :
    (∀ {m : ℕ} {N : Type} [Ring N] [ScaleAlgebra m N] (σ : Fin m → N) (a b c : Fin m),
        inf σ a b c - inf σ b a c = ad (d a (σ c)) (d b (σ c)))
    ∧ inf crossedScale 0 1 0 - inf crossedScale 1 0 0 ≠ 0
    ∧ Determination.influence Explanation.coupled 0 1 2
        ≠ Determination.influence Explanation.coupled 0 2 1 :=
  ⟨fun σ a b c => influence_asymmetry σ a b c, readings_disagree,
   observer_observed_not_symmetric⟩

end SCD.Triple
