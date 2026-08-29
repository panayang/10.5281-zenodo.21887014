/-
# What the axioms do **not** say about signs

General relativity forbids traversable wormholes, closed timelike curves and a
great deal else by imposing **energy conditions** — inequalities on the source.
Those inequalities are inputs; they are not consequences of the field equations,
and no experiment has ever tested the null energy condition directly.

This framework does not have them, and that fact should be on record as a
theorem rather than as an absence anyone has to notice for themselves.  Two
statements, of different strengths:

**At the level of types.**  A1 asks for a `Ring`.  It does not ask for an
ordered ring, so "positive" is not a predicate the axioms can even form.  This
is visible in the signature of `ScaleAlgebra` and needs no proof — but it is
also cheap, because one could answer "the physical models are real anyway".

**At the level of models.**  So the substantive statement is the one below.
`ℝ[X]` with `d/dX` along one direction and zero along the rest is a model of A1
over an *ordered* ring, and in it the deformation tensor contracted with a
**fixed null direction** takes strictly positive values for one scale field and
strictly negative values for another.

`no_null_energy_condition`.  Hence **no inequality of the form `D(v,v) ≥ 0` for
null `v` is a consequence of A1–A5**, and any argument that helps itself to one
is importing it.

## What this does and does not license

It does **not** predict that exotic configurations occur.  Producing one from a
source needs the scale response law, and that law is the framework's registered
external input (`Audit.lean` §V).  What it licenses is the refusal to assume the
opposite: statements like "wormholes here must be non-traversable" or "the
scale well must deepen rather than shallow" are **not** derivable, and treating
them as results to be recovered would be exactly the theory inertia the register
warns about — the more so because they are untested.

The honest position is: the sign is open, and what decides it is the source law.
That is why `Well.lean` states both branches and commits to neither.

## And what the source law then puts back

**Scope, added after `Index.lean` and `Attraction.lean`.**  The statement above
is about **A1–A7**, and it stays true of them.  But adopting the index form of
the source law reintroduces a condition of the same *kind*: `Attraction.lean`
argues `ν` is a threshold count, hence non-negative, hence the source has one
sign — and `Attraction.counting_bound` bounds the relative source below by minus
the background.

So the framework does not end up without an energy-condition-like restriction.
It ends up with a **combinatorial** one, entering through the source law rather
than through the axioms, and saturated by an empty region rather than by exotic
matter.  Read this file as "the axioms do not supply one", not as "the framework
has none".
-/
import SCD.Conformal
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace SCD.Positivity

open SCD ScaleAlgebra Polynomial Finset

/-! ## A model of A1 over an ordered ring

`ℝ[X]` with `d/dX` along direction `0` and the zero derivation along every
other.  The Leibniz rule and equality of mixed partials both hold trivially off
the first direction, so this is a model of A1 for **every** `n`, and it is a
model over a ring that carries an order — which is what makes the sign
statements below say something. -/

/-- A1 on `ℝ[X]`: one live direction, `n − 1` dead ones. -/
@[reducible] noncomputable def oneAxis (n : ℕ) : ScaleAlgebra n (Polynomial ℝ) where
  d := fun i p => if (i : ℕ) = 0 then Polynomial.derivative p else 0
  d_add := by
    intro i a b
    by_cases h : (i : ℕ) = 0 <;> simp [h]
  d_mul := by
    intro i a b
    by_cases h : (i : ℕ) = 0 <;> simp [h, Polynomial.derivative_mul]
  d_comm := by
    intro i j a
    by_cases hi : (i : ℕ) = 0 <;> by_cases hj : (j : ℕ) = 0 <;> simp [hi, hj]

attribute [local instance] oneAxis

/-! ## The derived quantities in this model -/

variable (σ : Polynomial ℝ)

@[simp] theorem sig_zero : sig (n := 4) σ 0 = derivative σ := rfl

theorem sig_succ (i : Fin 4) (hi : (i : ℕ) ≠ 0) : sig (n := 4) σ i = 0 := if_neg hi

theorem gradsq_eq : gradsq 4 σ = derivative σ * derivative σ := by
  simp only [gradsq, Fin.sum_univ_four]
  rw [sig_succ σ 1 (by decide), sig_succ σ 2 (by decide), sig_succ σ 3 (by decide)]
  simp only [sig_zero, mul_zero, add_zero]

theorem hess_zero_zero : hess (n := 4) σ 0 0 = derivative (derivative σ) := rfl

theorem hess_off (i j : Fin 4) (h : (i : ℕ) ≠ 0 ∨ (j : ℕ) ≠ 0) :
    hess (n := 4) σ i j = 0 := by
  rcases h with h | h
  · exact if_neg h
  · show d i (sig (n := 4) σ j) = 0
    rw [sig_succ σ j h, d_zero]

/-! ## The null contraction

Signature `η = (−1, 1, 1, 1)` makes `v = (1, 1, 0, 0)` a null direction of the
bare bookkeeping.  Contracting the deformation tensor with it gives `2σ''` — the
`|∇σ|²` terms cancel between the temporal and the spatial diagonal, which is
exactly why the contraction is sensitive to the *sign* of the second derivative
and to nothing else. -/

/-- The null direction used throughout. -/
def nullDir : Fin 4 → ℝ := ![1, 1, 0, 0]

/-- It is null for the bare form with signature `(−,+,+,+)`. -/
theorem nullDir_is_null :
    ∑ i, (![(-1 : ℝ), 1, 1, 1] i) * (nullDir i * nullDir i) = 0 := by
  simp [nullDir, Fin.sum_univ_four]

/-- The deformation tensor contracted with the null direction. -/
noncomputable def nullContract (σ : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i, ∑ j, (Polynomial.C (nullDir i) * Polynomial.C (nullDir j)) * Defm 4 σ i j

/-- **The contraction is `2σ''`.**  The gradient-squared terms cancel exactly
between `D₀₀` and `D₁₁`, so the whole of it is the second derivative — an
unconstrained element of the ring. -/
theorem nullContract_eq : nullContract σ = 2 * derivative (derivative σ) := by
  have h00 : Defm 4 σ 0 0 = 2 * derivative (derivative σ) - derivative σ * derivative σ := by
    simp only [Defm, hess_zero_zero, sig_zero, kron_self, one_mul, gradsq_eq]
    ring
  have h01 : Defm 4 σ 0 1 = 0 := by
    simp only [Defm, hess_off σ 0 1 (Or.inr (by decide)), sig_zero,
      sig_succ σ 1 (by decide), kron, if_neg (by decide : ¬((0 : Fin 4) = 1))]
    ring
  have h10 : Defm 4 σ 1 0 = 0 := by
    simp only [Defm, hess_off σ 1 0 (Or.inl (by decide)), sig_zero,
      sig_succ σ 1 (by decide), kron, if_neg (by decide : ¬((1 : Fin 4) = 0))]
    ring
  have h11 : Defm 4 σ 1 1 = derivative σ * derivative σ := by
    simp only [Defm, hess_off σ 1 1 (Or.inl (by decide)), sig_succ σ 1 (by decide),
      kron_self, one_mul, gradsq_eq]
    ring
  simp only [nullContract, Fin.sum_univ_four, nullDir]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  simp only [map_one, map_zero, one_mul, mul_one, zero_mul, mul_zero, add_zero]
  rw [h00, h01, h10, h11]
  ring

/-! ## Both signs occur -/

/-- A scale field whose null contraction is strictly positive. -/
theorem nullContract_pos : (nullContract (X ^ 2)).eval 0 = 4 := by
  rw [nullContract_eq]
  simp
  norm_num

/-- And one whose null contraction is strictly negative — the *same* null
direction, the *same* model of A1. -/
theorem nullContract_neg : (nullContract (-(X ^ 2))).eval 0 = -4 := by
  rw [nullContract_eq]
  simp
  norm_num

/-- **There is no null energy condition.**

In one model of A1, over an ordered ring, with one fixed null direction, the
deformation tensor's null contraction takes a strictly positive value on one
scale field and a strictly negative value on another.

So no inequality `D(v,v) ≥ 0` on null `v` follows from A1–A5, and every
consequence usually drawn from such an inequality — the singularity theorems,
the topological censorship theorems, the non-traversability of wormholes — is
**unavailable here as a derivation**.  Whether the framework nonetheless forbids
those things is a question about the scale response law, not about the axioms,
and it is open. -/
theorem no_null_energy_condition :
    (0 : ℝ) < (nullContract (X ^ 2)).eval 0
    ∧ (nullContract (-(X ^ 2))).eval 0 < 0
    ∧ ∑ i, (![(-1 : ℝ), 1, 1, 1] i) * (nullDir i * nullDir i) = 0 := by
  refine ⟨?_, ?_, nullDir_is_null⟩
  · rw [nullContract_pos]; norm_num
  · rw [nullContract_neg]; norm_num

/-! ## The scale itself is unbounded in both directions

The other half of the same point.  A2 makes `s` a **unit**, which forbids `0`
and forbids nothing else: there is no smallest scale and no largest one, and in
particular no bound preventing a local unit from being as small as one likes.

`Horizon.lean` states the no-minimum-length conclusion; this states the premise
in the form the wormhole question needs. -/

/-- **A local unit can be arbitrarily small, and is never zero.**

For any target `ε > 0` there is a legitimate scale strictly between `0` and `ε`.
So "the throat is short" is always available; "the throat has zero length" never
is. -/
theorem scale_small_but_nonzero (ε : ℝ) (hε : 0 < ε) :
    ∃ u : ℝˣ, 0 < (u : ℝ) ∧ (u : ℝ) < ε := by
  refine ⟨Units.mk0 (ε / 2) (by positivity), ?_, ?_⟩
  · simpa using by positivity
  · simpa using by linarith

/-- And symmetrically it can be arbitrarily large: nothing in A2 bounds the
scale on either side, so both branches of `Well.lean` are populated. -/
theorem scale_large (M : ℝ) (hM : 0 < M) : ∃ u : ℝˣ, M < (u : ℝ) := by
  refine ⟨Units.mk0 (M + 1) (by positivity), ?_⟩
  simp

end SCD.Positivity
