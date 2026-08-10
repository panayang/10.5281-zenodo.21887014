/-
# Scale Universe — Foundations

The substrate of the theory is *not* a metric manifold.  It is a bare affine
(Euclidean) counting structure together with a single dimensionless scalar
field `σ`, the **log-scale**.

To keep every statement finitary and machine-checkable we model "smooth
functions on the substrate" abstractly: a commutative ring `A` carrying `n`
commuting derivations `∂₀,…,∂_{n-1}`.  Every differential identity used later
(Christoffel symbols, Riemann tensor, Weyl curvature of the scale connection)
is then a *purely algebraic* consequence of the Leibniz rule and the equality
of mixed partials.  No analysis is needed, and nothing is assumed beyond what
is written down here.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace SCD

open Finset

/-! ## The differential substrate -/

/-- A commutative ring with `n` pairwise-commuting derivations.

This is the algebraic shadow of "smooth functions on an `n`-dimensional
Euclidean coordinate patch". -/
class ScaleAlgebra (n : ℕ) (A : Type*) [CommRing A] where
  /-- The `i`-th partial derivative. -/
  d : Fin n → A → A
  d_add : ∀ i a b, d i (a + b) = d i a + d i b
  d_mul : ∀ i a b, d i (a * b) = d i a * b + a * d i b
  d_comm : ∀ i j a, d i (d j a) = d j (d i a)

namespace ScaleAlgebra

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

attribute [simp] d_add

@[simp] theorem d_zero (i : Fin n) : d (A := A) i 0 = 0 := by
  have h : d (A := A) i (0 + 0) = d (A := A) i 0 + d (A := A) i 0 := d_add i 0 0
  rw [add_zero] at h
  have h' : d (A := A) i 0 + 0 = d (A := A) i 0 + d (A := A) i 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

@[simp] theorem d_one (i : Fin n) : d (A := A) i 1 = 0 := by
  have h : d (A := A) i (1 * 1) = d (A := A) i 1 * 1 + 1 * d (A := A) i 1 := d_mul i 1 1
  rw [one_mul, mul_one, one_mul] at h
  have h' : d (A := A) i 1 + 0 = d (A := A) i 1 + d (A := A) i 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

/-- Each derivation is additive, packaged as a monoid hom so that `map_sum`
applies. -/
def dHom (i : Fin n) : A →+ A where
  toFun := d i
  map_zero' := d_zero i
  map_add' := d_add i


@[simp] theorem d_neg (i : Fin n) (a : A) : d i (-a) = -d i a :=
  map_neg (dHom (A := A) i) a

@[simp] theorem d_sub (i : Fin n) (a b : A) : d i (a - b) = d i a - d i b :=
  map_sub (dHom (A := A) i) a b

theorem d_sum {ι : Type*} (s : Finset ι) (f : ι → A) (i : Fin n) :
    d i (∑ x ∈ s, f x) = ∑ x ∈ s, d i (f x) :=
  map_sum (dHom (A := A) i) f s

/-- Constants (integer multiples of `1`) are annihilated by every derivation. -/
@[simp] theorem d_natCast (i : Fin n) (k : ℕ) : d (A := A) i (k : A) = 0 := by
  induction k with
  | zero => simpa using d_zero (A := A) i
  | succ m ih => push_cast; simp [ih]

@[simp] theorem d_nsmul (i : Fin n) (k : ℕ) (a : A) : d i ((k : A) * a) = (k : A) * d i a := by
  rw [d_mul, d_natCast]; ring

end ScaleAlgebra

/-! ## Kronecker delta -/

open ScaleAlgebra

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-- The Kronecker delta, valued in the ring `A`.  It is the *bare* Euclidean
metric: pure bookkeeping, carrying no physics. -/
def kron (i j : Fin n) : A := if i = j then 1 else 0

@[simp] theorem kron_self (i : Fin n) : (kron i i : A) = 1 := by simp [kron]

theorem kron_symm (i j : Fin n) : (kron i j : A) = kron j i := by
  simp only [kron]; by_cases h : i = j <;> simp [h, eq_comm]

@[simp] theorem d_kron (k i j : Fin n) : d (A := A) k (kron i j) = 0 := by
  simp only [kron]; by_cases h : i = j <;> simp [h]

@[simp] theorem d_kron_mul (k i j : Fin n) (a : A) :
    d k ((kron i j : A) * a) = (kron i j : A) * d k a := by
  rw [d_mul, d_kron]; ring

/-! ### Contraction primitives

These four lemmas are the only facts about `kron` that the curvature
computation needs. -/

@[simp] theorem sum_kron_left (b : Fin n) (f : Fin n → A) :
    ∑ a, (kron a b : A) * f a = f b := by
  simp only [kron, ite_mul, one_mul, zero_mul]
  simp

@[simp] theorem sum_kron_right (b : Fin n) (f : Fin n → A) :
    ∑ a, (kron b a : A) * f a = f b := by
  simp only [kron, ite_mul, one_mul, zero_mul]
  simp



end SCD
