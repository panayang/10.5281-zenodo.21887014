/-
# A1 — the substrate, with one carrier

The substrate of the theory is *not* a metric manifold.  It is a bare affine
counting structure together with the dimensionless log-scale `σ`.

To keep every statement finitary and machine-checkable we model "smooth
functions on the substrate" abstractly: a ring `M` carrying `n` commuting
derivations `∂₀,…,∂_{n-1}`.  Every differential identity used later (Christoffel
symbols, Riemann tensor, the deformation tensor) is then a *purely algebraic*
consequence of the Leibniz rule and the equality of mixed partials.  No analysis
is needed, and nothing is assumed beyond what is written down here.

**One carrier, not two.**  This class was previously declared twice — once here
over a commutative ring as `ScaleAlgebra`, and once in `Connection.lean` over a
ring as `DiffRing` — with an instance and a `def` shuttling between them and a
paragraph in `Postulates.lean` explaining that they were the same axiom.  They
were the same axiom, so there is now one class, stated over a ring, and the
commutative sector is the sector in which the ring happens to be commutative.
Nothing is lost and nothing has to be transported: `Conformal.lean`'s objects
and `NCConformal.lean`'s are now literally the same objects.

**Commutativity of the ring is not part of A1, and commutativity of the
derivations is a chart.**  `Dynamics.no_flatness_from_commuting_derivations`
shows `d_comm` carries no flatness; `Quantum.ad_comm_of_commute` shows it is
exactly the statement that a coordinate system is a choice of commuting
observables.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination
import SCD.Pattern

namespace SCD

open Finset

/-! ## The differential substrate -/

/-- **A1 (Substrate).**  A ring with `n` pairwise-commuting derivations.

No commutativity of the ring is assumed: the commutative case is the classical
sector and the general case is the quantum one, and they are the same axiom.
This is the algebraic shadow of "smooth functions on an `n`-dimensional
coordinate patch". -/
class ScaleAlgebra (n : ℕ) (M : Type*) [Ring M] where
  /-- The `i`-th partial derivative. -/
  d : Fin n → M → M
  d_add : ∀ i a b, d i (a + b) = d i a + d i b
  d_mul : ∀ i a b, d i (a * b) = d i a * b + a * d i b
  d_comm : ∀ i j a, d i (d j a) = d j (d i a)

namespace ScaleAlgebra

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]

attribute [simp] d_add

@[simp] theorem d_zero (i : Fin n) : d (M := M) i 0 = 0 := by
  have h : d (M := M) i (0 + 0) = d (M := M) i 0 + d (M := M) i 0 := d_add i 0 0
  rw [add_zero] at h
  have h' : d (M := M) i 0 + 0 = d (M := M) i 0 + d (M := M) i 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

@[simp] theorem d_one (i : Fin n) : d (M := M) i 1 = 0 := by
  have h : d (M := M) i (1 * 1) = d (M := M) i 1 * 1 + 1 * d (M := M) i 1 := d_mul i 1 1
  rw [one_mul, mul_one, one_mul] at h
  have h' : d (M := M) i 1 + 0 = d (M := M) i 1 + d (M := M) i 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

/-- Each derivation is additive, packaged as a monoid hom so that `map_sum`
applies. -/
def dHom (i : Fin n) : M →+ M where
  toFun := d i
  map_zero' := d_zero i
  map_add' := d_add i

@[simp] theorem d_neg (i : Fin n) (a : M) : d i (-a) = -d i a :=
  map_neg (dHom (M := M) i) a

@[simp] theorem d_sub (i : Fin n) (a b : M) : d i (a - b) = d i a - d i b :=
  map_sub (dHom (M := M) i) a b

theorem d_sum {ι : Type*} (s : Finset ι) (f : ι → M) (i : Fin n) :
    d i (∑ x ∈ s, f x) = ∑ x ∈ s, d i (f x) :=
  map_sum (dHom (M := M) i) f s

/-- Constants (integer multiples of `1`) are annihilated by every derivation. -/
@[simp] theorem d_natCast (i : Fin n) (k : ℕ) : d (M := M) i (k : M) = 0 := by
  induction k with
  | zero => simp
  | succ m ih => push_cast; simp only [d_add, ih, d_one, add_zero]

@[simp] theorem d_nsmul (i : Fin n) (k : ℕ) (a : M) : d i ((k : M) * a) = (k : M) * d i a := by
  rw [d_mul, d_natCast, zero_mul, zero_add]

end ScaleAlgebra

/-! ## Kronecker delta

The bare Euclidean bookkeeping.  It is a cast of `0` or `1`, hence **central**:
every step that only moves a `kron` through a product is valid in the
non-commutative sector unchanged, which is why the curvature computation
survives the passage to the quantum case. -/

open ScaleAlgebra

section Kron

variable {n : ℕ} {M : Type*} [Ring M]

/-- The Kronecker delta, valued in the ring `M`.  It is the *bare* Euclidean
metric: pure bookkeeping, carrying no physics. -/
def kron (i j : Fin n) : M := if i = j then 1 else 0

@[simp] theorem kron_self (i : Fin n) : (kron i i : M) = 1 := by simp [kron]

theorem kron_symm (i j : Fin n) : (kron i j : M) = kron j i := by
  simp only [kron]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- **The bookkeeping is central.**  Being a cast of `0` or `1`, a Kronecker
delta commutes with everything, in any ring. -/
theorem kron_comm (i j : Fin n) (x : M) : (kron i j : M) * x = x * kron i j := by
  simp only [kron]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]; simp

/-- Two delta-prefixed factors can be collected on the left without disturbing
the order of the ring elements. -/
theorem kron_swap (i j p q : Fin n) (x : M) :
    (kron i j : M) * ((kron p q : M) * x) = (kron p q : M) * ((kron i j : M) * x) := by
  rw [← mul_assoc, ← mul_assoc, kron_comm i j (kron p q : M)]

theorem kron_mul_kron_mul (i j p q : Fin n) (x y : M) :
    ((kron i j : M) * x) * ((kron p q : M) * y) = ((kron i j : M) * (kron p q : M)) * (x * y) := by
  rw [mul_assoc, ← mul_assoc x, ← kron_comm p q x, mul_assoc, ← mul_assoc]

/-! ### Contraction primitives

These are the only facts about `kron` the curvature computation needs, and none
of them uses commutativity of the ring. -/

@[simp] theorem sum_kron_left (b : Fin n) (f : Fin n → M) :
    ∑ a, (kron a b : M) * f a = f b := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp only [kron, if_neg hc, zero_mul]
  · intro h; exact absurd (Finset.mem_univ b) h

@[simp] theorem sum_kron_right (b : Fin n) (f : Fin n → M) :
    ∑ a, (kron b a : M) * f a = f b := by
  rw [Finset.sum_congr rfl (fun a _ => by rw [kron_symm b a])]
  exact sum_kron_left b f

/-- A constant summed over `Fin m`. -/
theorem sum_const_fin (m : ℕ) (c : M) : ∑ _a : Fin m, c = (m : M) * c := by
  simp [Finset.sum_const, nsmul_eq_mul]

end Kron

section KronDiff

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]

@[simp] theorem d_kron (k i j : Fin n) : d (M := M) k (kron i j) = 0 := by
  simp only [kron]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]; simp

@[simp] theorem d_kron_mul (k i j : Fin n) (a : M) :
    d k ((kron i j : M) * a) = (kron i j : M) * d k a := by
  rw [d_mul, d_kron, zero_mul, zero_add]

end KronDiff

end SCD
