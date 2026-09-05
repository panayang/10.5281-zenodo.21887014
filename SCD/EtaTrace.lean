/-
# The coefficient survives the signature, and the operator does not

§V.au found `κ = −2(n−1)Δ` derived in the `δ` sector while the observables live
in the `η` sector, and named the repair: **redo `RscBare_eq` with an `η`-weighted
trace and see whether `−2(n−1)` survives.**  This file does it.

## The result

`RscE_eq`:

        Rsc_η = −2(n−1)·□σ − (n−1)(n−2)·|∇σ|²_η

with `□σ = ∑ᵢ ηᵢ σᵢᵢ` and `|∇σ|²_η = ∑ᵢ ηᵢ σᵢσᵢ`.  **Identical coefficients.**
`A6'_from_index_eta` then gives `κ = −2(n−1)Δ` again.

> **The number is safe.  What is not safe is the operator it multiplies.**

The whole computation is redone from the connection up — `ChrE`, `RmE`, `RicE`,
`RscE` — because inserting `η` into the final trace alone would not be the same
geometry.  The connection is the one `Anisotropic.ChrDir` already had, at the
isotropic locus with `η` left general: the case that existed and was never
computed.

## What made it work, and it is not a coincidence

In `sum_ChrE_ChrE`, two `η`-carrying terms cancel identically — the one from
`Γ^a_{cm}` meeting `Γ^m_{be}`'s trace part, and the one from the two `η`-terms
meeting each other, which carries `ηₑηₑ = 1`.  That cancellation is why the
signature cannot reach the coefficient.  Every surviving `η` appears either
squared (hence `1`) or attached to a `δ` that forces its two indices equal.

## The consequence, which is the real content

A6″ reads `lap σ = Δ·ν`.  In the `δ` sector `lap` is `∑ᵢ σᵢᵢ`, an **elliptic**
operator, and the source law is Poisson's equation.  In the sector the physics
actually uses, the operator is `lapE`, and `lapE_lorentzian_split` says what that
is:

        □σ = ∑_{i≠t} σᵢᵢ − σₜₜ ,

the **d'Alembertian**.  `lap_sub_lapE` measures the gap: `∑ᵢ (1−ηᵢ)σᵢᵢ`, which is
`2σₜₜ` for one timelike direction and zero only if the signature is Euclidean.

So the corrected source law is **hyperbolic**, not elliptic:

        □σ = Δ·ν .

That is a wave equation with a source, not Poisson's equation.  The Newtonian
limit is recovered the usual way — static configurations, where `σₜₜ = 0` and the
d'Alembertian *is* the Laplacian — and the framework's gravity results are all
static (`Diagonal.lean` computes under staticity, and `Ordering.lean` already
found the static case is where the operator ordering stops mattering).

## Status of the repair

**Done:** the `η`-weighted curvature identity, so §V.au's question is answered and
the answer is that `κ` is unharmed.

**Not done:** joining this to `Diagonal.lean`'s anisotropic `Ric η w σ`.  That
computation carries a scale **per direction** (`w`) as well as `η`; this file is
the isotropic locus of it.  So §V.au's disconnect is narrowed, not closed: the
coupling and the observables now live in the same *signature*, and still not
demonstrably in the same *geometry*.

**And one thing is now visibly wrong in the older text.**  `Index.lean` presents
A6″ as an equation about `lap`, and the register has read the Newtonian limit off
it directly.  With the operator hyperbolic, "Poisson's equation" is the static
limit of the source law rather than the law, and `Index.poisson_from_index`
should be read as scoped to static configurations.  Nothing computed from it
changes; what changes is what it is a limit of.
-/
import SCD.Conformal

namespace SCD.EtaTrace

open SCD ScaleAlgebra Finset

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]


/-- The conformal connection of `g = e^{2σ}η`.

This is `Anisotropic.ChrDir` at the isotropic locus with `η` left general — the
case that existed in the development and was never computed. -/
def ChrE (η : Fin n → A) (σ : A) (a b c : Fin n) : A :=
  (kron a b : A) * sig σ c + (kron a c : A) * sig σ b
    - (kron b c : A) * (η b * η a) * sig σ a

/-- Riemann, from that connection. -/
def RmE (η : Fin n → A) (σ : A) (a b c e : Fin n) : A :=
  d c (ChrE η σ a b e) - d e (ChrE η σ a b c)
    + ∑ m, (ChrE η σ a c m * ChrE η σ m b e - ChrE η σ a e m * ChrE η σ m b c)

/-- Ricci, from that Riemann. -/
def RicE (η : Fin n → A) (σ : A) (b e : Fin n) : A := ∑ a, RmE η σ a b a e

variable (n) in
/-- The **d'Alembertian**: the `η`-weighted trace of the Hessian. -/
def lapE (η : Fin n → A) (σ : A) : A := ∑ i : Fin n, η i * hess σ i i

variable (n) in
/-- The `η`-weighted squared gradient. -/
def gradsqE (η : Fin n → A) (σ : A) : A := ∑ i : Fin n, η i * (sig σ i * sig σ i)

variable (n) in
/-- The **`η`-trace** of Ricci — the scalar `Conformal.RscBare` should have been,
in the sector the physics uses. -/
def RscE (η : Fin n → A) (σ : A) : A := ∑ b : Fin n, η b * RicE η σ b b

omit [ScaleAlgebra n A] in
theorem kron_mul_eta (η : Fin n → A) (b e : Fin n) :
    (kron b e : A) * η b = (kron e b : A) * η e := by
  by_cases h : b = e
  · subst h; rfl
  · simp only [show (kron b e : A) = 0 from if_neg h,
      show (kron e b : A) = 0 from if_neg (Ne.symm h), zero_mul]

theorem sum_mul_lapE (η : Fin n → A) (σ c : A) :
    ∑ i : Fin n, c * (η i * hess σ i i) = c * lapE n η σ := by
  rw [lapE, Finset.mul_sum]

theorem sum_mul_gradsqE (η : Fin n → A) (σ c : A) :
    ∑ i : Fin n, c * (η i * (sig σ i * sig σ i)) = c * gradsqE n η σ := by
  rw [gradsqE, Finset.mul_sum]

section
variable (η : Fin n → A) (hη : ∀ a, η a * η a = 1) (hηc : ∀ a b : Fin n, d b (η a) = 0)

theorem ChrE_symm (σ : A) (a b c : Fin n) : ChrE η σ a b c = ChrE η σ a c b := by
  by_cases h : b = c
  · subst h; rfl
  · simp only [ChrE, show (kron b c : A) = 0 from if_neg h,
      show (kron c b : A) = 0 from if_neg (Ne.symm h)]
    ring

include hη

theorem sum_ChrE_diag (σ : A) (m : Fin n) : ∑ a, ChrE η σ a a m = (n : A) * sig σ m := by
  have h : ∀ a : Fin n, ChrE η σ a a m = sig σ m := by
    intro a
    simp only [ChrE, kron_self, one_mul, kron_symm a m]
    by_cases hb : m = a
    · subst hb; simp only [kron_self, one_mul]; rw [hη]; ring
    · simp only [show (kron m a : A) = 0 from if_neg hb]; ring
  rw [Finset.sum_congr rfl (fun a _ => h a), sum_const_fin]

theorem sum_ChrETrace_ChrE (σ : A) (b e : Fin n) :
    ∑ m, ((n : A) * sig σ m) * ChrE η σ m b e
      = (n : A) * (2 * (sig σ b * sig σ e)) - ((kron b e : A) * ((n : A) * η b)) * gradsqE n η σ := by
  have h : ∀ m : Fin n, ((n : A) * sig σ m) * ChrE η σ m b e
      = (kron m b : A) * ((n : A) * (sig σ e * sig σ m))
        + (kron m e : A) * ((n : A) * (sig σ b * sig σ m))
        - ((kron b e : A) * ((n : A) * η b)) * (η m * (sig σ m * sig σ m)) := by
    intro m; simp only [ChrE]; ring
  rw [Finset.sum_congr rfl (fun m _ => h m)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_kron_left,
    sum_mul_gradsqE]
  ring

/-- **The step where the signature would have entered, and does not.**

Two `η`-carrying terms cancel identically: the one from `Γ^a_{cm}` against the one
where both `η`-terms meet, which carries `ηₑηₑ = 1`.  Every surviving `η` is either
squared or pinned by a `δ`. -/
theorem sum_ChrE_ChrE (σ : A) (b e : Fin n) :
    ∑ a, ∑ m, ChrE η σ a e m * ChrE η σ m b a
      = ((n : A) + 2) * (sig σ b * sig σ e)
        - 2 * (((kron b e : A) * η b) * gradsqE n η σ) := by
  have inner : ∀ a : Fin n, ∑ m, ChrE η σ a e m * ChrE η σ m b a
      = (kron a e : A) * (2 * (sig σ b * sig σ a))
        - (kron a e : A) * (((kron b a : A) * η b) * gradsqE n η σ)
        + (kron a b : A) * (sig σ e * sig σ a)
        + (sig σ b * sig σ e)
        - ((kron e b : A) * η e) * (η a * (sig σ a * sig σ a))
        - (kron e a : A) * ((η e * η a) * (sig σ a * sig σ b)) := by
    intro a
    have h : ∀ m : Fin n, ChrE η σ a e m * ChrE η σ m b a
        = (kron m b : A) * ((kron a e : A) * (sig σ m * sig σ a))
          + (kron m a : A) * ((kron a e : A) * (sig σ m * sig σ b))
          - ((kron a e : A) * ((kron b a : A) * η b)) * (η m * (sig σ m * sig σ m))
          + (kron a m : A) * ((kron m b : A) * (sig σ e * sig σ a))
          + (kron a m : A) * ((kron m a : A) * (sig σ e * sig σ b))
          - (kron a m : A) * (((kron b a : A) * η b) * (η m * (sig σ e * sig σ m)))
          - (kron e m : A) * ((kron m b : A) * ((η e * η a) * (sig σ a * sig σ a)))
          - (kron e m : A) * ((kron m a : A) * ((η e * η a) * (sig σ a * sig σ b)))
          + (kron e m : A) * ((kron b a : A) * ((η e * η a) * (η b * (η m * (sig σ a * sig σ m))))) := by
      intro m; simp only [ChrE]; ring
    rw [Finset.sum_congr rfl (fun m _ => h m)]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_kron_left,
      sum_kron_right, sum_mul_gradsqE, kron_self, one_mul, mul_one]
    linear_combination ((kron b a : A) * (η a * η b) * (sig σ a * sig σ e)) * hη e
  rw [Finset.sum_congr rfl (fun a _ => inner a)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_kron_left,
    sum_kron_right, sum_mul_gradsqE, sum_const_fin, kron_self, one_mul, mul_one]
  rw [kron_mul_eta η b e]
  linear_combination (- (sig σ e * sig σ b)) * hη e

include hηc

theorem sum_d_ChrE (σ : A) (b e : Fin n) :
    ∑ a, d a (ChrE η σ a b e)
      = 2 * hess σ b e - ((kron b e : A) * η b) * lapE n η σ := by
  have h : ∀ a : Fin n, d a (ChrE η σ a b e)
      = (kron a b : A) * hess σ a e + (kron a e : A) * hess σ a b
        - ((kron b e : A) * η b) * (η a * hess σ a a) := by
    intro a
    simp only [ChrE, d_sub, d_add, d_mul, hηc, d_kron, hess, sig]
    ring
  rw [Finset.sum_congr rfl (fun a _ => h a)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_kron_left, sum_mul_lapE]
  rw [hess_symm σ e b]
  ring

theorem sum_d_ChrE_trace (σ : A) (b e : Fin n) :
    ∑ a, d e (ChrE η σ a b a) = (n : A) * hess σ e b := by
  have h : ∀ a : Fin n, d e (ChrE η σ a b a) = d e (ChrE η σ a a b) := by
    intro a; rw [ChrE_symm η]
  rw [Finset.sum_congr rfl (fun a _ => h a), ← d_sum, sum_ChrE_diag η hη, d_nsmul]
  rfl

/-- **Ricci, in closed form** — `Conformal.Ric_eq` with `η_b` on the trace term
and nothing else changed. -/
theorem RicE_eq (σ : A) (b e : Fin n) :
    RicE η σ b e
      = -((n : A) - 2) * (hess σ b e - sig σ b * sig σ e)
        - ((kron b e : A) * η b) * (lapE n η σ + ((n : A) - 2) * gradsqE n η σ) := by
  have hsplit : RicE η σ b e
      = (∑ a, d a (ChrE η σ a b e)) - (∑ a, d e (ChrE η σ a b a))
        + ((∑ a, ∑ m, ChrE η σ a a m * ChrE η σ m b e)
            - ∑ a, ∑ m, ChrE η σ a e m * ChrE η σ m b a) := by
    simp only [RicE, RmE, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hdiag : (∑ a, ∑ m, ChrE η σ a a m * ChrE η σ m b e)
      = (n : A) * (2 * (sig σ b * sig σ e))
        - ((kron b e : A) * ((n : A) * η b)) * gradsqE n η σ := by
    rw [Finset.sum_comm]
    have h : ∀ m : Fin n, ∑ a, ChrE η σ a a m * ChrE η σ m b e
        = ((n : A) * sig σ m) * ChrE η σ m b e := by
      intro m; rw [← Finset.sum_mul, sum_ChrE_diag η hη]
    rw [Finset.sum_congr rfl (fun m _ => h m)]
    exact sum_ChrETrace_ChrE η hη σ b e
  rw [hsplit, sum_d_ChrE η hη hηc, sum_d_ChrE_trace η hη hηc, hdiag,
    sum_ChrE_ChrE η hη, hess_symm σ e b]
  ring

/-- **The coefficient survives the signature.** -/
theorem RscE_eq (σ : A) :
    RscE n η σ
      = -2 * ((n : A) - 1) * lapE n η σ
        - ((n : A) - 1) * ((n : A) - 2) * gradsqE n η σ := by
  have h : ∀ b : Fin n, η b * RicE η σ b b
      = (-((n : A) - 2)) * (η b * hess σ b b)
        + ((n : A) - 2) * (η b * (sig σ b * sig σ b))
        - (lapE n η σ + ((n : A) - 2) * gradsqE n η σ) := by
    intro b
    rw [RicE_eq η hη hηc, kron_self]
    linear_combination (- (lapE n η σ + ((n : A) - 2) * gradsqE n η σ)) * hη b
  rw [RscE, Finset.sum_congr rfl (fun b _ => h b)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_mul_lapE,
    sum_mul_gradsqE, sum_const_fin]
  ring

/-- **So the coupling is unchanged, with the d'Alembertian in place of the
Laplacian.** -/
theorem A6'_from_index_eta (Δ ν σ : A) (hlin : gradsqE n η σ = 0)
    (hsrc : lapE n η σ = Δ * ν) :
    RscE n η σ = (-2 * ((n : A) - 1) * Δ) * ν := by
  rw [RscE_eq η hη hηc, hlin, hsrc]
  ring

omit hη hηc in
/-- **But the operator is not the same one.** -/
theorem lap_sub_lapE (σ : A) :
    lap n σ - lapE n η σ = ∑ i : Fin n, (1 - η i) * hess σ i i := by
  simp only [lap, lapE, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

omit hη hηc in
/-- **And with a Lorentzian signature it is hyperbolic.** -/
theorem lapE_lorentzian_split (t : Fin n) (ht : η t = -1)
    (hrest : ∀ i, i ≠ t → η i = 1) (σ : A) :
    lapE n η σ = (∑ i ∈ Finset.univ.erase t, hess σ i i) - hess σ t t := by
  rw [lapE, ← Finset.add_sum_erase _ _ (Finset.mem_univ t), ht]
  have h : ∀ i ∈ Finset.univ.erase t, η i * hess σ i i = hess σ i i := by
    intro i hi
    rw [hrest i (Finset.ne_of_mem_erase hi), one_mul]
  rw [Finset.sum_congr rfl h]
  ring


end

end SCD.EtaTrace
