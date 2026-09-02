/-
# Inexactness in more than one direction

`Gradient.lean` measured what A2 assumes and closed with a list of costs.  The
first was withdrawn in the same file: `logDeriv_closed` shows the gradient of a
unit is closed for every unit, so symmetry of the Hessian survives with no
hypothesis.  What that leaves is a single distinction —

> **exactness is the whole of what A2 adds to "the scale is a unit"** —

and a single reservation about it: `Circle.lean`'s inexact gradient lives at one
direction, where a great deal is degenerate.  This file removes the reservation.

## The construction

`Tor n` is the group algebra of `ℤⁿ` over `ℝ`: trigonometric polynomials on the
`n`-torus, `Σ c_α u^α`.  `dtor i` multiplies `u^α` by the `i`-th exponent, which
is `∂/∂θᵢ`, and the derivations commute because each is multiplication by a
component of the same exponent.  `torScaleAlgebra` is A1 at every `n`.

`uTor α` is the unit `u^α`, whose logarithmic derivative is the constant vector
`α` (`dtor_uTor`).  `dtor_coeff_zero` says every derivative has vanishing
constant term in every direction, so `no_potential_tor` — **a non-zero constant
is not a derivative**, whatever the dimension.

## What it settles

`torGradient α` is a scale gradient, and `torGradient_not_isExact` makes it
inexact as soon as the winding is non-zero in any one direction.  `twoTorus`
is the smallest case that was missing: two directions, `s = u`, gradient
`(1, 0)`, and no potential.

So the `ℝ`/`𝕋` split of A3′ is **not an artefact of one dimension**.  Together
with `logDeriv_closed` that gives the axiom question its final shape:

* closedness — automatic, for every unit, in every dimension;
* exactness — fails, for a unit, in every dimension.

A2 assumes the second.  Nothing in A1–A7 supplies it, and `Dual.lean` says the
branch where it fails is the one gravity selects.

## What it does not do

It supplies a family of inexact scale gradients and nothing else.  There is no
map here to `Defect.ScaleDefect` — `Circle.lean` has one at `n = 1` and the
higher-dimensional analogue would need the winding of a `ℤⁿ` class, which is a
different invariant.  No dynamics is run on any of these, and there is still no
vacuum solution.
-/
import SCD.Gradient

namespace SCD.Torus

open AddMonoidAlgebra SCD


open AddMonoidAlgebra SCD

/-- Trigonometric polynomials on the `n`-torus: `Σ c_α u^α` with `α ∈ ℤⁿ`. -/
abbrev Tor (n : ℕ) := AddMonoidAlgebra ℝ (Fin n → ℤ)

variable {n : ℕ}

/-- `∂/∂θᵢ`: on `u^α` it is multiplication by the `i`-th exponent. -/
noncomputable def dtor (i : Fin n) (f : Tor n) : Tor n :=
  f.coeff.sum fun α c => single α ((α i : ℝ) * c)

@[simp] theorem dtor_single (i : Fin n) (α : Fin n → ℤ) (c : ℝ) :
    dtor i (single α c) = single α ((α i : ℝ) * c) := by
  simp only [dtor, coeff_single]
  rw [Finsupp.sum_single_index]
  simp

@[simp] theorem dtor_zero (i : Fin n) : dtor i (0 : Tor n) = 0 := by simp [dtor]

theorem dtor_add (i : Fin n) (f g : Tor n) : dtor i (f + g) = dtor i f + dtor i g := by
  simp only [dtor, AddMonoidAlgebra.coeff_add]
  rw [Finsupp.sum_add_index']
  · intro α; simp
  · intro α a b; rw [← single_add]; congr 1; ring

theorem induction_single {motive : Tor n → Prop} (f : Tor n)
    (h0 : motive 0) (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsingle : ∀ α c, motive (single α c)) : motive f := by
  have key : ∀ c : (Fin n → ℤ) →₀ ℝ, motive (ofCoeff c) := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => exact h0
    | add f g hf hg => exact hadd _ _ hf hg
    | single a b => exact hsingle a b
  exact key f.coeff

theorem dtor_mul (i : Fin n) (f g : Tor n) :
    dtor i (f * g) = dtor i f * g + f * dtor i g := by
  induction f using induction_single with
  | h0 => simp
  | hadd x y hx hy => rw [add_mul, dtor_add, dtor_add, hx, hy, add_mul]; ring
  | hsingle α a =>
    induction g using induction_single with
    | h0 => simp
    | hadd x y hx hy => rw [mul_add, dtor_add, dtor_add, hx, hy, mul_add]; ring
    | hsingle β b =>
      simp only [single_mul_single, dtor_single]
      rw [← single_add]
      congr 1
      simp only [Pi.add_apply]
      push_cast
      ring

theorem dtor_comm (i j : Fin n) (f : Tor n) : dtor i (dtor j f) = dtor j (dtor i f) := by
  induction f using induction_single with
  | h0 => simp
  | hadd x y hx hy => simp only [dtor_add, hx, hy]
  | hsingle α c =>
    simp only [dtor_single]
    congr 1
    ring

/-- **A1 on the `n`-torus.** -/
noncomputable instance torScaleAlgebra : ScaleAlgebra n (Tor n) where
  d := dtor
  d_add := dtor_add
  d_mul := dtor_mul
  d_comm := dtor_comm

/-- `u^α`, a unit. -/
noncomputable def uTor (α : Fin n → ℤ) : (Tor n)ˣ where
  val := single α 1
  inv := single (-α) 1
  val_inv := by
    rw [single_mul_single, add_neg_cancel, one_mul]
    exact (AddMonoidAlgebra.one_def (R := ℝ) (M := Fin n → ℤ)).symm
  inv_val := by
    rw [single_mul_single, neg_add_cancel, one_mul]
    exact (AddMonoidAlgebra.one_def (R := ℝ) (M := Fin n → ℤ)).symm

theorem dtor_uTor (i : Fin n) (α : Fin n → ℤ) :
    dtor i ((uTor α : (Tor n)ˣ) : Tor n)
      = ((uTor α : (Tor n)ˣ) : Tor n) * single 0 ((α i : ℝ)) := by
  show dtor i (single α 1) = single α 1 * single 0 ((α i : ℝ))
  rw [dtor_single, single_mul_single]
  simp

/-- Every derivative has vanishing constant term, in every direction. -/
theorem dtor_coeff_zero (i : Fin n) (f : Tor n) : (dtor i f).coeff 0 = 0 := by
  induction f using induction_single with
  | h0 => simp
  | hadd x y hx hy => rw [dtor_add]; simp [AddMonoidAlgebra.coeff_add, hx, hy]
  | hsingle α c =>
    rw [dtor_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : α = 0
    · subst h; simp
    · simp [h]

/-- **A non-zero constant is not a derivative**, in any direction. -/
theorem no_potential_tor (i : Fin n) {c : ℝ} (hc : c ≠ 0) :
    ¬ ∃ σ : Tor n, dtor i σ = single 0 c := by
  rintro ⟨σ, hσ⟩
  have h := congrArg (fun f => AddMonoidAlgebra.coeff f 0) hσ
  simp only [dtor_coeff_zero, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at h
  exact hc h.symm

/-- The winding scale on the torus, as a scale gradient. -/
noncomputable def torGradient (α : Fin n → ℤ) : Circle.ScaleGradient n (Tor n) where
  s := uTor α
  grad := fun i => single 0 ((α i : ℝ))
  d_s := fun i => dtor_uTor i α

/-- **Inexact whenever the winding is non-zero in some direction** — and now in
any number of directions, not only one. -/
theorem torGradient_not_isExact {α : Fin n → ℤ} {i : Fin n} (hi : α i ≠ 0) :
    ¬ (torGradient α).IsExact := by
  rintro ⟨σ, hσ⟩
  exact no_potential_tor i (by exact_mod_cast hi) ⟨σ, hσ i⟩

/-- The two-torus with a single winding: `s = u`, gradient `(1, 0)`. -/
noncomputable def twoTorus : Circle.ScaleGradient 2 (Tor 2) := torGradient ![1, 0]

theorem twoTorus_not_isExact : ¬ twoTorus.IsExact := by
  refine torGradient_not_isExact (i := 0) ?_
  simp


end SCD.Torus
