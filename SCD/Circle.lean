/-
# The join: a scale that winds, in a ring

`ExpPoly.lean` closed "A2 has no model" and its correction named what stayed
open.  `Defect.ScaleDefect` is inhabited, so the gap was never that the `𝕋`
branch has no model; it is that **`ScaleDefect` is not a scale field** — a
function `ℝ → ℝ` with a quasiperiodicity condition, carrying no ring, no
derivations and no unit.  Nothing in the development was at once a model of A1–A2
and periodic, and the two branches of A3′ were related by `Dual.lean`'s prose
together with theorems about `ScaleDefect` alone.

This file builds the missing object, and the first thing it finds is that the
join cannot have the shape one would reach for.

## Why there is no "periodic scale field"

If the log-scale is defined only modulo a period then **`σ` is not an element of
the ring** — only its gradient is, because differentiating kills the ambiguity.
`Axioms.ScaleField` has a field `σ : A`.  So a periodic scale field is not a
thing to be constructed; it is a contradiction in terms, and
`no_scaleField_with_uPow` proves it on the smallest example.

That is the structural reason the branches never joined: **`Axioms.ScaleField`
*is* the `ℝ` branch by construction.**  It was not a modelling accident.

## The object

`Circ` is `ℝ[u, u⁻¹]`, the coordinate ring of the circle, with `dloop = u ∂/∂u`
— on `u^k` it is multiplication by `k`, which is `∂/∂θ` with `u = e^{iθ}`.
`dloop_mul` and the instance give A1 with one direction, the loop.

`uPow k` is the unit `u^k`, and `dloop_uPow` says its logarithmic derivative is
the constant `k`: a perfectly good scale gradient.  But `dloop_coeff_zero` shows
every derivative has vanishing constant term, so `no_potential` — **a non-zero
constant is not a derivative.**  The gradient is closed and not exact, which is
what "defined only modulo a period" means algebraically.

## The join, and what separates the branches

`ScaleGradient` keeps the unit and the gradient and drops the potential:

    s : Aˣ,  grad : Fin n → A,  d s = s · grad .

`ofScaleField` embeds every scale field into it and `ofScaleField_isExact` says
the image is the exact locus.  `circGradient k` is a scale gradient that is
**not** exact for `k ≠ 0` (`circGradient_not_isExact`).  So:

> **One carrier, two branches, and `IsExact` is exactly what separates them.**
> The `ℝ` branch is the exact locus, and `Dual.lean`'s `Δ → 0` degeneration is
> the statement that on that locus nothing winds.

And `exact_iff_trivial` relates the two branches' *carriers* rather than
arguing the relation: the gradient of `u^k` is exact exactly when the defect it
follows is trivial.  `Dual.lean` called `Defect.lift` the covering map
`ℝ → ℝ/ΔZ`; this is that identification with a ring on one side of it.

## What is not done, and it is a real list

* **One direction.**  `Circ` has a single loop, so the closedness condition
  `∂ᵢ gⱼ = ∂ⱼ gᵢ` that a multi-direction `ScaleGradient` needs is vacuous here.
  Whether A2's other consequences survive the passage from `σ` to `grad`, and
  what closedness costs, is untouched;
* **`ScaleGradient` is a proposal, not an amendment.**  `Axioms.lean` is
  unchanged.  Whether A2 should be restated with the gradient primitive is a
  question for a pass that weighs it against everything downstream of `σ` — and
  there is a lot, since A5 is about differences of `σ` and `Openness.lean` reads
  A5 and A6 off the group `σ` generates.  Adopting it here because it is
  convenient would be exactly the move `Audit` §V.t declined for idempotents;
* **still no vacuum solution.**  Nothing here runs `Diagonal.lean`'s chain.  What
  is supplied is the object that branch needs, not a solution on it.
-/
import SCD.Axioms
import SCD.Defect
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Real.Basic

namespace SCD.Circle

open AddMonoidAlgebra SCD


open AddMonoidAlgebra SCD

/-- Trigonometric polynomials `Σ c_k u^k`: the coordinate ring of the circle. -/
abbrev Circ := AddMonoidAlgebra ℝ ℤ

/-- `u ∂/∂u` — differentiation along the loop.  On `u^k` it is multiplication
by `k`, which is `∂/∂θ` with `u = e^{iθ}`. -/
noncomputable def dloop (f : Circ) : Circ :=
  f.coeff.sum fun k c => single k ((k : ℝ) * c)

@[simp] theorem dloop_single (k : ℤ) (c : ℝ) :
    dloop (single k c) = single k ((k : ℝ) * c) := by
  simp only [dloop, coeff_single]
  rw [Finsupp.sum_single_index]
  simp

@[simp] theorem dloop_zero : dloop 0 = 0 := by simp [dloop]

theorem dloop_add (f g : Circ) : dloop (f + g) = dloop f + dloop g := by
  simp only [dloop, AddMonoidAlgebra.coeff_add]
  rw [Finsupp.sum_add_index']
  · intro k; simp
  · intro k a b; rw [← single_add]; congr 1; ring

theorem induction_single {motive : Circ → Prop} (f : Circ)
    (h0 : motive 0) (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsingle : ∀ k c, motive (single k c)) : motive f := by
  have key : ∀ c : ℤ →₀ ℝ, motive (ofCoeff c) := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => exact h0
    | add f g hf hg => exact hadd _ _ hf hg
    | single a b => exact hsingle a b
  exact key f.coeff

theorem dloop_mul (f g : Circ) : dloop (f * g) = dloop f * g + f * dloop g := by
  induction f using induction_single with
  | h0 => simp
  | hadd x y hx hy => rw [add_mul, dloop_add, dloop_add, hx, hy, add_mul]; ring
  | hsingle k c =>
    induction g using induction_single with
    | h0 => simp
    | hadd x y hx hy => rw [mul_add, dloop_add, dloop_add, hx, hy, mul_add]; ring
    | hsingle k' c' =>
      simp only [single_mul_single, dloop_single]
      rw [← single_add]
      congr 1
      push_cast
      ring

/-- **A1 on the circle**, with one direction: the loop. -/
noncomputable instance circScaleAlgebra : ScaleAlgebra 1 Circ where
  d _ := dloop
  d_add _ := dloop_add
  d_mul _ := dloop_mul
  d_comm _ _ _ := rfl

/-! ## The scale that winds -/

/-- `u^k`, a unit of the circle ring. -/
noncomputable def uPow (k : ℤ) : Circˣ where
  val := single k 1
  inv := single (-k) 1
  val_inv := by
    rw [single_mul_single, add_neg_cancel, one_mul]
    exact (AddMonoidAlgebra.one_def (R := ℝ) (M := ℤ)).symm
  inv_val := by
    rw [single_mul_single, neg_add_cancel, one_mul]
    exact (AddMonoidAlgebra.one_def (R := ℝ) (M := ℤ)).symm

/-- **Its logarithmic derivative is the constant `k`** — a perfectly good scale
gradient, and the reason `u^k` deserves to be called a scale. -/
theorem dloop_uPow (k : ℤ) :
    dloop ((uPow k : Circˣ) : Circ) = ((uPow k : Circˣ) : Circ) * single 0 (k : ℝ) := by
  show dloop (single k 1) = single k 1 * single 0 (k : ℝ)
  rw [dloop_single, single_mul_single]
  simp

/-! ## But the gradient has no potential -/

/-- Every image of `dloop` has vanishing constant term: `∂/∂θ` kills constants
and produces none. -/
theorem dloop_coeff_zero (f : Circ) : (dloop f).coeff 0 = 0 := by
  induction f using induction_single with
  | h0 => simp
  | hadd x y hx hy => rw [dloop_add]; simp [AddMonoidAlgebra.coeff_add, hx, hy]
  | hsingle k c =>
    rw [dloop_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : k = 0
    · subst h; simp
    · simp [h]

/-- **A non-zero constant is not a derivative.**

There is no `σ` in the ring whose loop-derivative is the constant `c ≠ 0`: the
scale gradient of `u^k` is closed and **not exact**.  That is what "the log-scale
is defined only modulo a period" means algebraically. -/
theorem no_potential {c : ℝ} (hc : c ≠ 0) : ¬ ∃ σ : Circ, dloop σ = single 0 c := by
  rintro ⟨σ, hσ⟩
  have h := congrArg (fun f => AddMonoidAlgebra.coeff f 0) hσ
  simp only [dloop_coeff_zero, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at h
  exact hc h.symm

/-! ## So A2, as stated, cannot hold here -/

/-- **There is no scale field on this object with this scale.**

`ScaleField` demands a log-scale `σ` *in the ring*; `u^k` has a gradient and no
potential, so no `ScaleField` can carry it.  This is why the two branches of A3′
never joined: `Axioms.ScaleField` **is** the `ℝ` branch by construction, and the
`𝕋` branch is not a scale field at all. -/
theorem no_scaleField_with_uPow {k : ℤ} (hk : k ≠ 0) :
    ¬ ∃ F : ScaleField 1 Circ, F.s = uPow k := by
  rintro ⟨F, hF⟩
  have hds : dloop ((uPow k : Circˣ) : Circ)
      = ((uPow k : Circˣ) : Circ) * dloop F.σ := by
    have := F.d_s 0
    rw [hF] at this
    exact this
  rw [dloop_uPow] at hds
  have hcancel : dloop F.σ = single 0 (k : ℝ) :=
    ((Units.mul_right_inj (uPow k)).mp hds).symm
  exact no_potential (by exact_mod_cast hk) ⟨F.σ, hcancel⟩

/-! ## The join: one carrier, two branches -/

/-- **The scale with only its gradient assumed to exist.**

A2 asks for a log-scale `σ` in the ring and *derives* the gradient from it.  The
`𝕋` branch has a gradient and no potential, so the carrier common to both keeps
the gradient and drops the potential.

Offered as the shape of the join and **not adopted as an amendment to A2** —
`Axioms.lean` is unchanged, and whether the axiom should be restated this way is
a question for a pass that weighs it, not for the file that noticed it. -/
structure ScaleGradient (n : ℕ) (A : Type*) [CommRing A] [ScaleAlgebra n A] where
  /-- The scale, a unit. -/
  s : Aˣ
  /-- Its logarithmic derivative, direction by direction. -/
  grad : Fin n → A
  /-- The scale differentiates to itself times its gradient. -/
  d_s : ∀ i, ScaleAlgebra.d i (s : A) = (s : A) * grad i

namespace ScaleGradient

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-- The gradient is **exact** when it is the gradient of something in the ring. -/
def IsExact (G : ScaleGradient n A) : Prop :=
  ∃ σ : A, ∀ i, ScaleAlgebra.d i σ = G.grad i

/-- **Every scale field is a scale gradient** — the `ℝ` branch embeds. -/
def ofScaleField (F : ScaleField n A) : ScaleGradient n A where
  s := F.s
  grad := fun i => sig F.σ i
  d_s := F.d_s

/-- **and its gradient is exact, by construction.**  The potential is `σ`. -/
theorem ofScaleField_isExact (F : ScaleField n A) : (ofScaleField F).IsExact :=
  ⟨F.σ, fun _ => rfl⟩

end ScaleGradient

/-- **The winding scale is a scale gradient.** -/
noncomputable def circGradient (k : ℤ) : ScaleGradient 1 Circ where
  s := uPow k
  grad := fun _ => single 0 (k : ℝ)
  d_s _ := dloop_uPow k

/-- **and it is not exact when the winding is non-zero.**

So `ScaleGradient` contains both branches and `IsExact` is exactly what
separates them: the `ℝ` branch is the exact locus, and `Dual.lean`'s `Δ → 0`
degeneration is the statement that the locus is where nothing winds. -/
theorem circGradient_not_isExact {k : ℤ} (hk : k ≠ 0) :
    ¬ (circGradient k).IsExact := by
  rintro ⟨σ, hσ⟩
  exact no_potential (by exact_mod_cast hk) ⟨σ, hσ 0⟩

/-! ## And the bridge to the defect -/

/-- The winding scale, followed around the loop: the lift shifts by `k` periods
per circuit, which is `Defect.ScaleDefect`'s quasiperiodicity. -/
noncomputable def toDefect (Δ : ℝ) (k : ℤ) : Defect.ScaleDefect Δ where
  lift := fun x => (k : ℝ) * Δ * x
  winding := k
  quasiperiodic := by intro x; ring

@[simp] theorem toDefect_winding (Δ : ℝ) (k : ℤ) : (toDefect Δ k).winding = k := rfl

/-- Exactness of the gradient is the vanishing of the winding. -/
theorem circGradient_isExact_iff (k : ℤ) : (circGradient k).IsExact ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    exact circGradient_not_isExact hk h
  · rintro rfl
    exact ⟨0, fun i => by simp [circGradient]⟩

/-- And so is triviality of the defect. -/
theorem toDefect_isTrivial_iff {Δ : ℝ} (hΔ : Δ ≠ 0) (k : ℤ) :
    (toDefect Δ k).IsTrivial ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    exact Defect.ScaleDefect.stable_of_winding_ne_zero hΔ (toDefect Δ k)
      (by simpa using hk) h
  · rintro rfl
    intro x
    simp [toDefect]

/-- **The algebraic winding is the topological one.**

The gradient of `u^k` is exact exactly when the defect it follows is trivial.
One object, two descriptions — and the first is the one that lives in a ring
with derivations, which is what the two branches of A3′ never had in common. -/
theorem exact_iff_trivial {Δ : ℝ} (hΔ : Δ ≠ 0) (k : ℤ) :
    (circGradient k).IsExact ↔ (toDefect Δ k).IsTrivial :=
  (circGradient_isExact_iff k).trans (toDefect_isTrivial_iff hΔ k).symm


end SCD.Circle
