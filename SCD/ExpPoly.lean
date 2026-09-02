/-
# The first configuration: exponential polynomials, and a scale that varies

Every model of A1 in this development is a polynomial ring or a matrix ring over
one — `Positivity.oneAxis`, `Witness.polyScaleAlgebra`, `Explanation.mvScaleAlgebra`,
`Triple.matrixScaleAlgebra` — and in a polynomial ring **the units are the
non-zero constants**.  A2 says `s = e^σ` is a unit and `d s = s · dσ`, so in every
one of them `dσ = 0`: the scale cannot vary.  `Newton.Dual` escapes that by making
`σ = εφ` square-zero, which buys a varying scale at the cost of being exactly
first order — `gradsq_inr` is zero by construction.

The consequence had gone unnoticed and it is sharp: **`ScaleField` had never been
constructed.**  Not "constructed only in special cases" — the structure carrying
A2 and A3 had no term anywhere in the development, so every theorem about the
scale field was true, clean, and unwitnessed.  The same holds of `Frame.DirScale`
with two different scales: `Light.twoScale` is constant over `ℝ`.

This file builds the ring those structures need.

## The construction

`ExpPoly n` is the additive monoid algebra of the polynomials over the
polynomials: finite formal sums `Σ qⱼ · e^{pⱼ}` where both the coefficients `qⱼ`
and the exponents `pⱼ` are polynomials in `n` variables.  The derivation is the
one the notation forces,

        `∂ᵢ (q · e^p) = (∂ᵢq + q ∂ᵢp) · e^p` ,

and `der_mul`, `der_comm` check that it satisfies A1 — Leibniz on the convolution
product, and commuting partials.  `expScaleAlgebra` is the instance.

What the ring buys is exactly what a polynomial ring lacks: `e^p` is a **unit**
for every polynomial `p`, with inverse `e^{-p}`, and `der_expUnit` gives
`∂ᵢ e^p = e^p · ∂ᵢp`.  That is A2's axiom, so:

* `scaleField p` — **A2 and A3, realised with a log-scale that varies.**  The
  first term of type `ScaleField` in the development;
* `scaleField_gradient_ne_zero` — and it genuinely varies: the gradient of
  `scaleField (Xᵢ)` is `1`, not `0`;
* `recipTwo` — **A4′, anisotropic, with exact reciprocity.**  The two-direction
  pattern `(e^{x₀}, e^{-x₀})` satisfies `s_t · s_r = 1` on the nose
  (`recipTwo_reciprocal`) and is not isotropic (`recipTwo_not_isotropic`).  That
  is the Schwarzschild relation at **finite amplitude**: no linearisation, no
  square-zero infinitesimal, and `Frame.reciprocal_iff_radial_is_temporal_energy`
  now has something to be about.

## What this does not do, stated before anyone reads more into it

**It does not exhibit a vacuum solution.**  `Diagonal.vacuum_scale_sum` is a
conditional whose antecedent includes `Ric = 0`, and nothing here supplies a
configuration meeting it.  The reason is not a gap in effort: the Schwarzschild
profile is `σ_r = −½ log(1 − 2M/r)`, and a **logarithm of a rational function is
not an exponential polynomial**.  So the gravity chain's hypotheses are now
*instantiable* — a directional scale with reciprocity exists — while its
*equations* are not solved in this ring.

That is a precise statement of what the next ring must contain, and it is more
useful than a vague one: closure under `∫ dp/p`, i.e. logarithms as well as
exponentials.  Registered as open rather than attempted here.

**And it is one model, not a classification.**  `Witness.lean`'s lesson applies
verbatim: one model carrying a structure shows the structure is *compatible* with
A1, not that every model of A1 carries it.  What changes is that the theorems
about `ScaleField` and about anisotropic `DirScale` are now known non-vacuous,
which they were not.

## The exponential is a choice, and here is the alternative

The construction above adjoins a formal `e^p` for every polynomial `p`, and it
would be easy to read that as forced.  It is not.  **A2 asks only for a unit `s`
and an element `σ` with `d s = s · dσ`**, and there are at least two ways to have
one:

* *adjoin an exponential* — this file: unbounded in the scale, at the price of a
  formal adjunction;
* *make `σ` nilpotent* — then `e^σ` is a **polynomial** and no adjunction is
  needed.  `Newton.Dual`'s square-zero `σ = εφ` is the smallest case, and
  `dualScaleField` below presents it as the `ScaleField` it always was.

So A2 has models of two different kinds, and §V records what separates them
rather than which is "the" model: `exp_not_first_order` against
`Newton.Dual.gradsq_inr`.  The nilpotent mechanism is exact but **truncated at a
finite order in the scale**; the exponential one is not truncated but is formal.
Neither is derived from A1–A7.  Calling the exponential the model of A2 would be
the failure this register has caught before.

## And a scope statement that matters more than either

`Dual.lean` (A3′) divides the scale group into branches and says which one the
framework needs:

> the `ℝ` branch — `Axioms.ScaleField`, a real-valued log-scale;
> the `𝕋` branch — `Defect.ScaleDefect`, a log-scale modulo a period `Δ`, which
> is what lets a defect wind.

and its own summary is that **gravity selects the `𝕋` branch**, the `ℝ` branch
being its `Δ → 0` degeneration — `Dual.R_branch_is_trivial`: a scale defect of
period zero has no holonomy, so nothing in the `ℝ` branch winds.

**Everything in this file is the `ℝ` branch.**  `Axioms.ScaleField` is that
branch's carrier, and a formal exponential of a polynomial has no period.  So
what is supplied here is a model of A2 *as `Axioms.lean` states it* — which is
the branch the framework's own source law does not use.  `Defect.ScaleDefect`,
the `𝕋` branch carrier, still has no model.

That is the honest reading of why no vacuum solution turned up, and it is a
better one than the observation about logarithms: it is not only that the profile
is transcendental, it is that the branch carrying defects is a different branch.
Registered as open, and it is the first thing bridge one's successor should
build.
-/
import SCD.Frame
import SCD.Explanation
import SCD.Newton
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace SCD.ExpPolyModel

open MvPolynomial AddMonoidAlgebra SCD


open MvPolynomial AddMonoidAlgebra

/-- Polynomials in `n` variables. -/
abbrev P (n : ℕ) := MvPolynomial (Fin n) ℝ

/-- Exponential polynomials: finite sums `Σ qⱼ · e^{pⱼ}` with both the
coefficients and the exponents polynomials. -/
abbrev ExpPoly (n : ℕ) := AddMonoidAlgebra (P n) (P n)

variable {n : ℕ}

/-- `∂ᵢ (q · e^p) = (∂ᵢq + q ∂ᵢp) · e^p`, extended additively. -/
noncomputable def der (i : Fin n) (f : ExpPoly n) : ExpPoly n :=
  f.coeff.sum fun p q => single p (pderiv i q + q * pderiv i p)

@[simp] theorem der_single (i : Fin n) (p q : P n) :
    der i (single p q) = single p (pderiv i q + q * pderiv i p) := by
  simp only [der, coeff_single]
  rw [Finsupp.sum_single_index]
  simp

@[simp] theorem der_zero (i : Fin n) : der (n := n) i 0 = 0 := by
  simp [der]

theorem der_add (i : Fin n) (f g : ExpPoly n) :
    der i (f + g) = der i f + der i g := by
  simp only [der, AddMonoidAlgebra.coeff_add]
  rw [Finsupp.sum_add_index']
  · intro p; simp
  · intro p q q'; simp only [map_add]; rw [← single_add]; congr 1; ring

theorem der_single_mul_single (i : Fin n) (p q p' q' : P n) :
    der i (single p q * single p' q')
      = der i (single p q) * single p' q' + single p q * der i (single p' q') := by
  simp only [single_mul_single, der_single, map_add, pderiv_mul]
  rw [← single_add]
  congr 1
  ring

/-- Every exponential polynomial is a finite sum of `q · e^p`. -/
theorem induction_single {n : ℕ} {motive : ExpPoly n → Prop} (f : ExpPoly n)
    (h0 : motive 0)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsingle : ∀ p q, motive (single p q)) : motive f := by
  have key : ∀ c : (P n) →₀ (P n), motive (ofCoeff c) := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => exact h0
    | add f g hf hg => exact hadd _ _ hf hg
    | single a b => exact hsingle a b
  exact key f.coeff

theorem der_mul (i : Fin n) (f g : ExpPoly n) :
    der i (f * g) = der i f * g + f * der i g := by
  induction f using induction_single with
  | h0 => simp
  | hadd x y hx hy => rw [add_mul, der_add, der_add, hx, hy, add_mul]; ring
  | hsingle p q =>
    induction g using induction_single with
    | h0 => simp
    | hadd x y hx hy => rw [mul_add, der_add, der_add, hx, hy, mul_add]; ring
    | hsingle p' q' => exact der_single_mul_single i p q p' q'

theorem der_comm (i j : Fin n) (f : ExpPoly n) :
    der i (der j f) = der j (der i f) := by
  induction f using induction_single with
  | h0 => simp
  | hadd x y hx hy => simp only [der_add, hx, hy]
  | hsingle p q =>
    have h : pderiv i (pderiv j q + q * pderiv j p)
          + (pderiv j q + q * pderiv j p) * pderiv i p
        = pderiv j (pderiv i q + q * pderiv i p)
          + (pderiv i q + q * pderiv i p) * pderiv j p := by
      simp only [map_add, pderiv_mul]
      rw [Explanation.pderiv_comm' i j q, Explanation.pderiv_comm' i j p]
      ring
    simp only [der_single]
    rw [h]

noncomputable instance expScaleAlgebra : ScaleAlgebra n (ExpPoly n) where
  d := der
  d_add := der_add
  d_mul := der_mul
  d_comm := der_comm



open MvPolynomial AddMonoidAlgebra SCD

variable {n : ℕ}

/-! ## II. A2/A3: the scale field, with a scale that actually varies -/

/-- A polynomial, read as an exponential polynomial with exponent zero. -/
noncomputable def emb (p : P n) : ExpPoly n := single 0 p

@[simp] theorem emb_zero : emb (0 : P n) = 0 := by simp [emb]

theorem emb_add (p q : P n) : emb (p + q) = emb p + emb q := by
  simp [emb, single_add]

theorem emb_one : emb (1 : P n) = 1 :=
  (AddMonoidAlgebra.one_def (R := P n) (M := P n)).symm

@[simp] theorem der_emb (i : Fin n) (p : P n) : der i (emb p) = emb (pderiv i p) := by
  simp [emb]

/-- `e^p`, as a unit: its inverse is `e^{-p}`. -/
noncomputable def expUnit (p : P n) : (ExpPoly n)ˣ where
  val := single p 1
  inv := single (-p) 1
  val_inv := by
    rw [single_mul_single, add_neg_cancel, one_mul]
    exact (AddMonoidAlgebra.one_def (R := P n) (M := P n)).symm
  inv_val := by
    rw [single_mul_single, neg_add_cancel, one_mul]
    exact (AddMonoidAlgebra.one_def (R := P n) (M := P n)).symm

@[simp] theorem expUnit_val (p : P n) : ((expUnit p : (ExpPoly n)ˣ) : ExpPoly n) = single p 1 :=
  rfl

theorem expUnit_add (p q : P n) : expUnit (p + q) = expUnit p * expUnit q := by
  ext
  simp [expUnit, single_mul_single]

/-- **`e^p` differentiates to `e^p · ∂p`** — the defining property A2 asks for,
and the reason a polynomial ring alone cannot carry A2: there the only units are
the constants, so `∂σ` is forced to vanish. -/
@[simp] theorem der_expUnit (i : Fin n) (p : P n) :
    der i ((expUnit p : ExpPoly n)) = (expUnit p : ExpPoly n) * emb (pderiv i p) := by
  simp [expUnit, emb, single_mul_single]

/-- **A2/A3 realised with a non-constant log-scale.** -/
noncomputable def scaleField (p : P n) : ScaleField n (ExpPoly n) where
  σ := emb p
  s := expUnit p
  d_s i := by
    show der i ((expUnit p : ExpPoly n)) = ((expUnit p : ExpPoly n)) * der i (emb p)
    rw [der_emb, der_expUnit]

@[simp] theorem scaleField_sigma (p : P n) : (scaleField p).σ = emb p := rfl

/-! ## III. It is not the linearised model -/

/-- The scale of `field (X i)` genuinely varies: its gradient is `1`, not `0`. -/
theorem scaleField_gradient_ne_zero (i : Fin n) :
    sig (scaleField (X i)).σ i ≠ 0 := by
  show der i (emb (X i)) ≠ 0
  rw [der_emb, pderiv_X_self, emb_one]
  exact one_ne_zero

theorem expUnit_zero : expUnit (0 : P n) = 1 :=
  Units.ext emb_one

/-! ## IV. A4′: one scale per direction, and exact reciprocity -/

/-- A directional scale `s_a = e^{φ a}`. -/
noncomputable def dirScale (φ : Fin n → P n) : Frame.DirScale n (ExpPoly n) where
  s := fun a => expUnit (φ a)

@[simp] theorem dirScale_s (φ : Fin n → P n) (a : Fin n) :
    (dirScale φ).s a = expUnit (φ a) := rfl

/-- **`s_t · s_r = 1` exactly**, whenever the two log-scales are negatives.
This is the Schwarzschild relation, at finite amplitude and with no
linearisation: `Newton.Dual` gets it only to first order in a square-zero
infinitesimal. -/
theorem reciprocal_of_neg (φ : Fin n → P n) (t r : Fin n) (h : φ r = -φ t) :
    (dirScale φ).Reciprocal t r := by
  show expUnit (φ t) * expUnit (φ r) = 1
  rw [h, ← expUnit_add, add_neg_cancel, expUnit_zero]

/-- The two-direction reciprocal pattern `(e^{x₀}, e^{-x₀})`. -/
noncomputable def recipTwo : Frame.DirScale 2 (ExpPoly 2) :=
  dirScale ![X 0, -X 0]

theorem recipTwo_reciprocal : recipTwo.Reciprocal 0 1 :=
  reciprocal_of_neg _ 0 1 rfl

/-- **And it is anisotropic**: the two directional scales differ, which is what
a scalar scale cannot express and what `Frame.lean` needed A4′ for. -/
theorem recipTwo_not_isotropic : ¬ recipTwo.Isotropic := by
  intro h
  have hne : (-X 0 : P 2) ≠ X 0 := by
    intro he
    have h2 := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) he
    rw [MvPolynomial.coeff_neg, MvPolynomial.coeff_X] at h2
    norm_num at h2
  have h01 := congrArg (fun u => ((u : (ExpPoly 2)ˣ) : ExpPoly 2)) (h 0 1)
  simp only [recipTwo, dirScale_s, expUnit_val, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h01
  have hc := congrArg (fun f => AddMonoidAlgebra.coeff f (X 0)) h01
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hc
  rw [Finsupp.single_apply, if_neg hne] at hc
  exact one_ne_zero hc



/-! ## V.  The other mechanism, and what separates them

The point of this section is negative and it is the reason it exists: **nothing
in A1–A7 selects the exponential.**  A nilpotent does the same job with no
adjunction, and the development already had one — it was never presented as a
model of A2. -/

open TrivSqZeroExt in
/-- `1 + εφ` is a unit of the dual numbers, with inverse `1 − εφ`. -/
noncomputable def unipotent (φ : MvPolynomial (Fin n) ℝ) :
    (DualNumber (MvPolynomial (Fin n) ℝ))ˣ where
  val := 1 + inr φ
  inv := 1 - inr φ
  val_inv := by
    have h : (inr φ : DualNumber (MvPolynomial (Fin n) ℝ)) * inr φ = 0 :=
      TrivSqZeroExt.inr_mul_inr _ φ φ
    have e : (1 + inr φ) * (1 - inr φ)
        = 1 - (inr φ : DualNumber (MvPolynomial (Fin n) ℝ)) * inr φ := by ring
    rw [e, h, sub_zero]
  inv_val := by
    have h : (inr φ : DualNumber (MvPolynomial (Fin n) ℝ)) * inr φ = 0 :=
      TrivSqZeroExt.inr_mul_inr _ φ φ
    have e : (1 - inr φ) * (1 + inr φ)
        = 1 - (inr φ : DualNumber (MvPolynomial (Fin n) ℝ)) * inr φ := by ring
    rw [e, h, sub_zero]

open TrivSqZeroExt in
/-- **A2, realised by a nilpotent instead of an exponential.**

`σ = εφ` squares to zero, so `e^σ = 1 + σ` is a polynomial and the ring needs no
formal exponential.  This is `Newton.Dual`'s model, which the development has
carried since the Newtonian limit was written and never presented as the
`ScaleField` it is. -/
noncomputable def dualScaleField (φ : MvPolynomial (Fin n) ℝ) :
    ScaleField n (DualNumber (MvPolynomial (Fin n) ℝ)) where
  σ := inr φ
  s := unipotent φ
  d_s i := by
    have hd : ScaleAlgebra.d i (inr φ : DualNumber (MvPolynomial (Fin n) ℝ))
        = inr (ScaleAlgebra.d i φ) := Dual.sig_inr φ i
    have h0 : (inr φ : DualNumber (MvPolynomial (Fin n) ℝ))
        * inr (ScaleAlgebra.d i φ) = 0 := TrivSqZeroExt.inr_mul_inr _ φ _
    show ScaleAlgebra.d i ((1 : DualNumber (MvPolynomial (Fin n) ℝ)) + inr φ)
        = ((1 : DualNumber (MvPolynomial (Fin n) ℝ)) + inr φ)
          * ScaleAlgebra.d i (inr φ)
    rw [ScaleAlgebra.d_add, ScaleAlgebra.d_one, zero_add, hd, add_mul, one_mul,
      h0, add_zero]

/-- **What separates the two mechanisms.**

`Newton.Dual.gradsq_inr` makes the quadratic invariant vanish *by construction*
in the nilpotent model — that is what "exactly first order" means, and it is why
`Newton.poisson_exact` is exact there.  In the exponential model it does not
vanish, so the terms a linearisation discards are present.

This is the whole of the difference that matters, and stating it is what keeps
the choice of mechanism a choice. -/
theorem exp_not_first_order :
    gradsq 1 ((scaleField (X (0 : Fin 1)) : ScaleField 1 (ExpPoly 1)).σ) ≠ 0 := by
  show gradsq 1 (emb (X (0 : Fin 1))) ≠ 0
  rw [gradsq, Fin.sum_univ_one]
  show der 0 (emb (X (0 : Fin 1))) * der 0 (emb (X (0 : Fin 1))) ≠ 0
  rw [der_emb, pderiv_X_self, emb_one, one_mul]
  exact one_ne_zero

end SCD.ExpPolyModel
