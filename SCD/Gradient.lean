/-
# What A2 assumes, measured

`Circle.lean` found that a periodic scale field is a contradiction in terms and
proposed a carrier keeping the gradient and dropping the potential.  A proposal
of that shape should not be adopted or rejected on taste, and it should certainly
not be built on before it is settled: the question is what A2 is actually doing,
and that is measurable.

This file measures it.  Nothing here changes an axiom.

## I.  The geometry never sees the log-scale

`hess`, `lap`, `gradsq`, `Chr`, `Rm`, `Ric` and `Defm` are each built from `sig`
and from nothing else.  §I turns that from a remark into theorems: two log-scales
with the same gradient have the same **everything** (`geometry_congr`).  So `σ`
appears in the statements of the development and not in their content.

`Axioms.geometry_fiducial_invariant` — A5's carrier — then arrives from the
congruence side (§II): a fiducial shift changes no geometry because it changes no
gradient.

## II.  What `σ` is doing, and it is three things

* it lets `ScaleField` be **stated** — it is a field of the structure;
* it carries the additive half of the group law, since `Axioms.mul` adds `σ`;
* and it makes `hess_symm` free: `d i (d j σ) = d j (d i σ)` is `d_comm`.

The first two are bookkeeping.  **The third is the whole of what the passage to a
gradient costs**, and calling it a cost is the wrong reading — it is information
A2 was carrying without declaring.

## III.  The finding: A2 assumes exactness, and that is a branch choice

`Closed g` says the Hessian of a gradient is symmetric.  `exact_isClosed`: an
exact gradient is closed, which is `hess_symm` again.  `closed_not_exact`: the
converse fails, on `Circle.lean`'s winding scale.  Therefore

> **A2 does not assume "there is a scale".  It assumes the scale's gradient is
> *exact*** — and by `Dual.lean` that is the `ℝ` branch of A3′, chosen silently
> and, by `Dual.lean`'s own summary, the branch gravity does not select.

That reframes the axiom question from a matter of style — `σ` or `grad` — to one
with an answer: the choice is between **closed** and **closed-and-exact**, and
the framework's own source law wants the weaker one.

## IV.  And then the structure collapses

§IV is the part that was not expected.  Given a unit `s`, the equation
`d s = s · g` **determines** `g`, because `s` is invertible: `logDeriv_spec`
supplies a solution and `grad_unique` shows there is only one.  So
`Circle.ScaleGradient` adds nothing to `s : Aˣ` (`grad_eq_logDeriv`), and

> **A2's content is one unit.**  The gradient is a definition, the log-scale is
> an *optional potential* for it, and exactness is a property of the unit rather
> than an extra piece of data.

That is a real simplification of the axiom and it is what the pass was for: not
"should the primitive be σ or grad" but "the primitive is `s`, and `σ` is a
choice of potential that not every model admits".

## What follows, and what is deliberately not done

**Not done: the amendment.**  `Axioms.lean` is untouched.  Restating A2 as "the
scale is a unit" plus `Closed` as a hypothesis where it is needed is a mechanical
but wide edit — every consequence of `hess_symm` inherits a hypothesis — and it
should be made once, deliberately, not as a side effect of the file that measured
it.

**The costs, so the decision is made with them in hand — and the first one turned
out not to exist.**

* *withdrawn.*  §III above says the passage costs the Hessian's symmetry, and §V
  disproves it: `logDeriv_closed` shows the gradient of a unit is closed for
  **every** unit, so `hess_symm` survives with no hypothesis and nothing
  downstream of it inherits one.  The claim is left standing in §III with this
  correction beside it rather than edited away, because the shape of the mistake
  — assuming a condition must be assumed — is the one worth remembering;
* the branch distinction is therefore **exactness alone**, and it is not tested
  above one direction: `Circle.lean`'s witness is at `n = 1`.  Whether inexact
  gradients persist in higher dimension is not settled here;
* **the observer.**  `Observer.Crossed` compares *values* — `μ i ≤ σ i` — in a
  real-valued shadow.  With the axiom reduced to a unit there is no `σ` in the
  ring for that shadow to shadow.  Nothing breaks today, because
  `Observer.Resolution` was never the ring's `σ`; what it does is sharpen G3 from
  "the observer does not reach the algebra" to **"the observer compares values of
  a quantity the axioms need not have"**.

**And a placement question.**  `ScaleGradient` currently lives in `Circle.lean`,
a model file, because that is where it was noticed.  If the amendment is made it
belongs in `Axioms.lean`, and if it is not made it should probably stay where the
evidence for it is.
-/
import SCD.Circle
import SCD.Conformal

namespace SCD.Gradient

open SCD ScaleAlgebra Finset


open SCD ScaleAlgebra Finset

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]

/-! ## I. The geometry is a function of the gradient -/

theorem hess_congr {σ τ : M} (h : ∀ i : Fin n, sig σ i = sig τ i) (i j : Fin n) :
    hess σ i j = hess τ i j := by
  simp only [hess, h]

theorem gradsq_congr {σ τ : M} (h : ∀ i : Fin n, sig σ i = sig τ i) :
    gradsq n σ = gradsq n τ := by
  simp only [gradsq, h]

theorem lap_congr {σ τ : M} (h : ∀ i : Fin n, sig σ i = sig τ i) : lap n σ = lap n τ := by
  simp only [lap, hess_congr h]

theorem Chr_congr {σ τ : M} (h : ∀ i : Fin n, sig σ i = sig τ i) (a b c : Fin n) :
    Chr σ a b c = Chr τ a b c := by
  simp only [Chr, h]

theorem Defm_congr {σ τ : M} (h : ∀ i : Fin n, sig σ i = sig τ i) (i j : Fin n) :
    Defm n σ i j = Defm n τ i j := by
  simp only [Defm, hess_congr h, h, gradsq_congr h]

theorem Rm_congr {σ τ : M} (h : ∀ i : Fin n, sig σ i = sig τ i) (a b c e : Fin n) :
    Rm σ a b c e = Rm τ a b c e := by
  simp only [Rm, Chr_congr h]

theorem Ric_congr {σ τ : M} (h : ∀ i : Fin n, sig σ i = sig τ i) (b e : Fin n) :
    Ric σ b e = Ric τ b e := by
  simp only [Ric, Rm_congr h]

/-- **The geometry does not see the log-scale, only its gradient.** -/
theorem geometry_congr {σ τ : M} (h : ∀ i : Fin n, sig σ i = sig τ i) :
    (∀ i j : Fin n, hess σ i j = hess τ i j) ∧ gradsq n σ = gradsq n τ ∧ lap n σ = lap n τ
      ∧ (∀ i j : Fin n, Defm n σ i j = Defm n τ i j)
      ∧ (∀ a b c e : Fin n, Rm σ a b c e = Rm τ a b c e)
      ∧ (∀ b e : Fin n, Ric σ b e = Ric τ b e) :=
  ⟨hess_congr h, gradsq_congr h, lap_congr h, Defm_congr h, Rm_congr h, Ric_congr h⟩

/-! ## II. So a fiducial shift changes no geometry -/

variable {A : Type*} [CommRing A] [ScaleAlgebra n A]

theorem fiducial_changes_no_geometry (F C : ScaleField n A)
    (hC : ScaleField.IsFiducial C) :
    (∀ i j : Fin n, hess (F * C).σ i j = hess F.σ i j) ∧ gradsq n (F * C).σ = gradsq n F.σ
      ∧ (∀ a b c e : Fin n, Rm (F * C).σ a b c e = Rm F.σ a b c e) := by
  have h : ∀ i, sig (F * C).σ i = sig F.σ i :=
    fun i => ScaleField.sig_mul_fiducial F C hC i
  exact ⟨hess_congr h, gradsq_congr h, Rm_congr h⟩

/-! ## III. What the passage costs -/

/-- A gradient is **closed** when its Hessian is symmetric. -/
def Closed (g : Fin n → M) : Prop := ∀ i j, d i (g j) = d j (g i)

/-- **An exact gradient is closed** — that is `hess_symm`, which is `d_comm`.
With `σ` in the ring the symmetry of the Hessian is free; with only a gradient it
is a condition. -/
theorem exact_isClosed (σ : M) : Closed (sig (n := n) σ) :=
  fun i j => hess_symm σ i j

/-- **And closed does not imply exact.**  The winding scale of `Circle.lean` is a
closed gradient with no potential.  So `Closed` is strictly weaker than "is the
gradient of something", and the gap is exactly the two branches of A3′. -/
theorem closed_not_exact {k : ℤ} (hk : k ≠ 0) :
    Closed (Circle.circGradient k).grad ∧ ¬ (Circle.circGradient k).IsExact := by
  refine ⟨fun i j => ?_, Circle.circGradient_not_isExact hk⟩
  have : i = j := Subsingleton.elim i j
  rw [this]

/-! ## IV. And the gradient is not data either -/

/-- The logarithmic derivative of a unit: `s⁻¹ ∂s`. -/
def logDeriv (s : Aˣ) (i : Fin n) : A := ((s⁻¹ : Aˣ) : A) * d i (s : A)

/-- **It satisfies A2's equation by construction.** -/
theorem logDeriv_spec (s : Aˣ) (i : Fin n) :
    d i (s : A) = (s : A) * logDeriv s i := by
  simp only [logDeriv, ← mul_assoc, Units.mul_inv, one_mul]

/-- **So the gradient is determined by the scale, and is not extra data.**

Two scale gradients with the same unit have the same gradient: `s` is invertible,
so `d s = s · g` has one solution.  What A2 supplies beyond "the scale is a unit"
is therefore not the gradient — it is the *potential*. -/
theorem grad_unique (G H : Circle.ScaleGradient n A) (h : G.s = H.s) :
    G.grad = H.grad := by
  funext i
  have hG := G.d_s i
  have hH := H.d_s i
  rw [h] at hG
  exact (Units.mul_right_inj H.s).mp (hG.symm.trans hH)

/-- **A2's content, measured: one unit.**

Every scale gradient is the one determined by its own unit, so the structure adds
nothing to `s : Aˣ`.  A2 = "the scale is a unit"; the gradient is a definition and
the log-scale is an optional potential for it. -/
theorem grad_eq_logDeriv (G : Circle.ScaleGradient n A) : G.grad = logDeriv G.s := by
  funext i
  exact (Units.mul_right_inj G.s).mp ((G.d_s i).symm.trans (logDeriv_spec G.s i))


/-! ## V.  And closedness is free

Written after §III claimed the passage costs the Hessian's symmetry.  **It does
not.**  The gradient of a unit is closed for every unit, so nothing downstream of
`hess_symm` needs a hypothesis and the cost §III named is not a cost. -/


/-- `∂(s⁻¹) = −(s⁻¹)² ∂s`. -/
theorem d_inv (s : Aˣ) (i : Fin n) :
    d i ((s⁻¹ : Aˣ) : A) = -(((s⁻¹ : Aˣ) : A) * ((s⁻¹ : Aˣ) : A) * d i (s : A)) := by
  have h : (s : A) * ((s⁻¹ : Aˣ) : A) = 1 := s.mul_inv
  have hd := congrArg (fun x => d i x) h
  simp only [d_mul, d_one] at hd
  -- hd : d i s * s⁻¹ + s * d i s⁻¹ = 0
  have hs : ((s⁻¹ : Aˣ) : A) * (s : A) = 1 := s.inv_mul
  calc d i ((s⁻¹ : Aˣ) : A)
      = (((s⁻¹ : Aˣ) : A) * (s : A)) * d i ((s⁻¹ : Aˣ) : A) := by rw [hs, one_mul]
    _ = ((s⁻¹ : Aˣ) : A) * ((s : A) * d i ((s⁻¹ : Aˣ) : A)) := by ring
    _ = ((s⁻¹ : Aˣ) : A) * (-(d i (s : A) * ((s⁻¹ : Aˣ) : A))) := by
          rw [show (s : A) * d i ((s⁻¹ : Aˣ) : A)
                = -(d i (s : A) * ((s⁻¹ : Aˣ) : A)) by linear_combination hd]
    _ = -(((s⁻¹ : Aˣ) : A) * ((s⁻¹ : Aˣ) : A) * d i (s : A)) := by ring

/-- **The logarithmic derivative of a unit is always closed.**

So symmetry of the Hessian is *not* lost when the potential is dropped: it is a
theorem about any unit, not a hypothesis. -/
theorem logDeriv_closed (s : Aˣ) : Closed (logDeriv (n := n) s) := by
  intro i j
  simp only [logDeriv]
  rw [d_mul, d_mul, d_inv, d_inv, d_comm i j (s : A)]
  ring


end SCD.Gradient
