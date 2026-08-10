/-
# One axiom system, not two

`Frame.lean` introduced A4′ (a scale per direction) after proving that the
original A4 (a single scalar scale) forbids Schwarzschild.  Left there, the
development would carry two mutually inconsistent axioms: `Conformal.lean`,
`Newton.lean`, `Covariance.lean` and `Singularity.lean` all work with the
scalar `σ` and the metric `e^{2σ}δ`, while `Frame.lean` declares the scale to
be directional.  A theory cannot have both.

This file removes the inconsistency by demoting the old axiom.  **A4′ is the
axiom; A4 is a theorem about its isotropic locus.**  Concretely:

* `DirScale.toMetric` gives the metric of a directional scale;
* `toMetric_of_isotropic` shows that an isotropic directional scale produces
  *exactly* the conformal metric `η_a s² δ_{ab}` — no approximation, no extra
  hypothesis;
* `ofScalar` embeds every scalar scale field as an isotropic directional one,
  and `isotropic_iff_ofScalar` shows the isotropic locus is precisely the image
  of that embedding.

So every theorem previously proved about `σ` is retained verbatim, now with a
sharp domain of validity: it is a statement about the isotropic sector of A4′.
Nothing is lost and the axiom list has one entry where it had two.

What this file does **not** do is compute curvature in the anisotropic sector.
That work is outstanding, and until it is done the geometric consequences of
A4′ are known only where the scale happens to be isotropic.  The axiom system
is now consistent; it is not yet complete.
-/
import SCD.Frame
import SCD.Conformal

namespace SCD

open ScaleAlgebra Frame

variable {n : ℕ} {A : Type*} [CommRing A]

namespace Frame.DirScale

/-- The measured metric of a directional scale field: diagonal in the frame,
with the local unit `s_a` in direction `a` and signature `η`. -/
def toMetric (E : DirScale n A) (η : Fin n → A) (a b : Fin n) : A :=
  (kron a b : A) * (η a * ((E.s a : A)) ^ 2)

end Frame.DirScale

namespace Unify

/-! ## The metric of a directional scale -/

/-- The metric of the *old* axiom A4: one scalar scale, `g = η e^{2σ} δ`. -/
def conformalMetric (u : Aˣ) (η : Fin n → A) (a b : Fin n) : A :=
  (kron a b : A) * (η a * ((u : A)) ^ 2)

/-- **The old axiom is the isotropic locus of the new one.**

If all directions carry the same scale `s`, the metric of A4′ is *literally*
the conformal metric of A4.  Every result proved in the conformal sector
therefore holds unchanged, as a statement about isotropic scale fields. -/
theorem toMetric_of_isotropic (E : DirScale n A) (η : Fin n → A)
    (h : E.Isotropic) (c : Fin n) :
    E.toMetric η = conformalMetric (E.s c) η := by
  funext a b
  simp only [DirScale.toMetric, conformalMetric, h a c]

/-- Every scalar scale is a directional scale, namely an isotropic one. -/
def ofScalar (u : Aˣ) : DirScale n A where
  s := fun _ => u

@[simp] theorem ofScalar_isotropic (u : Aˣ) : (ofScalar (n := n) u).Isotropic := by
  intro a b; rfl

@[simp] theorem ofScalar_toMetric (u : Aˣ) (η : Fin n → A) :
    (ofScalar (n := n) u).toMetric η = conformalMetric u η := by
  funext a b
  simp only [DirScale.toMetric, conformalMetric, ofScalar]

/-- **The isotropic locus is exactly the image of the scalar theory.**

An `n`-direction scale field is isotropic if and only if it is `ofScalar u` for
some unit `u`.  So the old axiom is not merely implied by the new one — it is
precisely the new one restricted to a sub-locus, with nothing left over. -/
theorem isotropic_iff_ofScalar [NeZero n] (E : DirScale n A) :
    E.Isotropic ↔ ∃ u : Aˣ, E = ofScalar u := by
  constructor
  · intro h
    refine ⟨E.s ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, ?_⟩
    cases E with
    | mk s =>
      simp only [ofScalar, DirScale.mk.injEq]
      funext a
      exact h a _
  · rintro ⟨u, rfl⟩
    exact ofScalar_isotropic u

/-! ## The bridge to the scalar sector

`ScaleField` (A2/A3) carries a log-scale `σ` together with its unit `s = e^σ`.
It embeds as an isotropic directional scale, and the curvature that
`Conformal.lean` computes from `σ` is the curvature of that embedded metric. -/

end Unify

variable [ScaleAlgebra n A]

namespace ScaleField

/-- A scalar scale field, viewed as an isotropic directional scale field. -/
def toDirScale (F : ScaleField n A) : DirScale n A := Unify.ofScalar F.s

end ScaleField

namespace Unify

theorem toDirScale_isotropic (F : ScaleField n A) :
    F.toDirScale.Isotropic := ofScalar_isotropic F.s

/-- **The conformal sector sits inside A4′ exactly.**  The metric obtained from
A2/A3 by the new axiom is the metric the old axiom postulated. -/
@[simp] theorem toDirScale_toMetric (F : ScaleField n A) (η : Fin n → A) :
    F.toDirScale.toMetric η = conformalMetric F.s η :=
  ofScalar_toMetric F.s η

/-- Collected coherence statement.

For any scalar scale field `F`:
* its directional embedding is isotropic;
* the metric it induces under A4′ equals the conformal metric of A4;
* consequently the curvature computed in `Conformal.lean` from `F.σ` is the
  curvature of the A4′ metric of `F.toDirScale`.

This is the precise sense in which the earlier development is a sub-theory of
the present one rather than a competitor to it. -/
theorem sector_coherence (F : ScaleField n A) (η : Fin n → A) :
    F.toDirScale.Isotropic
    ∧ F.toDirScale.toMetric η = conformalMetric F.s η
    ∧ (∀ c : Fin n, F.toDirScale.toMetric η = conformalMetric (F.toDirScale.s c) η) :=
  ⟨toDirScale_isotropic F, toDirScale_toMetric F η,
    fun c => toMetric_of_isotropic _ η (toDirScale_isotropic F) c⟩

/-! ## Where anisotropy actually shows up

The two sectors are distinguished by a single observable: whether the metric is
a multiple of the bare bookkeeping.  Under isotropy every direction is scaled
alike, so the ratio `g_aa / η_a` is direction-independent.  Anisotropy is
exactly the failure of that. -/

/-- Under isotropy the metric is a common multiple of the signature. -/
theorem isotropic_ratio_const (E : DirScale n A) (η : Fin n → A)
    (h : E.Isotropic) (a b : Fin n) :
    E.toMetric η a a * η b = E.toMetric η b b * η a := by
  unfold DirScale.toMetric
  rw [kron_self, kron_self, h a b]
  ring

/-- Conversely, if two directions carry different squared scales the field is
not isotropic — this is the observable that Schwarzschild needs and that the
scalar axiom could not supply. -/
theorem not_isotropic_of_ne (E : DirScale n A) (a b : Fin n)
    (h : ((E.s a : A)) ^ 2 ≠ ((E.s b : A)) ^ 2) : ¬ E.Isotropic := by
  intro hiso
  exact h (by rw [hiso a b])

end Unify

end SCD
