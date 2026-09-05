/-
# The amendment, and why it is not a refactor

`Gradient.lean` measured A2 and found its content is a unit; `Torus.lean` showed
the one thing A2 adds beyond the unit — exactness of the logarithmic derivative —
fails in every dimension.  The obvious next move is to restate `Axioms.lean` and
push the change through everything that imports it.

**That move is not made, and this file is why.**  What the refactor was for was
information: *which results need the potential.*  That information is available
as theorems, and once it is, the refactor buys only tidiness.

## What is proved

* `sig_eq_logDeriv` — a scale field's gradient **is** the logarithmic derivative
  of its unit.  Nothing is chosen: `d s = s · sig σ` and `s` is invertible;
* `same_unit_same_geometry` — two scale fields with the same unit have the same
  geometry, all of it: Hessian, `gradsq`, Laplacian, deformation, Riemann and
  Ricci.  **This is the amendment's payoff, as a theorem rather than an edit**;
* `ofUnitOfPotential` — and the axiom is recovered from a unit together with any
  `σ` whose gradient is that logarithmic derivative.  So A2 is exactly *a unit,
  plus a witness that its logarithmic derivative is exact*;
* `potential_unique_up_to_fiducial` — two potentials for one unit differ by
  something every derivation kills, which is `Axioms.IsFiducial`'s condition.
  **A5's freedom is exactly the choice of potential**, and nothing else.

## So the recommendation, stated plainly

Leave `Axioms.lean` alone.  The refactor would rewrite the file every other file
imports, in order to say something the four theorems above already say, and the
register has been burned before by changes made because they were tidy.

What *is* worth doing is one paragraph: `Postulates.lean`'s statement of A2 now
records that the potential is a choice, invisible to the geometry, unique up to a
fiducial, and that its **existence** is the axiom's real content.  That is the
same information at the place a reader meets the axiom, with none of the churn.

## What this does not settle

Whether A2 *should* assume exactness is not a question about formalisation and
this file does not answer it.  What is now on the table is the choice, stated
precisely: assume the potential exists and take the `ℝ` branch of A3′, or drop it
and keep both branches, at the cost that `ScaleField` is no longer the carrier —
and `Dual.lean` says gravity wants the second.  The framework has not chosen; it
had not previously known it was choosing.
-/
import SCD.Torus

namespace SCD.Amendment

open SCD ScaleAlgebra Gradient


open SCD ScaleAlgebra Gradient

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-- **A scale field's gradient is the logarithmic derivative of its unit.**

Nothing is chosen: `d s = s · sig σ` and `s` is invertible. -/
theorem sig_eq_logDeriv (F : ScaleField n A) (i : Fin n) :
    sig F.σ i = logDeriv F.s i :=
  (Units.mul_right_inj F.s).mp ((F.d_s i).symm.trans (logDeriv_spec F.s i))

/-- **Two scale fields with the same unit have the same geometry — all of it.**

This is the amendment's payoff, as a theorem rather than a refactor: every
geometric consequence of A2 factors through the *unit*, so the log-scale is
carrying nothing the geometry reads. -/
theorem same_unit_same_geometry (F G : ScaleField n A) (h : F.s = G.s) :
    (∀ i j : Fin n, hess F.σ i j = hess G.σ i j)
      ∧ gradsq n F.σ = gradsq n G.σ
      ∧ lap n F.σ = lap n G.σ
      ∧ (∀ i j : Fin n, Defm n F.σ i j = Defm n G.σ i j)
      ∧ (∀ a b c e : Fin n, Rm F.σ a b c e = Rm G.σ a b c e)
      ∧ (∀ b e : Fin n, Ric F.σ b e = Ric G.σ b e) := by
  have hg : ∀ i : Fin n, sig F.σ i = sig G.σ i := by
    intro i
    rw [sig_eq_logDeriv, sig_eq_logDeriv, h]
  exact geometry_congr hg

/-- **And the axiom is recovered from a unit plus a potential.**

Given a unit and any `σ` whose gradient is its logarithmic derivative, the scale
field is rebuilt.  So A2 is exactly "a unit, together with a witness that its
logarithmic derivative is exact". -/
def ofUnitOfPotential (s : Aˣ) (σ : A) (hσ : ∀ i : Fin n, d i σ = logDeriv s i) :
    ScaleField n A where
  σ := σ
  s := s
  d_s i := by rw [logDeriv_spec s i, ← hσ i]; rfl

@[simp] theorem ofUnitOfPotential_s (s : Aˣ) (σ : A) (hσ : ∀ i : Fin n, d i σ = logDeriv s i) :
    (ofUnitOfPotential s σ hσ).s = s := rfl

/-- **The potential is unique up to a fiducial.**

Two potentials for the same unit differ by something every derivation kills,
which is `Axioms.IsFiducial`'s condition — so A5's freedom is exactly the choice
of potential, and nothing else. -/
theorem potential_unique_up_to_fiducial (s : Aˣ) (σ τ : A)
    (hσ : ∀ i : Fin n, d i σ = logDeriv s i) (hτ : ∀ i : Fin n, d i τ = logDeriv s i) (i : Fin n) :
    d i (σ - τ) = 0 := by
  rw [d_sub, hσ i, hτ i, sub_self]

/-- **The amendment, stated once.**

A2's content is a unit; the potential is a choice that the geometry cannot see
and that is unique up to a fiducial; and what A2 adds beyond the unit is the
assertion that a potential exists at all — which `Torus.torGradient_not_isExact`
shows is a real assumption in every dimension. -/
theorem what_A2_adds (F G : ScaleField n A) (h : F.s = G.s) :
    (∀ i : Fin n, sig F.σ i = sig G.σ i) ∧ (∀ i : Fin n, d i (F.σ - G.σ) = 0) := by
  have hg : ∀ i : Fin n, sig F.σ i = sig G.σ i := by
    intro i; rw [sig_eq_logDeriv, sig_eq_logDeriv, h]
  exact ⟨hg, fun i => by rw [d_sub]; exact sub_eq_zero.mpr (hg i)⟩


end SCD.Amendment
