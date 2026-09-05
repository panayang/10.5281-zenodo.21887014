/-
# The source law A4′ can carry, and the breathing mode — including a correction
# to §V.ax

§V.ax found A6′'s form presupposes one conformal factor and asked for a law that
does not.  This file writes it, and then follows the wave question far enough to
find that **two claims in the development do not have the support they state —
one of them mine, one commit old.**

## I.  The merge

`RscBare`'s design goal was *no invertibility hypothesis*, which is why the
conformal factor is kept explicit.  A4′ makes that goal free: it supplies
`w : Fin n → Aˣ`, and **units are invertible by definition**.  So in the
directional sector the law can be written on the true scalar curvature:

        `DirSource` :   `∑_b η_b w_b⁻¹ R_bb  =  κ·ρ` .

No bare form, no single factor, nothing presupposed about isotropy.
`dirSource_isotropic` reduces it: on the isotropic locus it is
`∑_b η_b R_bb = κ·(wρ)`, so A6′'s `ρ` and this `ρ` differ by the conformal factor
— the familiar coordinate-density versus proper-density distinction, which A6′
could absorb and this cannot.  `kappa_from_dirSource` then recovers
`κ = −2(n−1)Δ` where the density is cancellable.

**That is the merge §V.at was looking for**: A4′ supplies exactly the
invertibility A6′ was contorted to avoid, and the two axioms fit in the
directional sector in a way they never did in the isotropic one.

## II.  Correction to §V.ax, which is mine

§V.ax said: *No interferometer can see a scale wave.  It is not a strain*, citing
`Light.michelson_morley_null`.  **That overstates the theorem.**  Its hypothesis
is a single `E : DirScale n A` — **one** scale pattern — and it compares two null
directions at one point.  It rules out finding a *static* anisotropy.  A wave is
a scale that differs between the arms and between emission and return, and the
theorem says nothing about that case.

The claim is withdrawn.  What survives is the narrower and still useful
statement: **a static scale pattern is invisible to an interferometer, at any
precision.**

## III.  And `Horizon.no_breathing_mode` does not have the reason it gives

`no_breathing_mode` is `(m−1) + 1 = m`, proved by `omega`.  Its physical content
is the subtraction in `scaleModes m = m - 1`, whose docstring justifies it:
*`Expressive.eval_not_invariant` says a uniform rescaling is a fiducial shift,
and A5 declares fiducial shifts unobservable.*

But `Expressive.FiducialInvariant f` quantifies over `∀ σ c, f (fun x => σ x + c)
= f σ` — **one constant `c` added at every point** — and `diffPattern` measures
differences **between points**.  A breathing wave is uniform across *directions*
and varies across *points*.  `uniform_across_directions_still_varies` exhibits
that combination, and `nonconstant_scale_is_expressible` shows any such field is
separated by a fiducial-invariant functional.

> **A wave is not a fiducial shift, so A5 does not remove the breathing mode.**

And `Hyperbolic.vacuum_wave_is_null` already exhibits the mode: a non-constant
`σ`, uniform across directions, propagating on the null cone.

## IV.  But the conclusion survives, on a different ground

The framework does exclude breathing *radiation*, and its own files say why —
just not where `Horizon.lean` looks.  A scalar disturbance is sourced by the
**monopole**, and `Waves.monopole_does_not_radiate` freezes the monopole of a
conserved source, while `Dynamics.no_field_equation_of_nonconserved` says a
non-conserved source admits **no field equation at all**.  So:

> **The breathing mode is expressible but cannot be radiated by any source this
> framework can write a field equation for.**

Same prediction, different ground, and a different **scope**: the exclusion is
about radiation from conserved sources.  A free breathing wave — primordial, or
a boundary condition — is not excluded by anything here, and `Horizon.lean`'s
"the amplitude is identically zero, not small" is broader than what is proved.

This is §V.aq's pattern for the third time: a result kept and its standing
described correctly.

## What is not claimed

That `two_polarizations` is wrong.  With the monopole argument in place the count
`1 + 1` stands for radiation from conserved sources, which is the case
polarization tests examine.  What is wrong is only the **reason** `scaleModes`
gives for its subtraction, and it matters because the reason is what the register
has been citing as a discriminator.
-/
import SCD.Directional
import SCD.Expressive
import SCD.Waves

namespace SCD.Breathing

open SCD ScaleAlgebra Finset

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]


/-! ## I. The source law A4′ can carry -/

/-- **The source law A4′ can carry.**

The true scalar curvature equals `κ` times the density.  No bare form and no
single conformal factor, because A4′'s `w : Fin n → Aˣ` are **units** — the
invertibility `RscBare` was built to avoid needing is supplied by the axiom. -/
def DirSource (η : Fin n → A) (w : Fin n → Aˣ) (R : Fin n → A) (κ ρ : A) : Prop :=
  Directional.dirTrace η w R = κ * ρ

omit [ScaleAlgebra n A] in
/-- **On the isotropic locus it is A6′, with the density read the other way.**

The two `ρ`s differ by the conformal factor — coordinate density against proper
density — which A6′ could absorb and this law cannot. -/
theorem dirSource_isotropic (η : Fin n → A) (w : Aˣ) (R : Fin n → A) (κ ρ : A) :
    DirSource η (fun _ => w) R κ ρ ↔ (∑ b, η b * R b) = κ * (((w : Aˣ) : A) * ρ) := by
  rw [DirSource, Directional.dirTrace_isotropic]
  constructor
  · intro h
    calc (∑ b, η b * R b)
        = ((w : A)) * (((w⁻¹ : Aˣ) : A) * ∑ b, η b * R b) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
      _ = κ * ((w : A) * ρ) := by rw [h]; ring
  · intro h
    calc ((w⁻¹ : Aˣ) : A) * ∑ b, η b * R b
        = ((w⁻¹ : Aˣ) : A) * (κ * ((w : A) * ρ)) := by rw [h]
      _ = κ * ρ := by
          rw [show ((w⁻¹ : Aˣ) : A) * (κ * ((w : A) * ρ))
              = κ * ((((w⁻¹ : Aˣ) : A) * (w : A)) * ρ) by ring, Units.inv_mul, one_mul]

/-- **And the coupling comes out the same**, wherever the density is
cancellable. -/
theorem kappa_from_dirSource (η : Fin n → A) (hη : ∀ a, η a * η a = 1)
    (hηc : ∀ a b : Fin n, d b (η a) = 0) (w : Aˣ) (σ Δ ν ρ κ : A)
    (hlin : EtaTrace.gradsqE n η σ = 0) (hsrc : EtaTrace.lapE n η σ = Δ * ν)
    (hden : ((w : A)) * ρ = ν)
    (h : DirSource η (fun _ => w) (fun b => EtaTrace.RicE η σ b b) κ ρ) :
    (κ - (-2 * ((n : A) - 1) * Δ)) * ν = 0 := by
  have hR : (∑ b, η b * EtaTrace.RicE η σ b b) = (-2 * ((n : A) - 1) * Δ) * ν := by
    have := EtaTrace.RscE_eq η hη hηc σ
    rw [EtaTrace.RscE] at this
    rw [this, hlin, hsrc]; ring
  have h' := (dirSource_isotropic η w _ κ ρ).mp h
  rw [hR, hden] at h'
  linear_combination -h'

/-! ## II. A wave is not a fiducial shift -/

/-- **A scale that varies between points is expressible.**

`FiducialInvariant` quantifies over one constant added at every point; a field
that differs between two points is separated by a fiducial-invariant functional.
So A5 does not remove it. -/
theorem nonconstant_scale_is_expressible {X : Type*} (x₀ x₁ : X) (σ : X → ℝ)
    (h : σ x₁ ≠ σ x₀) :
    ∃ f : (X → ℝ) → ℝ, Expressive.FiducialInvariant f ∧ f σ ≠ f (fun _ => 0) := by
  refine ⟨fun τ => τ x₁ - τ x₀, fun τ c => by simp only; ring, ?_⟩
  simp only [sub_self]
  exact sub_ne_zero.mpr h

/-- **And "uniform across directions" is compatible with that.**

The breathing mode is uniform across directions and varies across points, which
is exactly the combination `scaleModes`' justification treats as impossible. -/
theorem uniform_across_directions_still_varies {X : Type*} (x₀ x₁ : X) (f : X → ℝ)
    (h : f x₁ ≠ f x₀) {m : ℕ} (a : Fin m) :
    ∃ σ : Fin m → X → ℝ, (∀ b c, σ b = σ c) ∧ σ a x₁ ≠ σ a x₀ :=
  ⟨fun _ => f, fun _ _ => rfl, h⟩

end SCD.Breathing
