/-
# How big the anisotropic non-commutative correction is, and where it is not zero

`Anisotropic.lean` closes by saying the directional commutator `[σ_a, σ_b]` is
**zeroth order in gradients**, hence "the leading quantum-gravitational correction
is not derivative-suppressed", hence "whatever bounds anisotropy bounds it
directly" — and that putting a number on it had not been done.

Going after the number does not produce one.  It produces two corrections and a
sharper question, and the corrections are worth more than the number would have
been.

## I.  The claim carrying that reading has no content

`Anisotropic.dirCommutator_is_leading` is proved by `⟨rfl, rfl⟩`.  Its statement
is two definitional unfoldings; the entire order-counting argument lives in its
docstring and none of it is in the theorem.  Applying `Anchor.Falsifiable`:
`leading_claim_has_no_failing_instance`.

This is the fifth occurrence of the register's recurring failure — a docstring
carrying a physical claim that the theorem underneath does not make — and unlike
the four in §V.n this one had a *physical* consequence, since "not
derivative-suppressed" is what made the sector look experimentally accessible.

## II.  In the framework's own deformation it is second order in gradients

The development constructs exactly one non-commutative algebra: `Deformation.lean`'s
first-order deformation `A_ħ = A[ħ]/(ħ²)`, whose commutator is `ħ` times the
Poisson bracket (`Deformation.star_commutator`), with the bracket supplied by
`Deformation.canonical`:

        {f, g} = ∂_q f · ∂_p g − ∂_q g · ∂_p f .

Evaluating the directional commutator *in that algebra*:

> **`[σ_a, σ_b]_⋆ = ħ · ( ∂_q σ_a ∂_p σ_b − ∂_q σ_b ∂_p σ_a )`**
> (`dir_commutator_star`).

Two gradients, and an explicit `ħ`.  So:

* the **relative** claim of `Anisotropic.lean` survives — the isotropic
  correction `[∂_aσ, ∂_bσ]` becomes `ħ{∂_aσ, ∂_bσ}`, which carries **four**
  gradients, so the directional one is indeed ahead by two;
* the **absolute** claim does not.  "Zeroth order in gradients" is a property of
  how the expression is *written*, not of its value in the only non-commutative
  algebra the framework has.  It is `ħ × (∇σ)²`, and `∇σ` is the gravitational
  field.  **Withdrawn.**

The two files could only both be right if the anisotropic sector's
non-commutativity were intrinsic rather than deformation-induced.  Nothing in the
development constructs such an algebra, and until something does, the deformation
is what the symbol means.

## III.  And it vanishes in every configuration anyone measures in

The bracket is a wedge of two gradients, so it dies when they are parallel:

> **`collinear_gradients_kill_it`** — if every directional log-scale has gradient
> proportional to the gradient of one common function `u`, with a
> direction-dependent factor, then the correction is identically zero.

That hypothesis is exactly **staticity plus spherical symmetry**: there, every
`σ_a` is a function of the radial coordinate alone, so every `∇σ_a` is radial and
any two of them are parallel.  Hence

> **the leading anisotropic non-commutative correction vanishes identically in
> the Schwarzschild configuration** (`spherical_static_gives_zero`).

Which is the whole solar system to the accuracy of its own spherical symmetry.
So the reason no number has been put on this sector is not that the work was
skipped: **the effect is zero at leading order in the configuration where the
spin-sector bounds are taken.**  Torsion balances and co-magnetometers sitting in
a static, very nearly spherical field are looking where the framework says there
is nothing.

**It is not identically zero as a matter of algebra** — `noncollinear_witness`
exhibits a configuration in the three-direction model of `Explanation.lean` where
it equals `−1`.  So this is a genuine selection rule and not a triviality.

## IV.  Where it is not zero, and what that costs to use

Non-collinear scale gradients require the directional log-scales to depend on
more than one variable, i.e. a source that is **not spherically symmetric**.  The
two available in the laboratory are the oblateness of the source and its
rotation: in an axisymmetric field the scales depend on `r` and on the polar
angle, and two of their gradients are then generically non-parallel.

So the framework's own statement of where to look is: **the effect is sourced by
the departure from spherical symmetry**, suppressed relative to a naive estimate
by that departure — `J₂ ∼ 10⁻³` for the Earth — *and* by two powers of `∇σ`,
*and* by `ħ`.  That is a much smaller and much better-defined target than "not
derivative-suppressed".

## V.  Why there is still no number, stated precisely

One item is missing and it is nameable:

> **a dictionary from a weight-two scale quantity to an energy.**

`[σ_a, σ_b]` has weight two under `σ ↦ cσ` (`Weight.lean`), so it is the square
of a log-scale interval, not an energy.  Converting it into a spin-sector energy
shift — the thing a co-magnetometer measures — requires knowing how the
rotational label couples to matter, and the framework **has no matter sector**.
`dirCommutator_is_wedge` says the object *is* a rotational label, which is
suggestive and is not a coupling.

That is the whole obstruction, and it is one item rather than a fog.  Until it
exists, the honest statement of this sector is:

> the leading correction is `ħ` times the wedge of two directional scale
> gradients; it vanishes in every static spherically symmetric configuration; it
> is sourced by the departure from spherical symmetry; and its conversion to an
> observable energy is not available.

`Anchor.lean`'s ledger is unchanged by this file — no prediction is added, and
one docstring claim is removed.
-/
import SCD.Anisotropic
import SCD.Deformation
import SCD.Anchor

namespace SCD.NCSize

open SCD Deformation MvPolynomial

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-! ## I. The magnitude, in the framework's own deformation -/

/-- **The directional commutator, evaluated in the deformation.**

`Deformation.star_commutator` says the `ħ`-coefficient of the star commutator is
the Poisson bracket; `Deformation.canonical_poisson` says what that bracket is.
Together:

        [σ_a, σ_b]_⋆  =  ħ ( ∂_q σ_a ∂_p σ_b − ∂_q σ_b ∂_p σ_a ) .

**Two gradients.**  `Anisotropic.lean`'s "zeroth order in gradients" describes the
expression, not its value here. -/
theorem dir_commutator_star (p q : Fin n) (σ : Fin n → A) (a b : Fin n) :
    (star (canonical (A := A) p q) (σ a, 0) (σ b, 0)).2
      - (star (canonical (A := A) p q) (σ b, 0) (σ a, 0)).2
      = ScaleAlgebra.d q (σ a) * ScaleAlgebra.d p (σ b)
        - ScaleAlgebra.d q (σ b) * ScaleAlgebra.d p (σ a) :=
  (star_commutator (canonical (A := A) p q) (σ a, 0) (σ b, 0)).2

/-- **The isotropic correction is two gradients further down.**

`NCConformal`'s object is `[∂_aσ, ∂_bσ]`, whose `ħ`-coefficient is the bracket of
two *gradients* — four derivatives in all.  So the relative claim of
`Anisotropic.lean` stands even though the absolute one does not. -/
theorem iso_commutator_star (p q : Fin n) (σ : A) (a b : Fin n) :
    (star (canonical (A := A) p q) (ScaleAlgebra.d a σ, 0) (ScaleAlgebra.d b σ, 0)).2
      - (star (canonical (A := A) p q) (ScaleAlgebra.d b σ, 0) (ScaleAlgebra.d a σ, 0)).2
      = ScaleAlgebra.d q (ScaleAlgebra.d a σ) * ScaleAlgebra.d p (ScaleAlgebra.d b σ)
        - ScaleAlgebra.d q (ScaleAlgebra.d b σ) * ScaleAlgebra.d p (ScaleAlgebra.d a σ) :=
  (star_commutator (canonical (A := A) p q)
    (ScaleAlgebra.d a σ, 0) (ScaleAlgebra.d b σ, 0)).2

/-! ## II. The selection rule -/

/-- **Collinear scale gradients kill the correction.**

If every directional log-scale has gradient proportional to `∇u` for one common
`u` — with a factor that may depend on the direction and on position — the
bracket vanishes identically.

The bracket is a wedge of two gradients, and a wedge of parallel vectors is
zero. -/
theorem collinear_gradients_kill_it (σ : Fin n → A) (u : A) (g : Fin n → A)
    (h : ∀ a i : Fin n, ScaleAlgebra.d i (σ a) = g a * ScaleAlgebra.d i u)
    (p q a b : Fin n) :
    (canonical (A := A) p q).poisson (σ a) (σ b) = 0 := by
  simp only [canonical_poisson, h]
  ring

/-- **Hence it vanishes in every static, spherically symmetric configuration.**

There every directional log-scale is a function of the radial coordinate alone,
which is the hypothesis above with `u` the radial coordinate and `g a = σ_a'`.
So the whole solar-system laboratory — where the spin-sector bounds are taken —
sits at exactly the locus where the framework says the effect is zero.

That is why no number has been put on this sector, and it is a better answer than
a number would have been: the experiments that would bound it are looking in the
wrong configuration. -/
theorem spherical_static_gives_zero (σ : Fin n → A) (r : A) (rate : Fin n → A)
    (hstatic : ∀ a i : Fin n, ScaleAlgebra.d i (σ a) = rate a * ScaleAlgebra.d i r)
    (p q a b : Fin n) :
    (canonical (A := A) p q).poisson (σ a) (σ b) = 0 :=
  collinear_gradients_kill_it σ r rate hstatic p q a b

/-! ## III. But it is not identically zero -/

section Witness

open Explanation

/-- Two directional log-scales with non-parallel gradients: `σ₀ = x₀`,
`σ₁ = x₁`. -/
noncomputable def crossed : Fin 3 → MvPolynomial (Fin 3) ℝ := ![X 0, X 1, 0]

/-- **A configuration where the correction is nonzero**, in the three-direction
model of `Explanation.lean`.  So the selection rule of §II is a genuine
restriction and not a triviality: the effect is absent for spherical symmetry
and present otherwise. -/
theorem noncollinear_witness :
    (canonical (A := MvPolynomial (Fin 3) ℝ) (n := 3) 0 1).poisson (crossed 0) (crossed 1)
      = -1 := by
  have h0 : (0 : Fin 3) ≠ 1 := by decide
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  simp only [canonical_poisson, Explanation.d_eq_pderiv, crossed,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    pderiv_X_self, pderiv_X_of_ne h0, pderiv_X_of_ne h1]
  ring

theorem correction_is_not_identically_zero :
    ∃ (σ : Fin 3 → MvPolynomial (Fin 3) ℝ) (p q a b : Fin 3),
      (canonical (A := MvPolynomial (Fin 3) ℝ) (n := 3) p q).poisson (σ a) (σ b) ≠ 0 :=
  ⟨crossed, 0, 1, 0, 1, by rw [noncollinear_witness]; norm_num⟩

end Witness

/-! ## IV. The claim that had no content -/

omit [ScaleAlgebra n A] in
/-- **`Anisotropic.dirCommutator_is_leading` has no failing instance.**

It is `⟨rfl, rfl⟩` — two definitional unfoldings — and every order-counting claim
attached to it lives in its docstring.  The `Anchor.lean` test applied once more,
and this time to a claim with a physical consequence: "not derivative-suppressed"
is what made the sector look accessible, and §I–§II withdraw it. -/
theorem leading_claim_has_no_failing_instance :
    ¬ Anchor.Falsifiable (fun σ : Fin n → A =>
        ∀ a b : Fin n,
          Anisotropic.dirCommutator σ a b = Quantum.ad (σ a) (σ b)) := by
  rintro ⟨σ, hσ⟩
  exact hσ fun _ _ => rfl

/-- **Collected: what this sector actually says.**

The correction is `ħ` times a wedge of two directional scale gradients; it
vanishes whenever those gradients are collinear, hence in every static
spherically symmetric configuration; and it is not identically zero. -/
theorem summary (σ : Fin n → A) (u : A) (g : Fin n → A)
    (h : ∀ a i : Fin n, ScaleAlgebra.d i (σ a) = g a * ScaleAlgebra.d i u)
    (p q a b : Fin n) :
    (canonical (A := A) p q).poisson (σ a) (σ b) = 0
    ∧ (∃ (τ : Fin 3 → MvPolynomial (Fin 3) ℝ) (p' q' a' b' : Fin 3),
        (canonical (A := MvPolynomial (Fin 3) ℝ) (n := 3) p' q').poisson (τ a') (τ b') ≠ 0) :=
  ⟨collinear_gradients_kill_it σ u g h p q a b, correction_is_not_identically_zero⟩

end SCD.NCSize
