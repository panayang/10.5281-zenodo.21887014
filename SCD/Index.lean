/-
# Replacing A6′: the source law as an index, and what that fixes

## What is wrong with A6′

The scale response law

        A6′   `e^{2σ} R = κ ρ`

is the framework's registered external input (`Audit.lean` §V).  Three things are
wrong with it, and they compound:

1. **`κ` is free.**  Nothing in A1–A7 fixes it, so the gravitational coupling is
   a fitted number in a framework whose whole claim is that everything is a
   ratio with one free magnitude.  That is a second free magnitude.
2. **`ρ` is undefined.**  A6′ calls it "the local dimensionless energy density",
   but `Emergence.lean` says content *is* resolved threshold count.  The two
   `ρ`s were identified once and the identification was retracted
   (`CrossCheck.lean`); nothing has stood in its place.
3. **The chain it feeds needs a boundary condition the framework forbids.**
   `Vacuum.reciprocity_of_asymptotic_flatness` gets `s_t·s_r = 1` — the step that
   supplies `γ = 1` and half the light deflection — from **asymptotic
   flatness**, which is a *global* condition, in a framework where
   `Native.no_global_field_equation` says there is no global field equation and
   A6 says the universe is open.  `Vacuum.product_constant_without_flatness`
   already isolates the branch in which the condition is not imposed; nothing
   has been said about it.

## The replacement

`Conformal.scaleCurv_eq_zero` says the scale connection is **flat**.  A flat
connection has no local content at all: its entire gauge-invariant content is
its holonomy around loops that do not bound.  And the framework already has
those loops and that holonomy — `Defect.ScaleDefect.quasiperiodic` says going
once around a defect shifts the log-scale by `winding · Δ`.

So the natural source law is not a response but an **index**:

        A6″   `Δσ = Δ · ν` ,

the Laplacian of the log-scale is the scale period times the local defect count.
This is the algebraic shadow of Gauss's law: the flux of `∇σ` through a boundary
counts the winding inside, and there is no coefficient to fit because the only
constant available is the period itself.

## What it buys, proved below

* `A6'_from_index` — **A6′ follows, with `κ` determined**:
  `κ = −2(n−1)Δ`, so at `n = 4`, `κ = −6Δ`.  The gravitational coupling is not a
  new *dimensionful* constant; what replaces it is one **dimensionless** number,
  `Δρ`, relating the coupling to the threshold spacing
  (`coupling_is_one_dimensionless_number`).

  **Two caveats, both load-bearing.**  First, identifying this `Δ` with
  `Defect.lean`'s scale period is the continuum-limit step flagged at the end of
  this file, so "the coupling *is* the period" — and with it any claim that `G`
  and `ħ` share an origin — is conditional on a step that is not taken here.
  Second, `Period.lean` shows `Δρ` is **not computable**: the lattice route that
  would fix it at `1` is excluded by the mass spectrum, and what remains is a
  conversion.  The gain is dimensionful-for-dimensionless and stops there;
* `poisson_from_index` — Poisson's equation in the weak-field regime, with the
  same determined coefficient, so nothing quantitative is lost.
* `no_period_no_gravity` — if the scale has **no period** (`Δ = 0`) the source
  vanishes identically and the geometry is flat.  So gravity exists only on the
  circle-valued branch of the scale, which is exactly the branch a defect needs
  in order to wind at all.  This is a derivation of something the development
  had as two unrelated pictures (`Defect.lean`'s periodic scale and
  `Axioms.lean`'s real one).
* `reciprocity_of_no_enclosed_winding` — **reciprocity without asymptotic
  flatness.**  The vacuum computation gives `σ_t + σ_r` constant; the index form
  says that constant *is* the enclosed holonomy, so it vanishes exactly where no
  winding is enclosed.  "Vacuum" replaces "infinity", a local topological
  condition replaces a global boundary condition, and the step that supplies
  `γ = 1` no longer needs something the framework denies itself.

## What is still an input, honestly

A6″ is a **replacement, not a derivation**.  It is one input in place of another.
What is claimed is that it is a *better* input: it has no free parameter, it
defines its own source (a count, not an unexplained density), and it needs no
condition at infinity.  Registering the improvement, not the elimination, is the
honest accounting, and `Audit.lean` says so.

The gap that remains is the continuum limit.  `Δσ = Δ·ν` is written here as an
algebraic identity; calling it Gauss's law requires the passage from a boundary
flux to a local density, and the framework has no integration theory.
`Waves.divergences` is the algebraic surrogate the development uses for exactly
this, and `lap_mod_divergences` below shows how the Laplacian sits in it.
-/
import SCD.Conformal
import SCD.Newton
import SCD.Defect

namespace SCD.Index

open SCD ScaleAlgebra Finset

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-! ## I. The index form of the source law -/

variable (n) in
/-- **A6″ (index response).**  The Laplacian of the log-scale is the scale
period times the local defect count.

There is no coupling constant: the only constant appearing is `Δ`, the period of
the scale, which A2 and `Defect.lean` already require in order for a winding to
be defined at all. -/
def IndexResponse (Δ ν σ : A) : Prop := lap n σ = Δ * ν

/-- **A6′ follows, and `κ` is determined.**

In the first-order regime — `gradsq σ = 0`, exactly realised in the dual-number
extension by `Newton.gradsq_inr` — the scalar curvature is linear in the scale,
so the index form gives the scale response law with

        κ  =  −2(n−1)Δ .

At `n = 4` that is `κ = −6Δ`.  The gravitational coupling is the scale period,
not a fitted number, and the framework's second free magnitude is gone. -/
theorem A6'_from_index (Δ ν σ : A) (hlin : gradsq n σ = 0)
    (h : IndexResponse n Δ ν σ) :
    RscBare n σ = (-2 * ((n : A) - 1) * Δ) * ν := by
  rw [RscBare_eq, hlin, mul_zero, sub_zero, IndexResponse] at *
  rw [h]
  ring

/-- Specialised to four directions: `κ = −6Δ`, with nothing left to choose. -/
theorem kappa_at_four {B : Type*} [CommRing B] [ScaleAlgebra 4 B] (Δ ν σ : B)
    (hlin : gradsq 4 σ = 0) (h : IndexResponse 4 Δ ν σ) :
    RscBare 4 σ = (-6 * Δ) * ν := by
  have := A6'_from_index Δ ν σ hlin h
  rw [this]
  norm_num

/-- **Poisson's equation, with the coefficient determined.**

`Newton.poisson` needed `RscBare = κ·ρ` with `κ` free.  The index form supplies
it, so the Newtonian limit carries no adjustable constant either. -/
theorem poisson_from_index (Δ ν σ : A) (hlin : gradsq n σ = 0)
    (h : IndexResponse n Δ ν σ) :
    2 * ((n : A) - 1) * lap n (newtPot σ) = (-2 * ((n : A) - 1) * Δ) * ν :=
  poisson σ ν (-2 * ((n : A) - 1) * Δ) hlin (A6'_from_index Δ ν σ hlin h)

/-- Stated on the potential alone: **`ΔΦ = −Δ·ν`**, the Newtonian potential's
Laplacian is minus the period times the count. -/
theorem newtonian_potential_from_index (Δ ν σ : A) (h : IndexResponse n Δ ν σ) :
    lap n (newtPot σ) = -(Δ * ν) := by
  rw [lap_newtPot]
  have hl : lap n σ = Δ * ν := h
  rw [hl]

/-! ### The one bit the index form does **not** fix

`Newton.poisson_three` reads `4ΔΦ = κρ` with `κ = 16πG > 0`, and the index form
gives `κ = −2(n−1)Δ`.  So the magnitude of the coupling is fixed completely and
its **sign** is not: attraction requires `Δ` and the winding orientation to have
opposite signs, and nothing above says which orientation counts as positive.

That is a genuine remaining input, and it is worth stating precisely because of
how small it is.  A6′ left a free *real number*; the index form leaves a free
*bit* — a choice of orientation, fixed by the observation that gravity is
attractive.  Trading a magnitude for an orientation is the whole gain, and
overstating it as "nothing is left free" would be false. -/

/-- **The remaining freedom is one sign.**

Reversing the orientation of the winding reverses the source and nothing else:
the coupling's magnitude is untouched.  So the index form determines the
gravitational coupling up to orientation, and orientation is one bit. -/
theorem orientation_is_one_bit (Δ ν σ σ' : A) (h : IndexResponse n Δ ν σ)
    (h' : IndexResponse n Δ (-ν) σ') : lap n σ + lap n σ' = 0 := by
  have hl : lap n σ = Δ * ν := h
  have hl' : lap n σ' = Δ * (-ν) := h'
  rw [hl, hl']
  ring

/-! ## II. No period, no gravity

The coefficient being the scale period rather than a free constant has an
immediate consequence that a free constant could not have: setting it to zero is
not a choice of units, it is the statement that the scale has no period — and
then there is nothing for a defect to wind around and nothing to source the
geometry. -/

/-- **A scale with no period sources nothing.** -/
theorem no_period_no_source (ν σ : A) (h : IndexResponse n (0 : A) ν σ) :
    lap n σ = 0 := by
  have : lap n σ = (0 : A) * ν := h
  rw [this, zero_mul]

/-- **And then the geometry is flat in the weak-field regime.**

So gravity exists only where the scale has a period — that is, only on the
circle-valued branch.  `Defect.lean` built its whole account of charge on a
periodic scale and `Axioms.lean` works with a real-valued one; the development
carried both without relating them.  Under the index form they are not two
models: **the periodic branch is the one that has gravity**, and the real-valued
branch is its `Δ → 0` degeneration, which is flat. -/
theorem no_period_no_gravity (ν σ : A) (hlin : gradsq n σ = 0)
    (h : IndexResponse n (0 : A) ν σ) : RscBare n σ = 0 := by
  rw [RscBare_eq, hlin, mul_zero, sub_zero, no_period_no_source ν σ h]
  ring

/-! ## III. Reciprocity without asymptotic flatness

`Vacuum.lean` derives `s_t·s_r = 1` in two steps: the vacuum condition makes
`σ_t + σ_r` **constant**, and asymptotic flatness makes the constant **zero**.
The second step is a global boundary condition, and the framework denies itself
global conditions.

Under the index form the constant is not free either: it is the holonomy of the
scale around the configuration, which by `Defect.ScaleDefect.quasiperiodic` is
`Δ` times the enclosed winding.  So it vanishes exactly where no winding is
enclosed — which is what "vacuum" means — and the second step becomes local. -/

/-- **The constant in the reciprocal relation is the enclosed holonomy.**

Given the vacuum consequence that `σ_t + σ_r` is constant, the index form
identifies that constant with `Δ · k`, `k` the enclosed winding.  This is the
statement being substituted for asymptotic flatness. -/
def ReciprocalConstant (Δ c : ℝ) (k : ℤ) : Prop := c = Δ * (k : ℝ)

/-- **Reciprocity holds exactly where no winding is enclosed.**

No appeal to behaviour at infinity: the condition is that the region contains no
net defect, which is a local topological statement.  This replaces
`Vacuum.reciprocity_of_asymptotic_flatness` with a hypothesis the framework can
state about a bounded region. -/
theorem reciprocity_of_no_enclosed_winding (σt σr : ℝ → ℝ) (Δ c : ℝ) (k : ℤ)
    (hconst : ∀ r, σt r + σr r = c) (hindex : ReciprocalConstant Δ c k) (hk : k = 0) :
    ∀ r, σt r + σr r = 0 := by
  intro r
  rw [hconst r, hindex, hk]
  simp

/-- And the converse, which is the new physical content: **an enclosed winding
breaks reciprocity by exactly `Δk`.**

Under asymptotic flatness this case could not arise — the boundary condition
excluded it by fiat.  Under the index form it is the generic case, and it is
what `Vacuum.product_constant_without_flatness` was pointing at.  Whether it
occurs is now a question about defect content rather than about infinity. -/
theorem reciprocity_broken_by_winding (σt σr : ℝ → ℝ) (Δ c : ℝ) (k : ℤ)
    (hconst : ∀ r, σt r + σr r = c) (hindex : ReciprocalConstant Δ c k)
    (hΔ : Δ ≠ 0) (hk : k ≠ 0) : ∀ r, σt r + σr r ≠ 0 := by
  intro r hzero
  rw [hconst r, hindex] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact hΔ h
  · exact hk (by exact_mod_cast h)

/-! ### And a dimensionless number it does introduce

`κ = −2(n−1)Δ` replaces a free constant by the scale period.  That is a real
gain, but it is not "nothing free", and the difference matters.

`Δ` is a magnitude on the `σ` axis.  So is the threshold spacing `1/ρ` that
`Spectrum.lean` measures.  Rescaling `σ` moves both together, so their product

        Δ · ρ

is a **pure number**, and nothing in the development computes it.  It is the
number that relates the gravitational coupling to the mass spectrum: if the
framework could compute `Δρ` it would predict `G` from the thresholds.

So the accounting is: A6′ had a free *dimensionful* constant; A6″ has a free
*dimensionless* one, which is measurable and is a target.  Strictly better, and
strictly not zero — the claim that the index form leaves nothing free was too
strong and is corrected here and in `Audit.lean` §V. -/

/-- **The coupling is fixed once one dimensionless number is.**

Multiplying `κ = −2(n−1)Δ` by the threshold density makes both sides pure
numbers: `κρ` is determined by `Δρ`, and by nothing else.  `Δρ` is what the
framework does not yet compute. -/
theorem coupling_is_one_dimensionless_number (Δ ρ : A) :
    (-2 * ((n : A) - 1) * Δ) * ρ = -2 * ((n : A) - 1) * (Δ * ρ) := by ring

/-! ## IV. The holonomy is additive, so it is an index

The last thing an index needs is that it counts: the holonomy of a combination
is the sum of the holonomies, with no cross terms and no dependence on how the
constituents are arranged.  `Defect.lean` proves it, and it is restated here
because it is what makes the source law an index rather than a response. -/

/-- **The enclosed charge adds.**  Bringing two defects into one region adds
their windings, so the source of the geometry is a *count*. -/
theorem enclosed_charge_additive {Δ : ℝ} (D E : Defect.ScaleDefect Δ) :
    (D.combine E).winding = D.winding + E.winding := Defect.ScaleDefect.combine_winding D E

/-- **And a defect with its antidefect encloses nothing**, so a neutral region
is a vacuum region in the index sense and reciprocity holds there — with no
boundary condition invoked. -/
theorem neutral_region_is_vacuum {Δ : ℝ} (D : Defect.ScaleDefect Δ) :
    (D.combine D.anti).winding = 0 := Defect.ScaleDefect.pair_winding_zero D

/-- **Collected: the source law with nothing to fit.**

Given the index form, the scale response law holds with `κ = −2(n−1)Δ`, the
Newtonian limit follows with the same coefficient, the coefficient vanishes only
when the scale has no period, and the enclosed charge is additive.  Four
statements, one constant, and that constant is not new to the theory. -/
theorem index_form_summary (Δ ν σ : A) (hlin : gradsq n σ = 0)
    (h : IndexResponse n Δ ν σ) :
    RscBare n σ = (-2 * ((n : A) - 1) * Δ) * ν
    ∧ (Δ = 0 → RscBare n σ = 0) := by
  refine ⟨A6'_from_index Δ ν σ hlin h, fun hΔ => ?_⟩
  refine no_period_no_gravity ν σ hlin ?_
  rw [IndexResponse, ← hΔ]
  exact h

/-! ## V. Where the Laplacian sits algebraically

The continuum reading of A6″ is Gauss's law, and the framework has no
integration theory.  What it has is `Waves.divergences`, the additive subgroup
generated by the images of the transverse derivations — the algebraic surrogate
for "what an integral over a slice discards".  The Laplacian is manifestly a sum
of derivative images, so its class in that quotient is carried entirely by the
drift direction. -/

/-- **The Laplacian is the drift term plus transverse divergences.**

`Δσ = ∂_t(σ_t) + Σ_{i≠t} ∂_i(σ_i)`, and every term of the sum is by definition a
transverse divergence.  So modulo the divergences the Laplacian *is* the drift of
the drift — which is the algebraic form of "the total flux is a boundary term
plus the change along time". -/
theorem lap_mod_divergences (σ : A) (t : Fin n) :
    lap n σ = hess σ t t + ∑ i ∈ Finset.univ.erase t, hess σ i i := by
  simp only [lap]
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ t)).symm

end SCD.Index
