/-
# The reciprocity chain, end to end and without a boundary condition

`s_t · s_r = 1` is the step that supplies `γ = 1` and half the light deflection.
It used to rest on two inputs, both registered:

1. that the vacuum makes `σ_t + σ_r` constant — the standard Ricci combination,
   taken as input in `Vacuum.lean` and `Schwarzschild.lean`;
2. that the constant is **zero** — asymptotic flatness, a *global* boundary
   condition, in a framework whose `Native.no_global_field_equation` denies
   itself global conditions.

Both now have replacements, and this file puts the chain together in one
setting so the seam is visible:

* (1) is **derived**, by `Diagonal.vacuum_scale_sum`, from A4′'s own metric with
  the connection certified by `Diagonal.metric_compatible`;
* (2) is **replaced**, by `Index.reciprocity_of_no_enclosed_winding`: under the
  index form of the source law the constant is the enclosed holonomy, so it
  vanishes where no winding is enclosed — a local topological condition instead
  of a condition at infinity.

## What the algebra says, and where each input enters

The chain is short once it is algebraic:

    vacuum + staticity  ⟹  every derivation kills σ_t + σ_r     (`sum_is_constant`)
                        ⟹  every derivation kills s_t·s_r        (`pair_is_constant`)
                        ⟹  s_t·s_r is a **constant unit**
    constant = 1        ⟺  reciprocity                           (`reciprocal_iff_one`)

The last line is an equivalence, not an implication, and that is the honest
shape of the thing: **the vacuum makes the product constant and says nothing
about which constant.**  `Vacuum.lean` fixes it by asymptotic flatness;
`Index.lean` fixes it by the enclosed winding.  Both are inputs, and the second
is the weaker one — it is local, and it has no free parameter.

The algebraic form also makes clear what "constant" means here without any
analysis: **annihilated by every derivation**.  Staticity gives that for free in
the transverse directions and the vacuum gives it in the radial one, so no
mean-value theorem is needed and `Vacuum.const_of_deriv_zero_and_vanishing`
becomes a convenience rather than a load-bearing step.

## Status of the two older files

`Schwarzschild.lean` and `Vacuum.lean` are the real-analytic shadow of this
chain.  They are retained — the cancellation is easiest to *see* in
`Schwarzschild.ricci_combination`, and the asymptotic-flatness argument is worth
keeping on record as the historical route — but **neither is load-bearing any
more**, and neither introduces anything this file does not derive or replace.
-/
import SCD.Diagonal
import SCD.Index
import SCD.Anisotropic

namespace SCD.Reciprocity

open SCD ScaleAlgebra Frame Anisotropic Diagonal

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-! ## I. From the vacuum to a constant -/

/-- **"Constant" without analysis.**  In an algebraic substrate a quantity is
constant when every derivation kills it.  Staticity supplies that transversally
and the vacuum supplies it radially, so no limit argument is needed. -/
def IsConstant (x : A) : Prop := ∀ b : Fin n, d b x = 0

/-- **The vacuum makes the scale sum constant.**

`Diagonal.vacuum_scale_sum` gives `σ_t' + σ_r' = 0` along the one direction
things vary in; staticity gives it along every other, trivially.  So the sum is
annihilated by every derivation. -/
theorem sum_is_constant (σ : Fin n → A) (r : Fin n)
    (hstat : ∀ a b : Fin n, b ≠ r → d b (σ a) = 0) (t : Fin n)
    (hvac : d r (σ t) + d r (σ r) = 0) :
    IsConstant (n := n) (σ t + σ r) := by
  intro b
  rw [d_add]
  by_cases hb : b = r
  · rw [hb]; exact hvac
  · rw [hstat t b hb, hstat r b hb, add_zero]

/-! ## II. From the constant sum to a constant product -/

/-- **And therefore the product of the two units is constant.**

`d(s_t s_r) = s_t s_r ·(σ_t' + σ_r')` by A2 applied in each direction, so a
constant sum of log-scales is a constant product of scales.  This is the step
that turns an additive statement into the multiplicative one reciprocity is
about. -/
theorem pair_is_constant (E : DirField n A) (t r : Fin n)
    (hsum : IsConstant (n := n) (E.lg t + E.lg r)) :
    IsConstant (n := n) (((E.s t * E.s r : Aˣ)) : A) := by
  intro b
  have ht : d b ((E.s t : Aˣ) : A) = ((E.s t : Aˣ) : A) * d b (E.lg t) := (E t).d_s b
  have hr : d b ((E.s r : Aˣ) : A) = ((E.s r : Aˣ) : A) * d b (E.lg r) := (E r).d_s b
  have hs := hsum b
  rw [d_add] at hs
  rw [Units.val_mul, d_mul, ht, hr]
  calc ((E.s t : Aˣ) : A) * d b (E.lg t) * ((E.s r : Aˣ) : A)
        + ((E.s t : Aˣ) : A) * (((E.s r : Aˣ) : A) * d b (E.lg r))
      = (((E.s t : Aˣ) : A) * ((E.s r : Aˣ) : A))
          * (d b (E.lg t) + d b (E.lg r)) := by ring
    _ = 0 := by rw [hs, mul_zero]

/-! ## III. Reciprocity is the value of that constant -/

/-- **Reciprocity is exactly "the constant is one".**

`Frame.DirScale.Reciprocal` unfolds to `s_t · s_r = 1`, so the whole remaining
question is which constant the vacuum left, and the vacuum does not answer
it. -/
theorem reciprocal_iff_one (E : DirField n A) (t r : Fin n) :
    (E.toDirScale).Reciprocal t r ↔ E.s t * E.s r = 1 := Iff.rfl

/-- **The chain, collected.**

Under staticity and the vacuum equations, the product of the temporal and radial
units is a **constant unit**, and reciprocity is the statement that the constant
is `1`.  Nothing here fixes it, and that is the correct outcome: the two ways of
fixing it are `Vacuum.reciprocity_of_asymptotic_flatness` (global, analytic) and
`Index.reciprocity_of_no_enclosed_winding` (local, topological), and the second
is the one the framework can afford. -/
theorem vacuum_gives_constant_product (E : DirField n A) (r : Fin n)
    (hstat : ∀ a b : Fin n, b ≠ r → d b (E.lg a) = 0) (t : Fin n)
    (hvac : d r (E.lg t) + d r (E.lg r) = 0) :
    IsConstant (n := n) (((E.s t * E.s r : Aˣ)) : A)
    ∧ ((E.toDirScale).Reciprocal t r ↔ E.s t * E.s r = 1) :=
  ⟨pair_is_constant E t r (sum_is_constant (fun a => E.lg a) r hstat t hvac),
   reciprocal_iff_one E t r⟩

/-- **And with reciprocity, the radial scale is the temporal energy.**

`Frame.reciprocal_iff_radial_is_temporal_energy` again, now at the end of a chain
that contains no boundary condition: the vacuum computation is derived, the
constant is fixed topologically, and what comes out is A3 read across two
directions. -/
theorem radial_is_temporal_energy (E : DirField n A) (t r : Fin n)
    (hrec : (E.toDirScale).Reciprocal t r) :
    ((E.toDirScale).s r : A) = (E.toDirScale).en t :=
  ((E.toDirScale).reciprocal_iff_radial_is_temporal_energy t r).mp hrec

end SCD.Reciprocity
