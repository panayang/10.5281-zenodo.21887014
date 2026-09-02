/-
# What one magnitude and one pure number can buy

`Conversion.lean` closed the question of *deriving* `Δρ`: predictions cannot fix
it and counts cannot fix it, so it is an input.  Accepting an input is not a
defeat — every theory has them — but it puts a question immediately: **what can
still be asked, and what can still be predicted?**

The answer is entirely structural and it is short.

## An input buys something exactly when it appears twice

`one_number_two_relations`: a free number appearing in **one** relation is
absorbed by it and predicts nothing; appearing in **two**, it is fixed by one
measurement and predicts the other.  So the whole question is a count of
appearances.

`Δρ` appears in the gravitational relation — `Index.A6'_from_index` gives
`κ = −2(n−1)Δ`, which is `gravRelation` at `n = 4`.  Does it appear anywhere
else?

## The one other place it might, and the identification nobody made

`Scanning.scanRate κ ρ t = κ·ρ(t)` proposes that the dissipation rate is the
threshold density times a conversion, and its docstring says of that conversion:
*"`κ` is a conversion, not a new freedom — it is what turns a count per e-fold
into a rate."*

**Nothing in the development identifies it.**  `scanRate` occurs in `Scanning`,
`Response`, `Verify` and `Audit` and nowhere else, and no theorem relates its `κ`
to `Index`'s.  So "not a new freedom" is an assertion, and `Anchor.lean`'s test
applies to it: an identification is anchored when swapping it changes something
falsifiable.  **This one changes everything falsifiable that the framework has in
the dimensionful sector.**

* **if the two `κ` are the same constant**, then `coupling_from_rate_and_density`:
  the dissipation rate from cosmology and the threshold density from the mass
  spectrum **determine the gravitational coupling**.  `product_from_rate` is the
  sharper form — `Δρ = −λ/6`, the framework's one free number read straight off a
  cosmological measurement.  Two measurements, one prediction, and it crosses
  from particle masses to gravity;
* **if they are not**, `no_prediction_without_identification`: the rate fixes the
  scanning constant and nothing else moves.  Two independent inputs, no
  prediction, and cosmology tells gravity nothing.

## So the question that decides the framework's dimensionful content

> **Is the conversion that turns a count into a dissipation rate the same
> conversion that turns a count into a curvature?**

That is one question, it is sharp, and it is the framework's own kind of
question: `Weight.only_gravity_crosses_the_weight` says the development has
exactly **one** law relating a weight-zero count to a weight-one scale.  If the
scanning rate is such a law, it is that one or a second — and a second would
contradict a theorem already in the register.

**That argument is not made here and is not a proof.**  Whether the dissipation
rate is a weight-crossing at all depends on the weight of `λ`, which
`Weight.lean`'s table does not list; settling it is the next piece of work and it
is small.  What this file establishes is that **everything dimensionful the
framework can say hangs on that one identification**, which is a much better
place to be than "there is one free number and no route to it".

## What is not claimed

No number is offered.  Converting `λ` into a measured rate requires the unit
bookkeeping between the framework's scale-axis time and cosmological time, and
that has not been done here; producing a figure without it would be the
register's oldest failure.  What is offered is the shape: **one identification
away from a cross-domain prediction, and the identification is stated rather than
assumed.**
-/
import SCD.Conversion
import SCD.Scanning

namespace SCD.Overdetermination

open SCD


/-- **What an input buys: it must appear twice.**

A free number appearing in one relation is absorbed by that relation and
predicts nothing.  Appearing in two, it is fixed by one measurement and predicts
the other.  This is the whole of what "one magnitude and one pure number" can
mean, and it is arithmetic — stated so the count cannot be fudged. -/
theorem one_number_two_relations (x a b p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (h1 : a = p * x) (h2 : b = q * x) : b = (q / p) * a := by
  rw [h1, h2]
  field_simp

/-- **The gravitational relation.**  `Index.A6'_from_index` at `n = 4`. -/
def gravRelation (Δ κ : ℝ) : Prop := κ = -6 * Δ

/-- **The cosmological relation**, if the scanning conversion is the
gravitational one: the dissipation rate is the coupling times the density. -/
def scanRelation (κ rho lam : ℝ) : Prop := lam = κ * rho

/-- **Given both, the coupling is determined by the rate and the density.**

Two measurements — the dissipation rate from cosmology, the threshold density
from the mass spectrum — and the gravitational coupling follows.  That is the
prediction the pair of inputs buys, and it is cross-domain. -/
theorem coupling_from_rate_and_density {Δ κ rho lam : ℝ} (hrho : rho ≠ 0)
    (hg : gravRelation Δ κ) (hs : scanRelation κ rho lam) :
    Δ = -lam / (6 * rho) := by
  rw [gravRelation] at hg
  rw [scanRelation, hg] at hs
  field_simp at hs ⊢
  linarith

/-- **And the pure number is read straight off the rate.**

`Δρ = −λ/6`: the one free number of the framework, fixed by one cosmological
measurement, with no reference to the spectrum at all. -/
theorem product_from_rate {Δ κ rho lam : ℝ} (hg : gravRelation Δ κ)
    (hs : scanRelation κ rho lam) : Δ * rho = -lam / 6 := by
  rw [gravRelation] at hg
  rw [scanRelation, hg] at hs
  field_simp
  linarith

/-- **Without the identification there is no second relation.**

If the scanning conversion is a constant of its own, the rate fixes it and
nothing else moves: two independent inputs, and the gravitational coupling is
untouched by any cosmological measurement. -/
theorem no_prediction_without_identification (κs rho lam : ℝ) (hrho : rho ≠ 0)
    (hs : lam = κs * rho) : κs = lam / rho := by
  field_simp
  exact hs.symm


end SCD.Overdetermination
