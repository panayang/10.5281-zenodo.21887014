/-
# Two sectors that share names and no types — and a claim of mine to withdraw

The next step was to be the unit bookkeeping: convert `λ` from the framework's
scale-axis time to cosmological time, and get a number.  Checking *which* `t`
first — the register's §III diagnostic, **a `t` of what?** — the bookkeeping turns
out to be impossible for a reason that is not about units.

## What the imports say

* `DarkEnergy.lean` imports **only Mathlib**.  Its `ε`, `t` and `λ` are bare
  reals; `σ` does not occur in the file;
* `Cosmos.lean` contains no algebra either — its two apparent matches are the
  word *overlap* in prose;
* `Scanning.lean` mentions `ScaleAlgebra` **nowhere**, and
  `scanRate (κ : ℝ) (rho : ℝ → ℝ) (t : ℝ)` takes all three as free real
  parameters;
* `Index.lean`, where `κ = −2(n−1)Δ` lives, imports `Conformal`, `Newton` and
  `Defect` — the algebra.

> **The cosmological sector and the algebraic sector share names and no types.**

So there is no conversion to compute.  `Scanning`'s `t` is not the scale axis
running in different units; it is an unconnected real variable.  The bookkeeping
is not hard, it is **not yet a question**.

## And a claim of mine to withdraw

`Bridge.lean` proves that a drift evaluation carries `Index.IndexResponse` to
`Response.FactorsThroughCount` at the pair `(val (lap σ), val ν)`.  That theorem
stands.  What I wrote around it — that **the scanning hypothesis is a theorem** —
does not.

The scanning hypothesis is factorisation at the pair *nature supplies*: the
cosmological response, and the resolved count.  My bridge supplies a different
pair, of its own construction.  `Bridge.lean`'s header flagged one of the two
identifications still needed and **missed the other** — that `val ν` is the
resolved count — and the summary I gave was stronger than the file.

`factorisation_is_generic` is why this matters rather than being a quibble: the
zero response factors through the zero count at every coefficient, so exhibiting
*an* instance of `FactorsThroughCount` establishes nothing.
`factorisation_has_failing_instances` shows the predicate is not vacuous once the
pair is fixed — so the content is entirely in *which pair*, which is exactly what
the disconnection means the framework cannot yet say.

## What the next step actually is

Not bookkeeping.  **Connecting the cosmological sector to the algebra** — giving
`Cosmos`'s `ε`, `Scanning`'s `ρ` and `DarkEnergy`'s `t` types that mention
`ScaleAlgebra` — and that is a substantial piece of work, not a conversion
factor.  Until it is done, `Anchor.lean`'s refusal to count the `w`/`H₀` link
among the predictions is not conservative but exactly right, and the "three
inputs deep" count was, if anything, generous.
-/
import SCD.Observations

namespace SCD.Disconnect

open SCD


/-- **Factorisation is generic: it holds of pairs with no physics in them.**

`Response.FactorsThroughCount D N κ` is a statement about *given* `D`, `N` and
`κ`.  The zero response factors through the zero count at every coefficient, so
exhibiting *an* instance establishes nothing about the scanning hypothesis, which
is factorisation at the pair **nature supplies**.

This is `Anchor.Falsifiable`'s discipline applied to a hypothesis rather than to
a prediction: a claim with no failing instance is not a claim, and a predicate
satisfiable by zero is not established by satisfying it somewhere. -/
theorem factorisation_is_generic (κ : ℝ) :
    Response.FactorsThroughCount (fun _ => 0) (fun _ => 0) κ := by
  intro t t'
  simp

/-- **And it is not vacuous either** — there are pairs that fail it, so the
predicate does have content once the pair is fixed.  What it lacks is any way to
say *which* pair. -/
theorem factorisation_has_failing_instances :
    ¬ Response.FactorsThroughCount (fun t => t ^ 2) (fun t => t) 1 := by
  intro h
  have h1 := h 2 0
  norm_num at h1


end SCD.Disconnect
