/-
# Four constants and three dimensions, counted here

The usual bookkeeping has three base dimensions `L, T, M` and four constants
`c, ℏ, G, e`: the first three carry independent dimensions and fix the units, and
`e` contributes one pure number.  This file asks what that becomes here, and the
answer changes a count the register has been quoting.

## I.  There are no dimensions — there is one grading

Everything in the development is a ratio and `σ` is a dimensionless log-scale.
What replaces dimension is **weight** under `σ ↦ cσ` (`Weight.lean`), a single
`ℤ`-grading.

> **Three base dimensions become one grading.**

And the collapse is not a choice of units.

*`T` is not separate from `L`.*  `Signature.lean` derives the `1 + (n−1)` split
from the drift: time is the direction the scale is running.  Both are directions
of one algebra, told apart by a sign `η`, not by a dimension.

*`c` is not a constant.*  `Well.light_measured_speed_one` — light crosses at
measured speed one in every direction, because the scale sets rods and light
times alike (`Light.michelson_morley_null`), and
`Horizon.no_energy_dependent_speed` says the cone is scale-blind.  **`c = 1` is a
theorem here, not a convention.**

*`M` is not separate either.*  A3 is `ε = s⁻¹`, and
`Consolidation.A3_is_inversion` shows that is a group law.  Energy is inverse
scale: weight `−1` where length is weight `+1`.  Same axis, opposite sign.

## II.  What is left, and the count is one more than we have been saying

Magnitudes on that axis:

* `Δ`, gravity's source coefficient — **weight 1** (`Weight`'s table);
* the **scale step** `Crossed.lean` identifies with `ℏ` — **weight 1**
  (`step_weight_one`: a step is a difference of log-scales);
* `ρ`, the threshold density — **weight −1**.

`two_pure_numbers`: both `Δρ` and `ℏρ` are weight zero.  `ratio_is_pure` says
`Δ/ℏ` is pure as well but not independent.  So the magnitudes carry **two**
pure numbers.

`Audit.lean` §V.ap says "one protected unit, one free pure number".  That holds
only if `Δ` and the step are the **same** magnitude — and `Index.lean` says in so
many words that "`G` and `ℏ` share an origin" is *conditional on a step that is
not taken here*, while `Crossed.lean`'s own scope note says going from "there is
a scale shift" to "`ℏ` is that step" is an **identification, not a
construction**.

`collapse_iff`: the two numbers coincide **iff** the magnitudes agree.

> **So there are two free pure numbers, not one, unless `G` and `ℏ` are the same
> magnitude — and nothing in the development says they are.**

Two claims the register has carried side by side for a long time, never read
against each other.

## III.  Where `e` goes, and this is the payoff

`α` is **weight zero** — `Weight`'s table: a gauge coupling's value does not
depend on how `σ` is labelled.  So it is a pure number **structurally**, not by a
dimensional accident.  And `Weight.only_gravity_crosses_the_weight` supplies the
asymmetry: the gauge law relates weight-zero to weight-zero, gravity's relates a
weight-zero count to a weight-one scale, and **exactly one law crosses the
grading**.

> **"Why is the fine-structure constant dimensionless and Newton's constant not"
> stops being a fact about dimensions and becomes a fact about which law crosses
> the grading.**

## IV.  The table

| usual | here |
|---|---|
| `L, T, M` | one grading, weight under `σ ↦ cσ` |
| `c` | not a constant — one cone, and measured speed one is a theorem |
| `ℏ` | a weight-one scale step; an identification, not a construction |
| `G` | a weight-one coefficient `Δ` |
| `e`, i.e. `α` | weight zero — already pure, and structurally so |
| Planck units | one axis, so one magnitude fixes everything |
| pure numbers | `Δρ` and `ℏρ` — **two**, collapsing to one iff `Δ = ℏ` |

## V.  And a question the usual picture cannot ask

`[G] = L³M⁻¹T⁻²` and `[ℏ] = ML²T⁻¹`: different dimensions, so *are `G` and `ℏ`
the same magnitude?* is not a well-formed question there.  Here they carry the
**same weight**, so it is well-formed, and its answer is a single pure number.

That is a real gain in what can be asked.  The framework has not answered it, and
`collapse_iff` says what answering it would buy: the second free number.

## What is not claimed

That `Δ = ℏ`.  Nor that two is the final count — a magnitude nobody has written
could add a third.  What is claimed is that the register's "one free pure number"
is conditional on an identification it elsewhere marks as unmade.
-/
import SCD.Weight
import SCD.Crossed

namespace SCD.Constants

open SCD


/-- **A scale step is a difference of log-scales, hence weight one.** -/
theorem step_weight_one (c σ₁ σ₂ : ℝ) : c * σ₂ - c * σ₁ = c * (σ₂ - σ₁) := by ring

/-- **Two weight-one magnitudes against one weight-minus-one give two pure
numbers, not one.** -/
theorem two_pure_numbers (c Δ h ρ : ℝ) (hc : c ≠ 0) :
    (c * Δ) * (ρ / c) = Δ * ρ ∧ (c * h) * (ρ / c) = h * ρ :=
  ⟨Weight.product_invariant c Δ ρ hc, Weight.product_invariant c h ρ hc⟩

/-- **And their ratio is pure too**, so the three magnitudes carry exactly two
independent numbers. -/
theorem ratio_is_pure (c Δ h : ℝ) (hc : c ≠ 0) : (c * Δ) / (c * h) = Δ / h := by
  rw [mul_div_mul_left _ _ hc]

/-- **The two collapse to one exactly when the magnitudes agree.**

So "`G` and `ħ` share an origin" is not a slogan: it is the assertion that one
particular pure number equals one. -/
theorem collapse_iff (Δ h ρ : ℝ) (hρ : ρ ≠ 0) : Δ * ρ = h * ρ ↔ Δ = h := by
  constructor
  · intro hc; exact mul_right_cancel₀ hρ hc
  · intro hc; rw [hc]


end SCD.Constants
