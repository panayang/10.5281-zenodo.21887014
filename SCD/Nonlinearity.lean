/-
# `β`, and where it actually comes from

`Anchor.lean` found the worst of the unanchored identifications: `Precession.lean`
uses `coeff 1 1` to produce `42.99″/century`, and its `β = 1` is glossed there as
"the scale response of A6′" and **proved nowhere**.  A measured number was quoted
downstream of an unproved gloss.

This file closes that.  The value is right; **the stated reason was wrong**, and
the correction matters because the wrong reason would make the result depend on
an input it does not depend on.

## I.  The gloss is wrong: A6′ is the source law, and this happens in vacuum

`β` is measured by the perihelion of Mercury, outside the Sun.  A6′/A6″ relates
the Laplacian of the scale to a source density, and the source density is zero
there.  Whatever fixes `β`, it is not the response law.

What fixes it is the framework's own **vacuum** equation, and only one component
of it: `R_tt = 0`, which `Diagonal.ric_tt` supplies with the connection certified
by `Diagonal.metric_compatible`.

## II.  The step where this goes wrong, stated first

For a static metric `−N² dt² + h_ij dx^i dx^j`, the `tt` vacuum equation is

        Δ_h N = 0 ,

the lapse is harmonic **with respect to the physical spatial metric `h`**.  Two
things in that sentence are easy to get wrong, and each gets a different answer:

* **which object.**  `N = s_t = e^{σ_t}` is harmonic, not `σ_t`;
* **which metric.**  `h`, not the bare flat one.

Dropping the second — treating `N` as flat-harmonic — kills the `∇ψ·∇N` term and
gives `a₂ = 0`, hence **`β = 1/2`** (`flat_shortcut_gives_half`).  That is not a
small error; it is a factor of two in the quantity being predicted, and it is
recorded here as a theorem rather than a warning so the trap stays visible.

Curiously, once the correct equation is used, `σ_t` *does* come out flat-harmonic
through second order — but as a **consequence**, not as the input, and only
because `γ = 1`.  Assuming it would have been assuming the answer.

## III.  The derivation

Work in the standard PPN gauge, where the `1PN` spatial metric is conformally
flat — this is not an extra physical assumption but the gauge in which `β` and
`γ` are *defined*, so it is forced by wanting to talk about them at all.  Write

        N = 1 + a₁μ + a₂μ² ,      h = e^{2ψ}δ ,   ψ = b₁μ + b₂μ² ,

with `μ` the Newtonian potential, harmonic away from the source.

For `h = e^{2ψ}δ` in three spatial dimensions,

        Δ_h f = e^{−2ψ} ( ∇²f + ∇ψ·∇f ) ,

the coefficient being `d − 2 = 1`.  Substituting and collecting the terms of
order `m²` — the only ones at this order are those carrying `|∇μ|²`, since `μ`
itself is harmonic —

        2a₂ |∇μ|²  +  a₁b₁ |∇μ|²  =  0 ,   so   **2a₂ + a₁b₁ = 0** .

The two definitions:

* `g_tt = −N² = −(1 − 2μ + 2βμ²)` gives `2a₁ = −2` and `a₁² + 2a₂ = 2β`;
* `g_ij = e^{2ψ}δ = (1 + 2γμ)δ` gives `b₁ = γ`.

So `a₁ = −1`, `2a₂ = −a₁b₁ = γ`, and

> **2β = a₁² + 2a₂ = 1 + γ.**

`beta_from_gamma`.  With `γ = 1` — already derived, from reciprocity
(`PPN.gamma_eq_one_of_reciprocal`) — this gives **`β = 1`**, `beta_eq_one`.

## IV.  What was actually gained, which is more than the number

`β = 1` on its own would only be agreement with general relativity.  The relation
is worth more:

> **`β` and `γ` are not independent here.  `2β = 1 + γ`, equivalently
> `β − 1 = (γ − 1)/2`.**

The PPN framework treats them as independent, and they are independent in the
theories it was built to compare.  **Scalar–tensor theories violate this
relation**: Brans–Dicke has `β = 1` exactly with `γ = (1+ω)/(2+ω) ≠ 1`, which is
off the line for every finite `ω` (`scalar_tensor_violates`).  The reason is
structural and worth naming: those theories do **not** have `R_tt = 0` in vacuum
— the scalar's stress sits on the right-hand side — and `R_tt = 0` is the whole
input here.

So this is a falsifiable relation between two independently measured parameters:
Cassini bounds `γ − 1`, lunar laser ranging bounds `β − 1` separately, and the
framework says the second is half the first.  Both current bounds are consistent
with it; a future measurement off the line kills the framework.

**It does not discriminate against general relativity**, which sits on the line
at `β = γ = 1`.  `Anchor.lean`'s tier count is updated accordingly: one more
falsifiable dimensionless statement, no more discriminating ones.

## V.  What is assumed, explicitly

* **staticity and spherical symmetry** — already on the register for the whole
  gravity chain;
* **the standard PPN gauge** (conformally flat `1PN` spatial slice) — a gauge
  choice, and the one in which `β`, `γ` are defined;
* **the second-order content of `Δ_h N = 0`**, namely `2a₂ + a₁b₁ = 0`.  The
  passage from the vacuum equation to that algebraic relation is the derivation
  of §III and is **not formalised** — the framework has no differential-operator
  theory to state `Δ_h` in.  It appears below as an explicit hypothesis,
  `VacuumSecondOrder`, in exactly the manner of A6″ and the areal coordinate;
* **`γ = 1`**, which is derived, with its own registered inputs
  (`Chain.lean`).

What is *not* assumed, and was the gloss being corrected: A6′.
-/
import SCD.PPN
import SCD.Precession

namespace SCD.Nonlinearity

open SCD

/-! ## I. The expansion

The `1PN` data of a static, spherically symmetric configuration in the standard
PPN gauge: the lapse to second order and the spatial conformal factor to first.
Nothing here is specific to this framework — it is the parametrisation in which
`β` and `γ` are defined. -/

/-- Coefficients of the static `1PN` expansion:
`N = 1 + a₁μ + a₂μ²` for the lapse, `h = e^{2ψ}δ` with `ψ = b₁μ + …` for the
spatial metric. -/
structure Static1PN where
  /-- Lapse, first order. -/
  a₁ : ℝ
  /-- Lapse, second order — the coefficient `β` measures. -/
  a₂ : ℝ
  /-- Spatial conformal factor, first order — the coefficient `γ` measures. -/
  b₁ : ℝ

namespace Static1PN

variable (E : Static1PN)

/-- `γ` reads off the spatial metric: `g_ij = (1 + 2γμ)δ_ij`. -/
def gamma : ℝ := E.b₁

/-- `β` reads off the lapse at second order: `g_tt = −N² = −(1 − 2μ + 2βμ²)`, so
`2β` is the `μ²` coefficient of `N² = 1 + 2a₁μ + (a₁² + 2a₂)μ²`. -/
noncomputable def beta : ℝ := (E.a₁ ^ 2 + 2 * E.a₂) / 2

/-- **The Newtonian limit**: `g_tt = −(1 − 2μ + …)` forces `a₁ = −1`. -/
def Newtonian : Prop := E.a₁ = -1

/-- **The second-order content of the static vacuum equation `Δ_h N = 0`.**

For `h = e^{2ψ}δ` in three dimensions, `Δ_h f = e^{−2ψ}(∇²f + ∇ψ·∇f)`.  With `μ`
harmonic, the only order-`m²` terms carry `|∇μ|²`, and they cancel exactly when
this holds.

Registered as a hypothesis, not derived: the passage from the vacuum equation to
this algebraic relation is the computation of the header, and the framework has
no theory of differential operators on a curved slice in which to state it. -/
def VacuumSecondOrder : Prop := 2 * E.a₂ + E.a₁ * E.b₁ = 0

/-- **The shortcut that gets it wrong**: treating the lapse as harmonic with
respect to the *bare flat* metric instead of the physical spatial one drops the
`∇ψ·∇N` term and leaves `a₂ = 0`. -/
def FlatShortcut : Prop := E.a₂ = 0

end Static1PN

/-! ## II. The relation -/

open Static1PN

/-- **`2β = 1 + γ`.**

The framework's `tt` vacuum equation plus the Newtonian normalisation leaves `β`
a function of `γ` — the two PPN parameters are not independent here, where the
PPN framework treats them as independent. -/
theorem beta_from_gamma (E : Static1PN) (hN : E.Newtonian)
    (hV : E.VacuumSecondOrder) :
    2 * E.beta = 1 + E.gamma := by
  simp only [Static1PN.beta, Static1PN.gamma, Static1PN.Newtonian] at *
  simp only [Static1PN.VacuumSecondOrder, hN] at hV
  rw [hN]
  linarith

/-- **Hence `β = 1`**, given the `γ = 1` already derived from reciprocity.

This is the theorem `Precession.lean` needed and did not have; its own gloss
attributed the value to A6′, which is the source law and plays no part. -/
theorem beta_eq_one (E : Static1PN) (hN : E.Newtonian) (hV : E.VacuumSecondOrder)
    (hγ : E.gamma = 1) : E.beta = 1 := by
  have h := beta_from_gamma E hN hV
  rw [hγ] at h
  linarith

/-- **The observable form**: the deviation of `β` from unity is half the
deviation of `γ`.

Cassini bounds `γ − 1`; lunar laser ranging bounds `β − 1` independently.  The
framework relates them, and a measured pair off this line falsifies it. -/
theorem deviation_halves (E : Static1PN) (hN : E.Newtonian)
    (hV : E.VacuumSecondOrder) :
    E.beta - 1 = (E.gamma - 1) / 2 := by
  have h := beta_from_gamma E hN hV
  linarith

/-! ## III. The trap, on record -/

/-- **The flat-metric shortcut gives `β = 1/2`.**

Treating the lapse as harmonic with respect to the bare flat metric — dropping
the `∇ψ·∇N` term that the physical spatial metric contributes — lands a factor of
two away from the answer.  Recorded as a theorem so the size of the error is
visible: this is the kind of step in the gravity sector that looks harmless and
is not. -/
theorem flat_shortcut_gives_half (E : Static1PN) (hN : E.Newtonian)
    (h : E.FlatShortcut) : E.beta = 1 / 2 := by
  simp only [Static1PN.beta, Static1PN.FlatShortcut] at *
  rw [hN, h]
  norm_num

theorem shortcut_is_off_by_two : (1 : ℝ) / 2 ≠ 1 := by norm_num

/-! ## IV. The relation has content -/

/-- **It is not vacuous**: a configuration satisfying the Newtonian limit but not
the vacuum condition violates the relation.  So `2β = 1 + γ` is a genuine
restriction and not an identity between the definitions of `β` and `γ` — the test
`Anchor.lean` applies to every entry in the ledger.

The first witness tried here — `a₂ = 0` with `b₁ = 0` — *satisfies* the relation,
and the reason is a check on the algebra rather than an accident: with no spatial
scale the `∇ψ·∇N` term is absent, so the flat shortcut and the correct equation
coincide, and both give `β = 1/2 = (1 + 0)/2`.  The shortcut of §III is wrong
only when `γ ≠ 0`, which is exactly the case that matters. -/
theorem relation_is_falsifiable :
    ∃ E : Static1PN, E.Newtonian ∧ 2 * E.beta ≠ 1 + E.gamma := by
  refine ⟨⟨-1, 1, 0⟩, rfl, ?_⟩
  simp only [Static1PN.beta, Static1PN.gamma]
  norm_num

/-- **Scalar–tensor theories violate it.**

Brans–Dicke has `β = 1` exactly together with `γ = (1+ω)/(2+ω)`, which differs
from `1` for every finite `ω`.  Such a pair is off the line, and the structural
reason is that those theories do not have `R_tt = 0` in vacuum — the scalar's
stress sits on the right-hand side, and `R_tt = 0` is this derivation's only
input. -/
theorem scalar_tensor_violates (γ : ℝ) (hγ : γ ≠ 1) : 2 * (1 : ℝ) ≠ 1 + γ := by
  intro h
  exact hγ (by linarith)

/-- **General relativity sits on the line**, so the relation does not
discriminate against it.  What it discriminates against is the wider PPN
parameter space, in which `β` and `γ` vary independently. -/
theorem gr_satisfies_the_relation : 2 * (1 : ℝ) = 1 + 1 := by norm_num

/-! ## V. Feeding it back to the precession -/

/-- **The precession coefficient is now derived rather than glossed.**

`Precession.coeff β γ = (2 − β + 2γ)/3` evaluated at the derived pair gives `1`,
which is the coefficient the `42.99″/century` value uses.  Both arguments are now
theorems: `γ` from reciprocity, `β` from the relation above. -/
theorem precession_coefficient_derived (E : Static1PN) (hN : E.Newtonian)
    (hV : E.VacuumSecondOrder) (hγ : E.gamma = 1) :
    Precession.coeff E.beta E.gamma = 1 := by
  rw [beta_eq_one E hN hV hγ, hγ]
  norm_num [Precession.coeff]

/-- **Collected.**  One relation, its consequence, and its falsifiability. -/
theorem summary (E : Static1PN) (hN : E.Newtonian) (hV : E.VacuumSecondOrder) :
    (2 * E.beta = 1 + E.gamma)
    ∧ (E.beta - 1 = (E.gamma - 1) / 2)
    ∧ (∃ F : Static1PN, F.Newtonian ∧ 2 * F.beta ≠ 1 + F.gamma) :=
  ⟨beta_from_gamma E hN hV, deviation_halves E hN hV, relation_is_falsifiable⟩

end SCD.Nonlinearity
