/-
# Which concepts are anchored, and an honest recount of the predictions

`Explanation.lean` closed with a ledger: one free magnitude against eight
dimensionless predictions.  **That count does not survive inspection, and this
file corrects it rather than defending it.**  Four of the eight are arithmetic on
definitions the framework imported, and reading them off as predictions is the
same error the register has caught before — reporting a number that contains the
answer as if the theory had produced it.

## I.  The test: a claim with no failing instance is not a prediction

A statement quantified over its own parameters is a prediction only if some
assignment of those parameters makes it false.  `Falsifiable`, applied
mechanically, sorts the ledger in one pass.

**`Deflection.iso_is_exactly_half` fails the test.**  `deflectionIso` is defined
as `2GM/bc²` and `deflectionObs` as `4GM/bc²`; the theorem is `2·x = 2·x` after
unfolding, and `factor_two_has_no_failing_instance` shows there is no `(G, M, b,
c)` at which it could fail.  It is bookkeeping between two definitions, and the
factor of two is not in it.

**The content it was standing in for does pass.**
`PPN.deflectionGamma G M b c γ = (2GM/bc²)(1+γ)` matches the observed deflection
exactly when `γ = 1`, and `gamma_claim_is_falsifiable` exhibits a `γ` at which it
fails.  *That* is the prediction; the factor of two is its consequence, not an
independent one.

Three more entries go the same way:

* `Precession.isotropic_is_third` — `coeff β γ = (2 − β + 2γ)/3` is the standard
  PPN formula, **imported**, and `coeff 1 0 · 3 = coeff 1 1` is arithmetic inside
  it.  Worse, it is evaluated at `β = 1`, which `Precession.lean` glosses as "the
  scale response of A6′" and **never proves**.  So the `42.99″/century` chain
  runs through an unproved `β = 1` (§II below);
* `PPN.gamma_prediction_is_sharp : γ = 1 → γ − 1 = 0` — a tautology.  It was cited
  in `Chain.lean` and again in `Explanation.lean` as "the framework's actual
  prediction".  The real statement is `PPN.gamma_eq_one_of_reciprocal`;
* `Attraction.universality_from_counting` — `0 ≤ ν → Δ < 0 → Δν ≤ 0` is
  `mul_nonpos`.  The physics is not in the arithmetic; it is entirely in the
  *identification* of `ν` with a count, which §III treats.

`Light.one_cone_for_every_sector` is a mixed case: its first component is
`Iff.rfl` and its second is real (`physFormDir_eq_bareForm_rescaled`).  The gloss
"every sector-relative Lorentz-violation coefficient vanishes" is a reading of
the second component together with A4′, not something the theorem says.  Kept as
a prediction, with the reading marked as a reading.

## II.  The recount

| tier | what it is | count |
|---|---|---|
| falsifiable and dimensionless | `γ = 1`; universal attraction; one cone for every sector; `CV² = 1`; `2β = 1 + γ` | **5** |
| of those, discriminating against GR + SM | `CV² = 1` alone | **1** |
| cited as predictions, actually definitional | the four of §I, plus `Anisotropic.dirCommutator_is_leading` (`NCSize.lean`) | **5** |
| free magnitudes | `Δ` ≡ `G` | **1** |

**As many entries are inflation as are real** — the rows have been `4`/`4`, then
`4`/`5`, and are now `5`/`5`, moving for independent reasons each time.  Nothing
has been rehabilitated: every entry withdrawn stayed withdrawn.

And the second row is the one that matters for "what has this theory achieved".
`γ = 1`, universal attraction, and exact Lorentz invariance are all things
general relativity and the Standard Model also predict.  Agreeing with them is a
**consistency check** — necessary, and passing it is not nothing — but it does
not distinguish this framework from the theories it is trying to replace.

The only dimensionless number here that GR + SM do not also give is `CV² = 1` for
the log-mass gap spectrum, and `Spectrum.lean` is careful about it in its own
docstring: the observed `0.875` sits at the 63rd percentile of a wide
distribution, so **agreement is encouraging and not decisive; what is decisive is
the exclusion of `CV = 0`**, the geometric tower.  So the framework's single
discriminating prediction currently *excludes a hypothesis* rather than *pinning
a number*.

Two more could join it and neither has yet:

* the `w`/`H₀` link (`Scanning.two_anomalies_one_number`) is **three inputs
  deep**, not one.  `Response.lean`: the theorem holds for *every* density, so it
  is `κ` cancelling in a fraction; its content is the scanning hypothesis plus two
  unformalised identifications (that a `w₀wₐ` fit measures the response's
  fractional evolution, and that the ladder-versus-ruler discrepancy measures the
  density's).  The hypothesis itself reduces to factorisation through the count,
  which A5 and the weight grading do **not** force;
* the anisotropic non-commutative sector's spin-sector effect is zeroth order in
  gradients and therefore not derivative-suppressed, but **no number has been put
  on it**.

## III.  The identifications — where the drift actually is

The tiers above are about theorems.  The concepts that "float" are the
*identifications*: places where a structure in the framework is given a physical
name and no theorem forces the naming.  The test is the same one:

> An identification is **anchored** when swapping it for an alternative changes
> something falsifiable.  Otherwise it is decoration.

**Anchored — `ν` as a *count* rather than a
signed winding.  The two give opposite signs (`signed_source_is_distinguished`:
a negative `ν` with `Δ < 0` gives `Δν > 0`, repulsion), so antihydrogen falling
selects between them.  This identification does work.

**`β = 1` was the worst entry here and has since been removed.**  It was glossed
as "the scale response of A6′" in `Precession.lean` and proved nowhere, while the
`42.99″/century` value is `coeff 1 1` — a measured number quoted downstream of an
unproved gloss.  `Nonlinearity.lean` derives it, and finds the gloss named the
**wrong input**: A6′ is the source law and the perihelion is measured in vacuum.
What does the work is the framework's own `tt` vacuum equation, and it gives more
than the value — `2β = 1 + γ`, so `β` is not an independent parameter at all.

**Not anchored — the register of drift:**

* **`a = 1/ε`**, the scale factor as inverse energy scale.  Already in the
  register as an identification; nothing in the development distinguishes it from
  any monotone alternative, so no cosmological statement tests it;
* **`ħ` as an exact scale step.**  `Crossed.lean` presented it as a discovery;
  A3′ (`Dual.lean`) demoted it to a **normalisation**.  A normalisation cannot be
  tested, so this one drifted from result to convention and the demotion should
  be read wherever `ħ` is mentioned;
* **the timelike direction as the drift direction.**  Rests on the sign
  convention already registered in §V.a.

Three unanchored against two anchored.  `drift_exceeds_anchor`.

## IV.  So, plainly

**Explanatory power: real and structural.**  The framework explains *why* several
things have the form they do — why gravity is universal while charge is signed
(different labels of one species), why the gravitational coupling carries a unit
and the gauge couplings do not (only one law crosses the grading), why there is
no dynamics in two directions, why no arrow of time can come from the dynamics,
why light shows no anisotropy despite the scale being directional.  These are
explanations of *form*, they are theorems, and they are not available in the
theories being replaced.

**Predictive power: one free magnitude; five falsifiable dimensionless
statements, of which three are shared with general relativity and the Standard
Model, one discriminating statement that so far excludes a hypothesis rather than
fixing a number, and one *relation between two measured parameters* —
`2β = 1 + γ` — that general relativity satisfies but the wider PPN parameter
space does not.**

That is a much smaller claim than "eight predictions", and it is the one the
theorems support.  It is not a bad position for a framework at this stage, but
calling it more than it is would be the failure mode the register exists to
catch — and this file is the fourth time that failure has been caught in it.
-/
import SCD.Explanation
import SCD.Deflection
import SCD.PPN
import SCD.Precession
import SCD.Attraction

namespace SCD.Anchor

open SCD

/-! ## I. The test -/

/-- A family of claims is **falsifiable** when some instance of its parameters
makes it false.  A family with no failing instance is an identity between
definitions, whatever it is called. -/
def Falsifiable {α : Type*} (P : α → Prop) : Prop := ∃ x, ¬ P x

/-- **The deflection factor of two is not falsifiable in its own parameters.**

`deflectionIso` is `2GM/bc²` by definition and `deflectionObs` is `4GM/bc²` by
definition, so the relation between them holds at every `(G, M, b, c)`,
including physically meaningless ones.  It is bookkeeping, and citing it as the
framework's prediction — which `Chain.lean` and `Explanation.lean` both did — is
the register's recurring failure of reporting an imported number as a produced
one. -/
theorem factor_two_has_no_failing_instance :
    ¬ Falsifiable (fun p : ℝ × ℝ × ℝ × ℝ =>
        2 * Deflection.deflectionIso p.1 p.2.1 p.2.2.1 p.2.2.2
          = Deflection.deflectionObs p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  rintro ⟨p, hp⟩
  exact hp (Deflection.iso_is_exactly_half _ _ _ _)

/-- **But the statement it stands in for is falsifiable.**

`deflectionGamma` depends on `γ`, and at `γ = 0` it disagrees with the observed
deflection.  So `γ = 1` carries content and the factor of two is its
consequence — one prediction, not two. -/
theorem gamma_claim_is_falsifiable :
    Falsifiable (fun γ : ℝ =>
      PPN.deflectionGamma 1 1 1 1 γ = Deflection.deflectionObs 1 1 1 1) := by
  refine ⟨0, ?_⟩
  norm_num [PPN.deflectionGamma, Deflection.deflectionObs]

/-- **And the precession coefficient is arithmetic inside an imported formula.**

`Precession.coeff` is the standard PPN expression; the factor of three between
its isotropic and reciprocal values holds identically.  The framework's input to
it is `γ`, and `β` is an identification (§III), not a theorem. -/
theorem precession_ratio_has_no_failing_instance :
    ¬ Falsifiable (fun _ : Unit => Precession.coeff 1 0 * 3 = Precession.coeff 1 1) := by
  rintro ⟨_, hp⟩
  exact hp Precession.isotropic_is_third

/-! ## II. The identification that is anchored -/

/-- **A signed source and a counted source are distinguishable, so the
identification of `ν` with a count does work.**

`Attraction.universality_from_counting` needs `0 ≤ ν`; drop it and the same `Δ`
gives repulsion.  Antihydrogen falling therefore selects between the two
readings, which is what makes this an anchored identification rather than a
naming convention. -/
theorem signed_source_is_distinguished :
    ∃ Δ ν : ℝ, Δ < 0 ∧ ν < 0 ∧ 0 < Δ * ν := by
  refine ⟨-1, -1, by norm_num, by norm_num, by norm_num⟩

/-- Against the counted reading, where the sign is forced the other way for every
source at once. -/
theorem counted_source_is_uniform (Δ ν : ℝ) (hΔ : Δ < 0) (hν : 0 ≤ ν) :
    Δ * ν ≤ 0 :=
  Attraction.attraction_from_counting Δ ν hν hΔ

/-! ## III. The ledger, corrected

Counts in the manner of `Audit.lean`: a bookkeeping device whose content is the
theorems named in the header. -/

/-- Falsifiable dimensionless statements: `γ = 1`; universal attraction; one cone
for every sector; `CV² = 1`; and **`2β = 1 + γ`** (`Nonlinearity.lean`), a
relation between two independently measured PPN parameters that the PPN framework
leaves independent. -/
def falsifiableDimensionless : ℕ := 5

/-- Of those, the ones general relativity and the Standard Model do **not** also
give: `CV² = 1` alone.  The other three are consistency checks — necessary,
passed, and not discriminating. -/
def discriminatingFromGR : ℕ := 1

/-- Statements cited as predictions that are arithmetic on definitions: the
deflection factor two, the precession ratio, `gamma_prediction_is_sharp`,
`universality_from_counting`, and — added by `NCSize.lean` —
`Anisotropic.dirCommutator_is_leading`, which is `⟨rfl, rfl⟩` and carried the
claim that the anisotropic quantum correction is not derivative-suppressed. -/
def citedAsPredictionButDefinitional : ℕ := 5

/-- Identifications no falsifiable statement distinguishes: `a = 1/ε`, `ħ` as an
exact scale step, and the timelike direction.

**`β = 1` has been removed from this list.**  It was the worst entry — a measured
number quoted downstream of an unproved gloss — and `Nonlinearity.lean` derives
it from the `tt` vacuum equation, replacing the gloss (which named A6′, the wrong
input entirely) with `2β = 1 + γ`. -/
def unanchoredIdentifications : ℕ := 3

/-- Identifications that some falsifiable statement does distinguish: `ν` as a
count, and `β` — no longer an identification at all, since
`Nonlinearity.beta_from_gamma` makes it a function of `γ`. -/
def anchoredIdentifications : ℕ := 2

/-- **The measurement of the drift: as many entries were inflation as were
real.**

`Explanation.dimensionlessPredictions` said eight.  Four survived the test of §I
and four did not, so exactly half the ledger was definitional at the time this
was written.  Carried as a number because a prose apology would not be checkable.

**This statement has now been rewritten twice, and that is itself the finding.**
It was `4 = 4`; it became `4 < 5` when `Nonlinearity.lean` added `2β = 1 + γ`; it
is `5 = 5` again now that `NCSize.lean` found a fifth definitional entry,
`Anisotropic.dirCommutator_is_leading`.  A relation between two live counts is
not a fact to assert — the same lesson `Audit.unification_added_nothing` learned.
The two current values are the record; the relation between them is not. -/
theorem the_inflation :
    citedAsPredictionButDefinitional = 5 ∧ falsifiableDimensionless = 5 :=
  ⟨rfl, rfl⟩

/-- **And the concepts drift more than they anchor.** -/
theorem drift_exceeds_anchor :
    anchoredIdentifications < unanchoredIdentifications := by decide

/-- **The honest position.**

More falsifiable dimensionless statements than free magnitudes — so the leverage
of `Explanation.leverage` is real — but only one of them discriminates against
the theories being replaced, and the register of unanchored concepts is not
empty. -/
theorem honest_ledger :
    Explanation.freeMagnitudes < falsifiableDimensionless
    ∧ discriminatingFromGR < falsifiableDimensionless
    ∧ 0 < unanchoredIdentifications := by
  refine ⟨by decide, by decide, by decide⟩

end SCD.Anchor
