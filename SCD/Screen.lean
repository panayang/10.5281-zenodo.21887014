/-
# The observer-invariance screen: which predictions are about the world alone

`Ordering.lean` answered the first half of step zero — the gravity chain's
numbers do not depend on an operator ordering the framework has not chosen.
This is the second half, and it asks the question the chain does not:

> **A prediction is a quantity constant across the theory's solutions.  Constant
> across solutions *of what*?**

The register's own diagnostic (§III, *a count of what?*) applied to the word
"configuration".  Because `Internal.lean` puts the observer inside the
configuration — `observer_is_in_the_determiner` — the accounting in
`Explanation.lean` has two readings, and they are not the same accounting.

## What is proved

* **Adding an observer cannot cost a prediction.**
  `observer_preserves_predictions`: if `f` is constant across the admissible
  worlds, it is constant across the admissible *(world, observer)* pairs, because
  the pairs project into the worlds.  Trivial as a proof and not as a statement —
  it is the answer to "will the ledger have to be redone once there is an
  observer?", and the answer is **no, not for any quantity of the world alone**;
* **but a quantity that reads the observer can be an input even when the world is
  completely pinned.**  `observer_relative_can_be_modulus` exhibits a theory
  admitting exactly one configuration — the tightest a consistent theory can be —
  in which what is recorded still varies with the observer.  Tightening the world
  does not help, because the freedom is in the other slot:
  `observer_relative_is_modulus` assumes nothing about the world beyond its
  admitting one resolution;
* **and the recorded set is not a function of the configuration.**
  `recorded_set_is_observer_relative`, with the direction of the dependence given
  by `Internal.record_antitone`: a larger observer records less, so shrinking the
  observer can only enlarge the sample.

## What that does to the ledger

`Anchor.lean` counts five falsifiable dimensionless statements.  Sorting them by
the screen:

| statement | quantity of |
|---|---|
| `γ = 1` | the configuration |
| `2β = 1 + γ` | the configuration |
| universal attraction | the configuration |
| one cone for every sector | the configuration |
| `CV² = 1` | the **recorded threshold set** |

Four are properties of the scale pattern and are covered by
`observer_preserves_predictions` verbatim.  The fifth is a statistic of *which
thresholds are in the sample*, and membership of that sample is what `record` is.

**And it is the discriminating one.**  `Anchor.lean` records that exactly one of
the five distinguishes this framework from general relativity and the Standard
Model, and it is `CV² = 1`.  So the single entry the framework's case rests on is
the single entry the screen classifies as observer-relative.  *That is an
observation about which entry it is, not a theorem* — the counts agreeing is
arithmetic, and this file does not dress it as anything else.

**What the screen does not prove.**  The classification of the four is by
inspection of what those statements are about, not by a theorem: the framework
has no formal object "the ledger" to quantify over.  And the fifth is classified
by reading `Spectrum.cvSq`, which is computed from a hand-selected list of
Standard Model mass scales — a sample — against `record`, which is what having a
sample means here.  **Nothing in the development links `Spectrum.gaps` to
`Internal.record`**, so the classification is a reading of two definitions and is
registered as one.  Building that link is what would turn `CV² = 1` from a
prediction about a sample into a prediction about a configuration, and it is not
built here.

**So step zero closes with the ordering settled and this one open**, which is a
smaller and sharper open item than the one it replaces: not "predictions may need
redoing" — they do not — but "the discriminating prediction is about a sample,
and the framework has no theory of which sample".
-/
import SCD.Internal
import SCD.Anchor

namespace SCD.Screen

open SCD Explanation Observer Internal

/-! ## I.  The configuration, with the observer in it -/

variable {C : Type*} {V : Type*} {n : ℕ} {ι : Type*}

/-- A world together with the part of it that observes.  `Internal.lean` makes an
observer a `Finset (Fin n)` of directions, so this is the pairing that file's
theorems are implicitly about. -/
abbrev Joint (C : Type*) (n : ℕ) := C × Finset (Fin n)

/-- The theory read on joint configurations: a constraint on the world, and a
constraint saying which observers that world admits. -/
def jointTheory (S : C → Prop) (O : C → Finset (Fin n) → Prop) :
    Joint C n → Prop := fun p => S p.1 ∧ O p.1 p.2

/-- **Adding an observer cannot cost a prediction.**

If `f` is constant across the admissible worlds then it is constant across the
admissible pairs, whatever the observer constraint is — the pairs project into
the worlds, so this is `Explanation.tightening_predicts_more` wearing the shape
of the question that was actually asked.

Trivial as a proof and not as a statement.  It is the answer to *"will the ledger
have to be redone once the observer is part of the system?"*, and for every
quantity of the world alone the answer is no. -/
theorem observer_preserves_predictions (S : C → Prop) (O : C → Finset (Fin n) → Prop)
    (f : C → V) (h : Predicted S f) :
    Predicted (jointTheory S O) (fun p : Joint C n => f p.1) :=
  fun x y hx hy => h x.1 y.1 hx.1 hy.1

/-- And the same for a theory that admits no observer at all: the projection
argument does not care, so nothing here depends on observers being plentiful. -/
theorem observer_preserves_predictions_vacuously (S : C → Prop) (f : C → V)
    (h : Predicted S f) :
    Predicted (jointTheory S (fun _ _ => False)) (fun p : Joint C n => f p.1) :=
  observer_preserves_predictions S _ f h

/-! ## II.  But what is recorded is not a quantity of the world

The screen would be worthless if the first section were all of it: every
accounting is preserved by adding a slot nothing looks at.  What matters is that
the framework's own notion of observation *does* look at that slot. -/

/-- One threshold in two directions, needing direction `0` resolved to `1` and
direction `1` resolved to `0`. -/
def oneThreshold : Fin 1 → Threshold 2 := ![![1, 0]]

/-- The pinned world: a single resolution, reaching `0` in both directions. -/
def pinned : Resolution 2 := ![0, 0]

/-- **The threshold is recorded by the observer occupying direction `1`.**

`0 ≤ 0`: the only condition is met. -/
theorem recorded_by_one : (0 : Fin 1) ∈ record {1} oneThreshold pinned := by
  intro i hi
  fin_cases hi
  norm_num [oneThreshold, pinned]

/-- **And not by the observer occupying direction `0`.**

`1 ≤ 0` fails, so the same threshold in the same world is unrecorded. -/
theorem not_recorded_by_zero : (0 : Fin 1) ∉ record {0} oneThreshold pinned := by
  intro h
  have := h 0 (by decide)
  norm_num [oneThreshold, pinned] at this

/-- **The recorded set is not a function of the configuration.**

Same world, two observers, different records.  This is the formal content of "do
not talk about what is observed without saying who observes". -/
theorem recorded_set_is_observer_relative :
    record {1} oneThreshold pinned ≠ record {0} oneThreshold pinned := by
  intro h
  exact not_recorded_by_zero (h ▸ recorded_by_one)

/-- **A quantity that reads the observer is an input for *every* theory of the
world that admits this configuration.**

The hypothesis is the whole strength of the statement: no constraint on the world
is assumed beyond admitting one particular resolution, so no amount of tightening
the world removes the freedom.  `Explanation.tightening_predicts_more` says a
stronger theory predicts more — and that is true of quantities of the world,
which is exactly what this one is not. -/
theorem observer_relative_is_modulus (S : Resolution 2 → Prop) (hpin : S pinned) :
    Modulus (jointTheory S (fun _ _ => True))
      (fun p : Joint (Resolution 2) 2 => record p.2 oneThreshold p.1) :=
  ⟨(pinned, {1}), (pinned, {0}), ⟨hpin, trivial⟩, ⟨hpin, trivial⟩,
    recorded_set_is_observer_relative⟩

/-- **In particular when the world is completely pinned.**

The instance at the tightest theory a consistent one can be: exactly one
admissible configuration.  What is recorded is still not determined, so it sits
in the inputs column of any honest ledger. -/
theorem observer_relative_can_be_modulus :
    Modulus (jointTheory (fun t : Resolution 2 => t = pinned) (fun _ _ => True))
      (fun p : Joint (Resolution 2) 2 => record p.2 oneThreshold p.1) :=
  observer_relative_is_modulus _ rfl

/-- **And the dependence has a direction.**

`Internal.record_antitone`: a larger observer records less.  So among nested
observers the sample can only grow as the observer shrinks — which is the shape
of the worry for any statistic of a sample, since the statistic is being read off
whatever the sample turned out to be. -/
theorem sample_grows_as_observer_shrinks (μ : ι → Threshold n) (σ : Resolution n)
    {S S' : Finset (Fin n)} (h : S ⊆ S') :
    record S' μ σ ⊆ record S μ σ :=
  Internal.record_antitone μ σ h

/-! ## III.  The ledger, sorted

The counts below are bookkeeping and are carried so they cannot drift, in the
manner of `Audit.lean`'s.  The classification behind them is by inspection and is
argued in this file's header, not proved here — the framework has no formal
object "the ledger" to quantify over. -/

/-- Entries of `Anchor.falsifiableDimensionless` that are quantities of the
configuration alone, hence covered verbatim by `observer_preserves_predictions`:
`γ = 1`, `2β = 1 + γ`, universal attraction, one cone for every sector. -/
def configurationQuantities : ℕ := 4

/-- And the entry that is a statistic of the recorded threshold set: `CV² = 1`. -/
def observerRelativeQuantities : ℕ := 1

/-- The sort is exhaustive: every falsifiable entry is in exactly one column. -/
theorem screen_is_exhaustive :
    configurationQuantities + observerRelativeQuantities
      = Anchor.falsifiableDimensionless := by decide

/-- **The screen's finding.**

Four of the five need nothing from a theory of the observer.  The fifth does, and
`Anchor.discriminatingFromGR` records that the fifth is the only one that
distinguishes this framework from general relativity and the Standard Model.

The equality of counts here is arithmetic and is *not* the content; the content
is the classification in the header, and which entry falls where.  Stated as a
count so that a later pass can see whether the sort has moved. -/
theorem the_discriminating_entry_is_the_observer_relative_one :
    observerRelativeQuantities = Anchor.discriminatingFromGR := by decide

end SCD.Screen
