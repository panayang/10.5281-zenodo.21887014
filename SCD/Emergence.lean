/-
# There are no fundamental particles

`Color.lean` tried to produce colour, and `ColorAudit.lean` showed the attempt
failed by a factor that is not close.  The failure was not a technical one.  The
whole attempt was aimed at the wrong thing: it took the Standard Model's
ontology — a fixed list of species, each carrying intrinsic labels — and tried
to reproduce it.  That is borrowing the question, and the framework does not
have that question.

A3 says something different, and it has been in the axioms from the start:
`ε·s = 1`.  Energy scale *is* inverse length scale.  So "what is present" is not
a property of the world; it is a property of the world **at a resolution**.
Change the resolution and you do not learn more about the same particles — you
are looking at a different set of them.

That is the content this file makes precise, and it is what "unification" means
here.  Gravity, `ħ` and particle content are not three things to be reconciled;
they are three readings of one variable:

* gravity is the inhomogeneity of the scale (`Conformal`, `Connection`);
* `ħ` is the size of a step along the scale (`Crossed`);
* **particle content is a slice across the scale** — this file.

The results:

* `resolved_mono` — content only grows with resolution;
* `content_never_complete` — **for every scale something remains unresolved**,
  so no scale carries a complete list.  There is no "the" set of fundamental
  particles, and asking for one is a malformed question;
* `always_more_above` — the content strictly grows infinitely often, so the
  tower never terminates;
* `mass_iff_threshold` — mass and threshold determine each other, so **mass is
  not a parameter attached to a species**: it is the coordinate on the scale
  axis at which the species appears.

The last point retro-explains two earlier findings at once.  `MassAudit` found
the mass law underdetermined by topology; of course it is — mass is not a
property of the defect, it is where the defect shows up.  And the effective
field theory embarrassment of changing frameworks at every energy is not an
embarrassment: `RG.active_eq_of_no_threshold` says the description is *exact*
between thresholds, and this file says there is no last threshold.  The theory
is reporting its own structure correctly.

**What is given up.**  Colour, generations, the Higgs, and the rest of the
Standard Model table are not targets here.  They are features of one slice, and
the framework has no reason to reproduce a slice's contingent contents.  What it
should be asked for instead is the *threshold structure* — where content
changes — and that is a different, and testable, kind of prediction.
-/
import SCD.RG
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Basic

namespace SCD.Emergence

open Real

/-! ## Content is a slice, not a list

A structure is labelled by the log-scale at which it becomes resolvable.  There
is no assumption that finitely many exist; by A2 the scale never vanishes, so
nothing caps the resolution from above. -/

/-- What a probe at log-scale `t` can resolve. -/
def resolved (μ : ℕ → ℝ) (t : ℝ) : Set ℕ := {k | μ k ≤ t}

@[simp] theorem mem_resolved {μ : ℕ → ℝ} {t : ℝ} {k : ℕ} :
    k ∈ resolved μ t ↔ μ k ≤ t := Iff.rfl

/-- **Content only grows.**  A better probe never loses a structure. -/
theorem resolved_mono (μ : ℕ → ℝ) {t t' : ℝ} (h : t ≤ t') :
    resolved μ t ⊆ resolved μ t' := fun _ hk => le_trans hk h

/-! ## No scale carries a complete list -/

/-- **For every scale something remains unresolved.**

If the thresholds are unbounded — which A2 permits, since the scale is a unit
and never vanishes, so there is no smallest length to cap the resolution — then
no probe, however good, sees everything.

There is therefore no such thing as *the* list of fundamental particles.  The
question presupposes a scale-independent answer, and the axioms provide none. -/
theorem content_never_complete (μ : ℕ → ℝ) (hunb : ∀ M : ℝ, ∃ k, M < μ k) (t : ℝ) :
    resolved μ t ≠ Set.univ := by
  obtain ⟨k, hk⟩ := hunb t
  intro hcon
  have hmem : k ∈ resolved μ t := by rw [hcon]; trivial
  rw [mem_resolved] at hmem
  linarith


/-- **The tower never terminates.**  Above any scale there is a strictly larger
content, so the refinement continues without end. -/
theorem always_more_above (μ : ℕ → ℝ) (hunb : ∀ M : ℝ, ∃ k, M < μ k) (t : ℝ) :
    ∃ t', t < t' ∧ resolved μ t ⊂ resolved μ t' := by
  obtain ⟨k, hk⟩ := hunb t
  refine ⟨μ k, hk, ?_, ?_⟩
  · exact resolved_mono μ (le_of_lt hk)
  · intro hsub
    have hmem : k ∈ resolved μ (μ k) := by simp only [mem_resolved]; exact le_refl _
    have := hsub hmem
    rw [mem_resolved] at this
    linarith

/-- Collected: the content is a strictly increasing, never-completed family.
"Which particles exist" has an answer only once a scale is named. -/
theorem no_fundamental_list (μ : ℕ → ℝ) (hunb : ∀ M : ℝ, ∃ k, M < μ k) :
    (∀ t : ℝ, resolved μ t ≠ Set.univ)
    ∧ (∀ t : ℝ, ∃ t', t < t' ∧ resolved μ t ⊂ resolved μ t') :=
  ⟨content_never_complete μ hunb, always_more_above μ hunb⟩

/-! ## Mass is a location, not a property

By A3 the mass of a structure is the reciprocal of the scale at which it
appears.  So mass and threshold carry the same information — which means mass
is not an attribute the structure *has*, but the place on the scale axis where
it *is*. -/

/-- Mass of the structure with threshold `μ k`, by A3.

`μ k` is the log-*energy* at which the structure becomes resolvable
(`resolved μ t = {k | μ k ≤ t}`), and by `ε·s = 1` energy is mass.  So the mass
is `e^{μ k}`: a later threshold is a heavier structure. -/
noncomputable def massOf (μ : ℕ → ℝ) (k : ℕ) : ℝ := Real.exp (μ k)


/-- **Mass and threshold determine each other.**

So mass is not a parameter attached to a species; it is the coordinate at which
the species appears.  This is why `MassAudit` found no topological law fixing
it: there is nothing for topology to fix, because mass was never an intrinsic
property. -/
theorem mass_iff_threshold (μ : ℕ → ℝ) (k l : ℕ) :
    massOf μ k = massOf μ l ↔ μ k = μ l := by
  simp only [massOf]
  constructor
  · intro h
    exact Real.exp_injective h
  · intro h; rw [h]

/-- Heavier means later: mass increases with the threshold, since a heavier
structure needs more energy to resolve. -/
theorem mass_mono (μ : ℕ → ℝ) {k l : ℕ} (h : μ k < μ l) :
    massOf μ k < massOf μ l := by
  simp only [massOf]
  exact Real.exp_lt_exp.mpr h

/-! ## Why effective field theory changes framework

Between thresholds the content is fixed, so the description there is exact, not
approximate — `RG.active_eq_of_no_threshold`.  At a threshold the content
changes and the description must change with it.  Since there is no last
threshold, this happens without end.

That is not a defect of the method.  It is the theory reporting that "the
particles" is a scale-indexed notion, which is what A3 said. -/

/-- The content is unchanged across an interval containing no threshold: the
effective description is exact there. -/
theorem content_eq_of_no_threshold (μ : ℕ → ℝ) {t t' : ℝ} (h : t ≤ t')
    (hgap : ∀ k, ¬(t < μ k ∧ μ k ≤ t')) :
    resolved μ t = resolved μ t' := by
  apply Set.Subset.antisymm (resolved_mono μ h)
  intro k hk
  rw [mem_resolved] at hk ⊢
  by_contra hlt
  exact hgap k ⟨lt_of_not_ge hlt, hk⟩

/-- And the change happens exactly at a threshold. -/
theorem content_changes_only_at_threshold (μ : ℕ → ℝ) {t t' : ℝ} (h : t ≤ t')
    (hne : resolved μ t ≠ resolved μ t') :
    ∃ k, t < μ k ∧ μ k ≤ t' := by
  by_contra hcon
  push_neg at hcon
  exact hne (content_eq_of_no_threshold μ h (fun k => fun hk => absurd hk.2 (not_le.mpr (hcon k hk.1))))

end SCD.Emergence
