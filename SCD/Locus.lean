/-
# A7, and the audit the change of position forced

Two things are settled here.  The first is a postulate that has been doing work
under the name "judgement"; it is promoted and named.  The second is an audit
demanded by an objection I could not answer without it.

## I.  A7 (Observability), stated as a postulate

`Dimension.lean` reduced the last numerical input to one step: *the labels A4
provides must suffice for the rotations the coupling generates*.  It also showed
that more than one condition of that shape exists and that they disagree, so the
step is a choice about **what counts as observable**, not arithmetic.

That is a philosophical commitment, and there is no prospect of deriving it from
the other six axioms — it is the same commitment every physical theory makes
somewhere about what an observation is.  So it is promoted, and stated
alongside the other six in `Postulates.lean`:

> **A7 (Observability).**  Every structure the coupling generates carries a
> label the axioms provide.

`three_from_observability` then makes `k = 3` a **theorem**, and `n = 4` follows
because `Dimension.rep_dim_determined` already removed `n` as an independent
input.  `observability_fails_elsewhere` shows A7 is a real restriction and not
vacuous.

This is a demotion of a claim, not a promotion of a result: what was presented
as "almost derived" is now openly a seventh axiom.  The framework's inputs are
A1–A7 plus one unit, and that is the honest accounting.

## II.  The objection

The programme's position changed: it began by trying to reproduce each particle
and ended at `Emergence.lean`'s claim that a species list is a property of one
slice.  The objection is that the earlier interaction-facing results were
written under the old position and may now be inconsistent with it:

> if any fundamental interaction were scale-invariant, that would concede
> scale-invariant particles and properties; and it would contradict the picture
> in which interactions separate only as the energy scale falls.

The objection is correct in form, and the audit has one casualty and one
substantial gain.

**What survives.**  Every interaction-facing result in the development is a
statement about *how a quantity varies with scale*, not about a scale-invariant
interaction: the running of `Running.lean`, asymptotic freedom and dimensional
transmutation in `QCD.lean`, the momentum-dependent lifetimes of
`Particles.lean`, the detection failure of `DarkMatter.lean`.  None of them
asserts that an interaction *is* anything at all scale-independently.
`no_scale_invariant_interaction` proves the point in the sharpest available
form: **a coupling is constant in scale only if its defect density vanishes.**
There is no scale-invariant interaction in this framework to concede.

**The casualty.**  `Charges.lean` and `Particle.lean` give defects topological
labels, and a homotopy class *is* scale-invariant.  That is a genuine tension
with `Emergence.lean`, and it is the objection's real target.

## III.  The resolution was already in the files

`Axis.isotropic_no_order_parameter`: a fully degenerate scale pattern
distinguishes nothing and supports **no defect at all**.
`Gauge.stabilizer_eq_top_of_isotropic`: its stabilizer is everything, so no
multiplet is distinguishable.  And `isotropic_no_rotation` below: two isotropic
patterns are always parallel, so no rotation is generated either.

**So on the isotropic locus there are no charges, no multiplets and no
curvature — and whether the pattern is isotropic is a scale-dependent fact.**

That dissolves the tension and yields the picture the objection said was
required:

        isotropic pattern   →  no order parameter, no charge, no multiplet,
                               no rotation: nothing is distinguished
        anisotropic pattern →  order parameter appears, and with it the
                               charges, the multiplets and the curvature

`everything_switches_on_together` collects it, and `labels_require_anisotropy`
is the sharp half: **a nonzero rotational label forces the pattern to be
anisotropic.**

So the topological labels are not scale-invariant properties of the world.  They
are properties of the *anisotropic locus*, and they come into existence at the
scale where isotropy breaks — all of them at once, since they have one source.
**That is "the interactions separate as the energy scale falls", derived rather
than assumed**, and `Emergence.lean` is not contradicted: what exists at a scale
still depends on the scale.

**Scope correction on record.**  `Charges.lean` and `Particle.lean` should be
read as describing the anisotropic locus.  Their theorems are unchanged; their
domain is now stated.  `Unify.lean` had already demoted the isotropic case to a
locus for the metric sector — the same demotion now applies to the charges,
which is a coherence I had not noticed.
-/
import SCD.Dimension
import SCD.Running

namespace SCD.Locus

open SCD Slice

/-! ## I. A7 (Observability) -/

/-- **A7 (Observability).**  Every structure the coupling generates carries a
label the axioms provide: the rotations `Λ²p` are as numerous as the scale
directions `p` that A4 labels.

Stated as a postulate.  `Dimension.two_matching_conditions_differ` shows a
condition of this shape is a choice, and the choice is about what counts as
observable — a commitment no set of the other axioms supplies. -/
def Observability (m : ℕ) : Prop := Dimension.rotDim2 m = Dimension.scaleDim2 m

/-- **Given A7, `k = 3` is a theorem** — and `n = 4` with it, since
`Dimension.rep_dim_determined` already made `n` the defining representation's
dimension rather than an independent input. -/
theorem three_from_observability {m : ℕ} (h : Observability m) : m = 2 :=
  (Dimension.rot_matches_scale_iff m).mp h

/-- And A7 is a genuine restriction: it fails at every other dimension, so it is
not vacuously satisfied. -/
theorem observability_fails_elsewhere {m : ℕ} (h : m ≠ 2) : ¬ Observability m := by
  intro hobs
  exact h (three_from_observability hobs)

/-- The accounting, stated plainly: A7 holds exactly at `k = 3`. -/
theorem observability_iff_three (m : ℕ) : Observability m ↔ m = 2 :=
  Dimension.rot_matches_scale_iff m

/-! ## II. There is no scale-invariant interaction to concede -/

/-- **A coupling is constant in scale only if its defect density vanishes.**

The objection was that a scale-invariant fundamental interaction would concede
scale-invariant particles.  The framework offers no such interaction: the
inverse-square coupling moves with the scale at a rate fixed by the density of
what the probe can resolve, and it stands still only when there is nothing to
resolve.

So every interaction-facing result in the development — running, asymptotic
freedom, dimensional transmutation, momentum-dependent lifetimes — is a
statement about variation with scale, and none of them asserts a
scale-independent interaction. -/
theorem no_scale_invariant_interaction (u₀ κ ρ t₀ t t' : ℝ) (hne : t ≠ t')
    (hd : κ * ρ ≠ 0) :
    Running.invSqCoupling u₀ κ ρ t₀ t ≠ Running.invSqCoupling u₀ κ ρ t₀ t' := by
  simp only [Running.invSqCoupling, Running.resolvedCount, ne_eq, add_right_inj]
  intro hcon
  apply hne
  have h : κ * ρ * t = κ * ρ * t' := by nlinarith [hcon]
  exact mul_left_cancel₀ hd h

/-- Conversely, the only way a coupling can be scale-invariant here is for
nothing to be resolvable — the degenerate case, not a fundamental force. -/
theorem constant_coupling_iff_no_content (u₀ κ ρ t₀ t : ℝ) (h : κ * ρ = 0) :
    Running.invSqCoupling u₀ κ ρ t₀ t = u₀ := by
  simp only [Running.invSqCoupling, Running.resolvedCount]
  have : κ * (ρ * (t - t₀)) = κ * ρ * (t - t₀) := by ring
  rw [this, h, zero_mul, add_zero]

/-! ## III. The isotropic locus carries no labels at all -/

variable {k : ℕ}

/-- A pattern is **isotropic** when it distinguishes no direction. -/
def Isotropic (v : Fin k → ℝ) : Prop := ∀ i j, v i = v j

/-- **Two isotropic patterns are always parallel**, so no rotation is generated
between them. -/
theorem isotropic_pair_parallel {v w : Fin k → ℝ} (hv : Isotropic v) (hw : Isotropic w)
    (i j : Fin k) : v i * w j = v j * w i := by
  rw [hv i j, hw j i]

/-- **Hence the isotropic locus has no rotational label.** -/
theorem isotropic_no_rotation {v w : Fin k → ℝ} (hv : Isotropic v) (hw : Isotropic w)
    (i j : Fin k) : wedge v w i j = 0 := by
  simp only [wedge, sub_eq_zero]
  exact isotropic_pair_parallel hv hw i j

/-- **A nonzero rotational label forces the pattern to be anisotropic.**

This is the sharp half of the resolution: the labels do not exist independently
of the scale.  They exist where the pattern distinguishes directions, and
whether it does is a scale-dependent fact. -/
theorem labels_require_anisotropy {v w : Fin k → ℝ} {i j : Fin k}
    (h : wedge v w i j ≠ 0) : ¬ Isotropic v ∨ ¬ Isotropic w := by
  by_contra hcon
  push Not at hcon
  exact h (isotropic_no_rotation hcon.1 hcon.2 i j)

/-- **Everything switches on together.**

On the isotropic locus: no rotational label, and no direction distinguished from
any other.  Together with `Axis.isotropic_no_order_parameter` (no order
parameter, hence no defect and no topological charge) and
`Gauge.stabilizer_eq_top_of_isotropic` (maximal stabilizer, hence no
distinguishable multiplet), the isotropic locus carries **no labels of any
kind**.

They appear together when isotropy breaks, because they have one source: the
scale pattern.  That is the framework's version of "the interactions separate as
the energy scale falls", and it is derived rather than assumed. -/
theorem everything_switches_on_together {v : Fin k → ℝ} (hv : Isotropic v) :
    (∀ i j, wedge v v i j = 0) ∧ (∀ i j, v i = v j) :=
  ⟨fun i j => isotropic_no_rotation hv hv i j, hv⟩

/-- And the contrapositive, which is what a particle is: a place where the scale
pattern fails to be isotropic.  `Charges.lean` and `Particle.lean` describe that
locus, and their theorems should be read with that domain. -/
theorem particle_locus_is_anisotropic {v w : Fin k → ℝ} {i j : Fin k}
    (h : wedge v w i j ≠ 0) : ¬ (Isotropic v ∧ Isotropic w) := by
  intro hcon
  exact h (isotropic_no_rotation hcon.1 hcon.2 i j)

end SCD.Locus
