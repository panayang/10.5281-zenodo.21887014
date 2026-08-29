/-
# The shared vocabulary

Four notions were being written down repeatedly, each time in the vocabulary of
whichever file needed it, and then reconnected afterwards by equivalence
theorems.  They are collected here once, in the generality they are actually
used in, so that the reconnecting theorems become `rfl` and the development
speaks one language.

**Isotropy.**  `Frame.lean` wrote it as `∀ a b, E.s a = E.s b` for a
directional scale; `Gauge.lean` and `Axis.lean` wrote the same condition as a
loose hypothesis on `Fin n → Aˣ`; `Locus.lean` wrote it a third time for
`Fin k → ℝ`.  All three say **the pattern is constant**, and that is
`IsIsotropic`.

**Parallelism.**  `∀ i j, v i * w j = v j * w i` appears unnamed in
`Slice.lean`, `Axes.lean`, `Algebra.lean`, `Locus.lean` and `Dimension.lean` —
as the condition for two boosts to commute, for a wedge to vanish, for a
pattern to be combable, and for two isotropic patterns to generate no rotation.
It is one predicate, `Parallel`.

**The wedge.**  The framework's rotational label, `v ∧ w`.  It was defined in
`Slice.lean` over `ℝ`; nothing in it needs `ℝ`, and stating it over a ring is
what lets `NCConformal.lean`'s commutator correction and the rotational label be
compared as the same kind of object rather than by analogy.

**The two sector counts.**  `Slice.wedgeDim`/`dirDim` and
`Dimension.rotDim2`/`scaleDim2` were the same two functions under two names, and
A7 was then stated a third time in `Postulates.lean` and a fourth in
`Locus.lean` with `Iff.rfl` bridges between them.  There is one count of the
rotation sector, one of the scaling sector, and one A7.

Nothing here is new physics.  It is the language the rest of the development is
written in, and having it in one place is what makes the equalities below
identities rather than translations.
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

namespace SCD

/-! ## Isotropy: the pattern is constant

A scale pattern assigns something to each direction.  It is **isotropic** when
it assigns the same thing to every direction — when it distinguishes nothing.
The carrier varies (`Aˣ` for a directional scale, `ℝ` for a scaling vector) and
the notion does not. -/

/-- A pattern is **isotropic** when it takes the same value in every direction:
it distinguishes no direction from any other. -/
def IsIsotropic {ι : Type*} {α : Type*} (v : ι → α) : Prop := ∀ i j, v i = v j

namespace IsIsotropic

variable {ι α β : Type*}

/-- A constant pattern is isotropic. -/
theorem const (c : α) : IsIsotropic (fun _ : ι => c) := fun _ _ => rfl

/-- Isotropy is preserved by reading the pattern through any map — in
particular by passing from a unit to its underlying ring element, which is how
the same isotropy hypothesis serves `Frame.lean` and `Gauge.lean`. -/
theorem map {v : ι → α} (h : IsIsotropic v) (f : α → β) : IsIsotropic (f ∘ v) :=
  fun i j => congrArg f (h i j)

/-- On a nonempty index set, isotropic is exactly constant.  This is what makes
`Unify.isotropic_iff_ofScalar` a restatement rather than a construction. -/
theorem eq_const {v : ι → α} (h : IsIsotropic v) (i₀ i : ι) : v i = v i₀ := h i i₀

theorem iff_exists_const [Nonempty ι] {v : ι → α} :
    IsIsotropic v ↔ ∃ c, v = fun _ => c := by
  constructor
  · intro h
    exact ⟨v (Classical.arbitrary ι), funext fun i => h i _⟩
  · rintro ⟨c, rfl⟩
    exact const c

end IsIsotropic

/-! ## Parallelism, and the wedge that measures its failure -/

section Parallel

variable {ι : Type*} {α : Type*}

/-- Two patterns are **parallel** when they differ by no rotation:
`vᵢwⱼ = vⱼwᵢ` for every pair of directions.

This is simultaneously the condition for two boosts to commute
(`Algebra.boosts_commute_iff_parallel`), for the rotational label to vanish
(`wedge_eq_zero_iff_parallel`), and for a pattern to be combable
(`Axes.combable_no_rotation`).  Those are one condition, not three. -/
def Parallel [Mul α] (v w : ι → α) : Prop := ∀ i j, v i * w j = v j * w i

/-- **Two isotropic patterns are always parallel.**  Nothing is distinguished at
either end, so there is no plane for a rotation to live in.  This is the whole
of `Locus.isotropic_pair_parallel`, and it needs no commutativity: both readings
are literally the same product. -/
theorem IsIsotropic.parallel [Mul α] {v w : ι → α} (hv : IsIsotropic v)
    (hw : IsIsotropic w) : Parallel v w := fun i j => by rw [hv i j, hw j i]

section Comm

variable [CommMonoid α]

/-- Every pattern is parallel to itself — which is why a *homogeneous* pattern
generates no rotation, and why rotation needs the pattern to vary.

Note what this needs: **commutativity of the scale values**.  Where they fail to
commute — the quantum sector — a pattern is *not* parallel to itself, and the
failure is `wedge_self_eq_commutator` below.  That is the same fact
`NCConformal.Defm_antisymm_part` reports from the geometry side. -/
@[simp] theorem parallel_self (v : ι → α) : Parallel v v := fun _ _ => mul_comm _ _

theorem Parallel.symm {v w : ι → α} (h : Parallel v w) : Parallel w v :=
  fun i j => by rw [mul_comm, h j i, mul_comm]

end Comm

end Parallel

section Wedge

variable {ι : Type*} {α : Type*} [Ring α]

/-- The **rotational label** carried by two patterns: their wedge.

`Algebra.boost_bracket_spatial` shows this is exactly what the coupling
generates — the bracket of the two scalings, read on the spatial block.  It is
stated over a ring rather than over `ℝ` because the object it must be compared
with, `NCConformal`'s commutator correction, lives in a ring; the two are then
the same kind of antisymmetric object rather than an analogy. -/
def wedge (v w : ι → α) (i j : ι) : α := v i * w j - v j * w i

@[simp] theorem wedge_self_index (v w : ι → α) (i : ι) : wedge v w i i = 0 := by
  simp only [wedge, sub_self]

@[simp] theorem wedge_antisymm (v w : ι → α) (i j : ι) :
    wedge v w i j = -wedge v w j i := by
  simp only [wedge]; noncomm_ring

/-- **A pattern wedged with itself is the commutator of its own values.**

Classically this is zero, and that is `wedge_self` below — a homogeneous pattern
carries no rotational label, so rotation must come from the pattern's
*variation* (`Axes.lean`).  Where the values fail to commute it is not zero, and
what survives is exactly `[vᵢ, vⱼ]`: the object `NCConformal.Defm_antisymm_part`
identifies as the whole quantum-gravitational correction.  So the correction and
the rotational label are not analogous — they are one expression, evaluated in
the commuting and non-commuting cases. -/
theorem wedge_self_eq_commutator (v : ι → α) (i j : ι) :
    wedge v v i j = v i * v j - v j * v i := rfl

theorem wedge_bilinear_left (u v w : ι → α) (i j : ι) :
    wedge (u + v) w i j = wedge u w i j + wedge v w i j := by
  simp only [wedge, Pi.add_apply]; noncomm_ring

/-- **The rotational label vanishes exactly on parallel patterns.**

This single equivalence replaces `Slice.wedge_eq_zero_iff_parallel`,
`Axes.rotation_iff_variation` and `Axes.rotationless_is_trivial`, which were the
same statement and its two halves. -/
theorem wedge_eq_zero_iff_parallel (v w : ι → α) :
    (∀ i j, wedge v w i j = 0) ↔ Parallel v w := by
  simp only [wedge, sub_eq_zero, Parallel]

/-- Half of it, in the form the defect argument uses: a nonzero label forces the
patterns apart. -/
theorem not_parallel_of_wedge_ne_zero {v w : ι → α} {i j : ι}
    (h : wedge v w i j ≠ 0) : ¬ Parallel v w := by
  intro hpar
  exact h ((wedge_eq_zero_iff_parallel v w).mpr hpar i j)

/-- And the converse direction, used where a non-parallelism is exhibited
directly. -/
theorem wedge_ne_zero_of_ne {v w : ι → α} {i j : ι} (h : v i * w j ≠ v j * w i) :
    wedge v w i j ≠ 0 := by
  simp only [wedge, ne_eq, sub_eq_zero]
  exact h

/-- **Isotropic patterns carry no rotational label** — immediately, since they
are parallel. -/
theorem wedge_eq_zero_of_isotropic {v w : ι → α} (hv : IsIsotropic v)
    (hw : IsIsotropic w) (i j : ι) : wedge v w i j = 0 :=
  (wedge_eq_zero_iff_parallel v w).mpr (hv.parallel hw) i j

end Wedge

section WedgeComm

variable {ι : Type*} {α : Type*} [CommRing α]

/-- **A pattern wedged with itself vanishes** — in the commuting case.  So a
*homogeneous* pattern carries no rotational label; rotation is carried by the
pattern's variation, not by a second axis (`Axes.lean`). -/
@[simp] theorem wedge_self (v : ι → α) (i j : ι) : wedge v v i j = 0 := by
  simp only [wedge]; ring

theorem wedge_swap (v w : ι → α) (i j : ι) : wedge w v i j = -wedge v w i j := by
  simp only [wedge]; ring

/-- **Rescaling the pattern rescales the rotational label by `c²`**, so every
*ratio* of rotational labels is invariant: the overall magnitude of the pattern
is the unit the predictions are expressed in, not a prediction
(`Dimension.only_ratios_are_fixed`). -/
theorem wedge_smul_both (c : α) (v w : ι → α) (i j : ι) :
    wedge (c • v) (c • w) i j = c ^ 2 * wedge v w i j := by
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

/-- A pattern proportional to a fixed direction is **combable**: every wedge
among its values vanishes, so it generates no rotation anywhere. -/
theorem wedge_smul_smul (a b : α) (u : ι → α) (i j : ι) :
    wedge (a • u) (b • u) i j = 0 := by
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### What a per-direction rescaling can and cannot remove

A4′ assigns one unit per direction, so the framework's own gauge freedom is
**rescaling each axis separately**.  That freedom is large: it can flatten any
diagonal symmetric form at a point (`Light.physFormDir_eq_bareForm_rescaled`).
What it cannot do is remove a wedge — the rescaling only multiplies it by a
unit.

So the split between what is a coordinate choice and what is physical, at a
single point, is exactly the split between the symmetric and antisymmetric
parts.  This is what makes the antisymmetric quantum correction of
`NCConformal.lean` an observable rather than a gauge artefact. -/

/-- **A per-direction rescaling multiplies the wedge by `u_i u_j`.**

The rotational label is *covariant* under the framework's gauge freedom, not
invariant — but it is multiplied, never cancelled. -/
theorem wedge_rescale (u v w : ι → α) (i j : ι) :
    wedge (fun a => u a * v a) (fun a => u a * w a) i j = (u i * u j) * wedge v w i j := by
  simp only [wedge]
  ring

/-- **Hence no rescaling can make a nonzero wedge vanish.**

If the rescaling factors are units — which is what A4′ provides — then the wedge
is nonzero after rescaling exactly when it was nonzero before.  The
antisymmetric part is therefore not a coordinate choice, whatever the symmetric
part is doing. -/
theorem wedge_rescale_ne_zero {α : Type*} [CommRing α] {v w : ι → α} {i j : ι}
    (u : ι → αˣ) (h : wedge v w i j ≠ 0) :
    wedge (fun a => ((u a : α)) * v a) (fun a => ((u a : α)) * w a) i j ≠ 0 := by
  rw [wedge_rescale]
  intro hz
  apply h
  have hunit : IsUnit (((u i : α)) * ((u j : α))) := (u i * u j).isUnit
  obtain ⟨y, hy⟩ := hunit.exists_left_inv
  calc wedge v w i j = y * ((((u i : α)) * ((u j : α))) * wedge v w i j) := by
        rw [← mul_assoc, hy, one_mul]
    _ = 0 := by rw [hz, mul_zero]

end WedgeComm

/-! ## The two sector counts, and A7

The Cartan decomposition has two sectors: the scalings `p`, which A4 labels by
directions, and the rotations `Λ²p`, which the coupling generates from them.
Their dimensions are written doubled so that no natural-number division ever
appears, with `k = m + 1` spatial directions. -/

/-- Twice the dimension of the rotation sector `Λ²p`, with `k = m + 1`:
`2 · k(k−1)/2 = k(k−1)`. -/
def rotDim2 (m : ℕ) : ℕ := (m + 1) * m

/-- Twice the dimension of the scaling sector `p`, with `k = m + 1`. -/
def scaleDim2 (m : ℕ) : ℕ := 2 * (m + 1)

/-- **A7 (Observability).**  Every structure the coupling generates carries a
label the axioms provide: the rotations are exactly as numerous as the scale
directions A4 labels.

This is the single statement of A7.  It was previously written three times —
here, in `Locus.lean` in terms of the sector counts, and inline in
`Slice.lean` as `wedgeDim = dirDim` — with `Iff.rfl` bridges standing in for
the identification. -/
def Observability (m : ℕ) : Prop := rotDim2 m = scaleDim2 m

/-- **A7 holds at exactly one dimension: `k = 3`.**

`k(k−1)/2 = k` has the unique positive solution `k = 3`, so A7 is a genuine
restriction rather than a vacuous one, and given A7 the dimension is a theorem:
`k = 3`, hence `n = k + 1 = 4`. -/
theorem observability_iff_two (m : ℕ) : Observability m ↔ m = 2 := by
  simp only [Observability, rotDim2, scaleDim2]
  constructor
  · intro h
    have h' : m * (m + 1) = 2 * (m + 1) := by rw [mul_comm]; exact h
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) h'
  · rintro rfl; norm_num

theorem three_from_observability {m : ℕ} (h : Observability m) : m = 2 :=
  (observability_iff_two m).mp h

theorem observability_fails_elsewhere {m : ℕ} (h : m ≠ 2) : ¬ Observability m :=
  fun hobs => h (three_from_observability hobs)

theorem observability_unique : ∃! m : ℕ, Observability m :=
  ⟨2, (observability_iff_two 2).mpr rfl, fun _ hm => three_from_observability hm⟩

/-- Above three dimensions there are strictly more generated rotations than
there are directions to label them, so some rotation carries no label. -/
theorem more_rotations_than_directions (m : ℕ) (hm : 2 < m) : scaleDim2 m < rotDim2 m := by
  simp only [rotDim2, scaleDim2]
  have : 3 ≤ m := hm
  nlinarith

/-- And below three the rotation sector degenerates. -/
theorem fewer_rotations_than_directions (m : ℕ) (hm : m < 2) : rotDim2 m < scaleDim2 m := by
  interval_cases m <;> simp [rotDim2, scaleDim2]

end SCD
