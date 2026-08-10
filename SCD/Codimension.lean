/-
# What a winding defect actually is in three dimensions

Trying to pin the dimension `n` from the algebra turned up a problem with
`Defect.lean` instead, and the problem is more interesting than the dimension
would have been.

`Defect.lean` says: "around any loop enclosing a point, the scale may fail to
close up".  In two spatial dimensions that sentence is fine — a loop does
enclose a point.  **In three it is false.**  A loop in three-dimensional space
does not enclose a point; it encloses a *line*.  What a loop detects is a locus
of codimension two, and codimension two in three dimensions is one-dimensional.

So a circle-valued scale in three spatial dimensions does not produce point
particles.  It produces **strings**.

This is forced, not chosen.  The scale is *one* number — a ratio — so the field
it defines is circle-valued and its defects are classified by loops.  Nothing
in the framework offers a second scale that would let defects be points in three
dimensions.  The conclusion has to be accepted or the framework changed.

What follows:

* `defectDim` — a winding defect in `d` spatial dimensions has dimension
  `d − 2`;
* `pointlike_iff_two_dim` — point-like winding defects require **two** spatial
  dimensions, hence a `2+1` world;
* `three_dim_gives_strings` — in our three, defects are one-dimensional;
* `string_mass_not_topological` — a one-dimensional defect has mass
  proportional to its *length*, which the winding does not determine.  This
  reaches the conclusion of `MassAudit.mass_law_underdetermined` by a
  completely independent route, and explains *why* the mass law was
  underdetermined: the object has extension that the topology never fixed.

**SUPERSEDED IN SCOPE — see `Axis.lean`.**  Everything below is true of a
*circle-valued* scale, which is what `Defect.lean` uses.  It is **not** true of
the framework as axiomatised: A4 provides one scale **per direction**, so the
order parameter is a pattern of scales, not a phase.  Because a scale is a ratio
it cannot see the orientation of a direction, the order parameter is an
unoriented axis, and a projective order parameter carries integer-charged
**point** defects as well as strings.

Applying scalar-scale reasoning where the axiom is directional is the same
mistake `Frame.lean` diagnosed for geometry; it was made a second time here and
is corrected in `Axis.lean`.  The theorems below stand as statements about the
circle-valued case, and as a record of the error.

The codimension-two fact itself is standard topology and is taken as input
here rather than proved.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace SCD.Codimension

/-! ## What a loop can detect -/

/-- The dimension of the locus a loop can wind around, in `d` spatial
dimensions.  A loop detects codimension two; nothing about the scale offers a
way to detect anything else, because the scale is a single ratio and so the
field it defines is circle-valued. -/
def defectDim (d : ℕ) : ℕ := d - 2

@[simp] theorem defectDim_two : defectDim 2 = 0 := rfl
@[simp] theorem defectDim_three : defectDim 3 = 1 := rfl
@[simp] theorem defectDim_four : defectDim 4 = 2 := rfl

/-- **Point-like winding defects require exactly two spatial dimensions.**

`Defect.lean` pictured a defect as a point with a loop around it.  That picture
is available only in `d = 2`. -/
theorem pointlike_iff_two_dim (d : ℕ) (hd : 2 ≤ d) : defectDim d = 0 ↔ d = 2 := by
  constructor
  · intro h
    simp only [defectDim] at h
    omega
  · intro h
    rw [h]
    rfl

/-- **In three spatial dimensions a winding defect is a string.**

Not a point with internal structure — a genuinely one-dimensional object. -/
theorem three_dim_gives_strings : defectDim 3 = 1 := rfl

/-! ## Spacetime dimension

`Signature.lean` derived exactly one time direction from the scale drift.  So
spacetime dimension is spatial dimension plus one, and the two scenarios are
sharply separated. -/

/-- Spacetime dimension: space plus the single drift direction. -/
def spacetimeDim (d : ℕ) : ℕ := d + 1

/-- If the fundamental excitations are point-like, the world is `2+1`. -/
theorem pointlike_forces_three (d : ℕ) (hd : 2 ≤ d) (h : defectDim d = 0) :
    spacetimeDim d = 3 := by
  rw [(pointlike_iff_two_dim d hd).mp h]
  rfl

/-- In a `3+1` world the excitations are one-dimensional.  The framework does
not get to have both. -/
theorem our_world_gives_strings :
    spacetimeDim 3 = 4 ∧ defectDim 3 = 1 := ⟨rfl, rfl⟩

/-- The two possibilities are mutually exclusive: no spatial dimension gives
both point-like defects and a `3+1` spacetime. -/
theorem no_pointlike_in_four (d : ℕ) (hd : 2 ≤ d) (h4 : spacetimeDim d = 4) :
    defectDim d ≠ 0 := by
  intro h0
  have h2 : d = 2 := (pointlike_iff_two_dim d hd).mp h0
  rw [h2] at h4
  simp only [spacetimeDim] at h4
  omega

/-! ## Why the mass law was underdetermined

An extended defect has a mass that depends on how much of it there is.  Winding
is a topological invariant and says nothing about length, so it cannot fix the
mass — which is exactly what `MassAudit` found by inspecting candidate laws.
Here the same conclusion arrives from the geometry of the defect. -/

/-- Mass of a one-dimensional defect: tension times length. -/
noncomputable def stringMass (tension length : ℝ) : ℝ := tension * length

/-- **Winding does not determine mass.**

Two defects of the *same* winding but different length have different mass.  So
no function of the winding alone can be the mass law — independently confirming
`MassAudit.mass_law_underdetermined`, and explaining its cause: the defect is
extended, and topology never measured the extension. -/
theorem string_mass_not_topological (tension : ℝ) (ht : 0 < tension)
    (L₁ L₂ : ℝ) (hL : L₁ ≠ L₂) :
    stringMass tension L₁ ≠ stringMass tension L₂ := by
  simp only [stringMass]
  intro hcon
  exact hL (mul_left_cancel₀ (ne_of_gt ht) hcon)

/-- Mass grows with length at fixed winding, so the spectrum of a string defect
is continuous in the length — not a tower indexed by an integer. -/
theorem stringMass_strictMono (tension : ℝ) (ht : 0 < tension)
    {L₁ L₂ : ℝ} (h : L₁ < L₂) : stringMass tension L₁ < stringMass tension L₂ := by
  simp only [stringMass]
  exact mul_lt_mul_of_pos_left h ht

/-- A closed string of zero length is massless: the vacuum is the degenerate
case, consistently with `Defect.mass_zero`. -/
@[simp] theorem stringMass_zero (tension : ℝ) : stringMass tension 0 = 0 := by
  simp only [stringMass, mul_zero]

/-! ## The choice the framework now faces

Either the fundamental excitations are extended — in which case `Defect.lean`'s
point picture must be replaced by a string picture, and the mass spectrum is not
a tower — or the scale is not circle-valued, in which case the discrete scale
invariance of `Defect.lean` and the block monodromy of `Color.lean` both go.

We record the disjunction rather than choosing, because nothing proved so far
decides it. -/

/-- The disjunction, stated: for any spatial dimension at least two, either the
defects are extended or the world is `2+1`. -/
theorem extended_or_low_dimensional (d : ℕ) (hd : 2 ≤ d) :
    defectDim d ≠ 0 ∨ spacetimeDim d = 3 := by
  rcases Nat.eq_or_lt_of_le hd with h | h
  · right
    rw [← h]
    rfl
  · left
    simp only [defectDim]
    omega

end SCD.Codimension
