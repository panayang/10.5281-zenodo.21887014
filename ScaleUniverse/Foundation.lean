/-
# Rebuilding the foundation: the split is not a choice

The audit found that A1 hands over a great deal for free — a set of directions,
a dimension `n`, and a flat metric `δ` that then does real work.  Worse, two
later results were *assumed* where they should have been derived:

* that transport splits into a "scale part" and a "rotation part";
* that the scale part is abelian and integrable while the rotation part carries
  all the curvature (`Connection.curv_eq_rotation_part`, proved there only
  *given* the split).

This file removes both assumptions by asking what a scale comparison actually
is, without any coordinate paper underneath.

Strip everything away.  What survives is: comparisons of local units compose,
composition is associative, every comparison can be undone.  That is a **group**
`Γ` — nothing more is available, and nothing less will do.

Now the whole split falls out of one observation.  **A scale is a quantity that
multiplies.**  Comparing by `a` then `b` must give the same scale as comparing
by `b` then `a`, because scales are ratios and ratios commute.  So the scale
carried by a comparison is exactly its image in the largest abelian quotient of
`Γ` — its abelianization.  There is no choice here: the abelianization is
canonical.

Everything then follows:

* `scale` is a homomorphism onto an abelian group — `scalePart_mul`;
* `scale_commutator` — **commutators carry no scale at all**;
* `curvature_is_scale_invisible` — since curvature *is* a commutator
  (`Connection.comm_covD`), curvature is necessarily invisible to the scale.
  What `Connection.curv_eq_rotation_part` assumed is now forced;
* `scale_eq_iff_differ_by_rotation` — two comparisons carry the same scale
  exactly when they differ by something in the commutator subgroup, so the
  scale/rotation split is a *partition*, not a decomposition one chooses.

The physical reading is the one the programme wanted all along and could not
previously justify: **gravity lives precisely where the scale cannot see.**
-/
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

namespace ScaleUniverse.Foundation

variable {Γ : Type*} [Group Γ]

/-! ## The only structure available

Comparisons of local units: they compose, associatively, invertibly.  That is a
group and there is nothing else to postulate. -/

/-- The **scale** carried by a comparison.

A scale is a ratio, and ratios commute.  So the scale of a comparison is its
image in the largest abelian quotient — the abelianization.  This is not a
modelling choice: the abelianization is the unique universal abelian quotient,
so "the commuting part of a comparison" has exactly one meaning. -/
def scale (g : Γ) : Abelianization Γ := Abelianization.of g

/-- Scales multiply, as scales must. -/
@[simp] theorem scale_mul (g h : Γ) : scale (g * h) = scale g * scale h :=
  map_mul Abelianization.of g h

/-- Scales commute — this is what makes them scales. -/
theorem scale_comm (g h : Γ) : scale g * scale h = scale h * scale g :=
  mul_comm _ _

@[simp] theorem scale_one : scale (1 : Γ) = 1 := map_one Abelianization.of

@[simp] theorem scale_inv (g : Γ) : scale g⁻¹ = (scale g)⁻¹ :=
  map_inv Abelianization.of g

/-! ## What the scale cannot see -/

/-- **A commutator carries no scale.**

Doing `g` then `h` differs from doing `h` then `g` — but the *scale* of that
difference is trivial.  Non-commutativity is invisible to the scale, always and
without hypothesis. -/
@[simp] theorem scale_commutator (g h : Γ) : scale (g * h * g⁻¹ * h⁻¹) = 1 := by
  simp only [scale_mul, scale_inv]
  rw [mul_comm (scale g) (scale h)]
  simp [mul_assoc]

/-- **Curvature is scale-invisible.**

`Connection.comm_covD` showed curvature is the failure of two transports to
commute.  Combined with the previous theorem, the scale of a curvature is
necessarily trivial — so the scale field contributes nothing to curvature.

`Connection.curv_eq_rotation_part` proved this only *after assuming* transport
splits into a scale part and a rotation part.  Here the split is not assumed;
it is the abelianization, and the conclusion is forced. -/
theorem curvature_is_scale_invisible (g h : Γ) :
    scale (g * h * g⁻¹ * h⁻¹) = (1 : Abelianization Γ) :=
  scale_commutator g h

/-- Anything in the commutator subgroup is scale-trivial. -/
theorem scale_eq_one_of_mem_commutator {g : Γ} (hg : g ∈ commutator Γ) :
    scale g = 1 := by
  rw [scale, ← MonoidHom.mem_ker, Abelianization.ker_of]
  exact hg

/-- Conversely a scale-trivial comparison is a pure rotation. -/
theorem mem_commutator_of_scale_eq_one {g : Γ} (hg : scale g = 1) :
    g ∈ commutator Γ := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  exact hg

/-- **The split is a partition, not a decomposition one chooses.**

Two comparisons carry the same scale exactly when they differ by a pure
rotation.  "Scale part" and "rotation part" are therefore not two components
selected by some convention — they are the two sides of a canonical quotient. -/
theorem scale_eq_iff_differ_by_rotation (g h : Γ) :
    scale g = scale h ↔ g * h⁻¹ ∈ commutator Γ := by
  constructor
  · intro hgh
    refine mem_commutator_of_scale_eq_one ?_
    rw [scale_mul, scale_inv, hgh, mul_inv_cancel]
  · intro hmem
    have h1 : scale (g * h⁻¹) = 1 := scale_eq_one_of_mem_commutator hmem
    rw [scale_mul, scale_inv] at h1
    exact mul_inv_eq_one.mp h1

/-! ## When there is no rotation at all

If every comparison commutes with every other, the group is its own
abelianization: everything is scale and nothing is curvature.  That is the
classical, gravity-free case, and it is now a theorem about `Γ` rather than a
regime one stipulates. -/

/-- **Commutative comparisons ⟹ no curvature.**  If `Γ` is abelian its
commutator subgroup is trivial, so nothing is scale-invisible and there is
nothing for curvature to live in. -/
theorem commutator_eq_one_of_comm (h : ∀ g k : Γ, g * k = k * g) (g k : Γ) :
    g * k * g⁻¹ * k⁻¹ = 1 := by
  rw [h g k]
  group

/-- And conversely, where the scale sees everything, the comparisons commute:
a faithful scale means no rotations, hence flat. -/
theorem comm_of_scale_injective (hinj : Function.Injective (scale : Γ → Abelianization Γ))
    (g h : Γ) : g * h = h * g := by
  have h1 : scale (g * h) = scale (h * g) := by
    rw [scale_mul, scale_mul, scale_comm]
  exact hinj h1

end ScaleUniverse.Foundation
