/-
# Two topological charges, and only one of them is confined

`Axis.lean` restored point particles: a uniaxial scale pattern has an
unoriented axis for its order parameter, and such an order parameter carries
defects of two independent kinds.  This raises a question the framework had not
yet faced — are the charge of `Color.lean` and the charge of a point defect the
same quantum number, or two?

They are two, and the way they differ is the interesting part.

* The **block charge** is the permutation the degenerate directions undergo
  around a loop.  It lives in a *finite* group (the symmetries of the block),
  and it is the one `Color.lean` constrained: a configuration is observable only
  if the labelling closes up.
* The **hedgehog charge** is the integer wrapping of the axis over an enclosing
  sphere.  It lives in `ℤ`, and **nothing constrains it**.

So the framework produces exactly two topological quantum numbers, of different
types, and confinement applies to one and not the other:

* `block_confined` — a nontrivial block charge is not observable on its own;
* `hedgehog_free` — **every** integer hedgehog charge is carried by some
  observable state;
* `charges_independent` — neither determines the other.

That asymmetry is not put in.  It follows from the two charges living in
different homotopy groups of the same order parameter: the finite one comes
from loops, the integral one from spheres, and the observability condition —
that the *labelling* close up — can only see the first.

The resulting pattern is the observed one: a confined charge taking finitely
many values, alongside an unconfined integer charge.  The framework does not
derive that the finite group is `SU(3)`'s centre or that the integer is
electric charge; what it derives is that there must be exactly these two kinds,
and that precisely one of them is confined.

**Domain (see `Locus.lean`).**  These charges describe the **anisotropic**
locus.  A fully degenerate scale pattern supports no order parameter
(`Axis.isotropic_no_order_parameter`), hence no defect and no charge; and
whether the pattern is degenerate is a scale-dependent fact.  So the labels
below are not scale-invariant properties of the world — they come into existence
where isotropy breaks, together with the multiplets and the curvature, since all
three have one source.
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

namespace SCD.Charges

variable {B : Type*} [Group B]

/-! ## The two charges -/

/-- The complete topological charge of a point defect in a uniaxial scale
pattern: a block permutation and an integer wrapping. -/
structure DefectCharge (B : Type*) [Group B] where
  /-- How the degenerate block is relabelled around a loop — the finite charge. -/
  block : B
  /-- How the axis wraps the enclosing sphere — the integral charge. -/
  hedgehog : ℤ

namespace DefectCharge

/-- Bringing two defects together. -/
def comp (c d : DefectCharge B) : DefectCharge B where
  block := c.block * d.block
  hedgehog := c.hedgehog + d.hedgehog

/-- The reversed defect. -/
def anti (c : DefectCharge B) : DefectCharge B where
  block := c.block⁻¹
  hedgehog := -c.hedgehog

/-- The vacuum. -/
def triv (B : Type*) [Group B] : DefectCharge B where
  block := 1
  hedgehog := 0

@[simp] theorem comp_block (c d : DefectCharge B) :
    (c.comp d).block = c.block * d.block := rfl
@[simp] theorem comp_hedgehog (c d : DefectCharge B) :
    (c.comp d).hedgehog = c.hedgehog + d.hedgehog := rfl
@[simp] theorem anti_block (c : DefectCharge B) : c.anti.block = c.block⁻¹ := rfl
@[simp] theorem anti_hedgehog (c : DefectCharge B) : c.anti.hedgehog = -c.hedgehog := rfl

/-! ## Observability sees only the finite charge

A configuration is realisable when the *labelling* of the block closes up
around the loop.  That is a condition on the block charge alone; the wrapping
of the axis over a sphere is not a labelling and is not constrained by it. -/

/-- Observability: the block labelling closes up.  Note what is absent — no
condition whatsoever on `hedgehog`. -/
def Observable (c : DefectCharge B) : Prop := c.block = 1

@[simp] theorem triv_observable : Observable (triv B) := rfl

/-- **The finite charge is confined.**  A defect that genuinely permutes the
block cannot stand alone. -/
theorem block_confined (c : DefectCharge B) (h : c.block ≠ 1) : ¬ Observable c := h

/-- **The integral charge is not confined.**

For every integer there is an observable state carrying it.  Nothing in the
framework prevents an isolated defect from having any wrapping number at all —
in sharp contrast to the block charge. -/
theorem hedgehog_free (k : ℤ) :
    ∃ c : DefectCharge B, Observable c ∧ c.hedgehog = k :=
  ⟨⟨1, k⟩, rfl, rfl⟩

/-- Sharpened: observable states realise *every* integer, so the integral charge
is completely unconstrained by observability. -/
theorem hedgehog_surjective_on_observables :
    ∀ k : ℤ, ∃ c : DefectCharge B, Observable c ∧ c.hedgehog = k := hedgehog_free

/-- **The asymmetry, stated in one place.**

One charge is constrained by observability and the other is not.  This is the
whole structural content: confinement is not a property of "charge", it is a
property of the *finite* charge only. -/
theorem exactly_one_confined :
    (∀ c : DefectCharge B, Observable c → c.block = 1)
    ∧ (∀ k : ℤ, ∃ c : DefectCharge B, Observable c ∧ c.hedgehog = k) :=
  ⟨fun _ h => h, hedgehog_free⟩

/-! ## The two charges are independent -/

/-- Fixing the block charge leaves the integral charge free. -/
theorem hedgehog_not_determined_by_block (b : B) (k l : ℤ) (h : k ≠ l) :
    ∃ c d : DefectCharge B, c.block = d.block ∧ c.hedgehog ≠ d.hedgehog :=
  ⟨⟨b, k⟩, ⟨b, l⟩, rfl, h⟩

/-- And fixing the integral charge leaves the block charge free. -/
theorem block_not_determined_by_hedgehog (b b' : B) (k : ℤ) (h : b ≠ b') :
    ∃ c d : DefectCharge B, c.hedgehog = d.hedgehog ∧ c.block ≠ d.block :=
  ⟨⟨b, k⟩, ⟨b', k⟩, rfl, h⟩

/-- Collected: the two charges are genuinely independent quantum numbers, not
two readings of one. -/
theorem charges_independent (b b' : B) (k l : ℤ) (hb : b ≠ b') (hk : k ≠ l) :
    (∃ c d : DefectCharge B, c.block = d.block ∧ c.hedgehog ≠ d.hedgehog)
    ∧ (∃ c d : DefectCharge B, c.hedgehog = d.hedgehog ∧ c.block ≠ d.block) :=
  ⟨hedgehog_not_determined_by_block b k l hk,
   block_not_determined_by_hedgehog b b' k hb⟩

/-! ## Both charges are additive and conserved -/

@[simp] theorem pair_observable (c : DefectCharge B) : Observable (c.comp c.anti) := by
  simp only [Observable, comp_block, anti_block, mul_inv_cancel]

@[simp] theorem pair_hedgehog_zero (c : DefectCharge B) :
    (c.comp c.anti).hedgehog = 0 := by
  simp only [comp_hedgehog, anti_hedgehog, add_neg_cancel]

/-- An observable pair of defects can carry any total integral charge, provided
their block charges cancel.  So the integral charge of an observable state is
free while the block charge of one is not — the two conservation laws have
different characters. -/
theorem observable_pair_any_hedgehog (b : B) (k l : ℤ) :
    Observable ((⟨b, k⟩ : DefectCharge B).comp ⟨b⁻¹, l⟩)
      ∧ ((⟨b, k⟩ : DefectCharge B).comp ⟨b⁻¹, l⟩).hedgehog = k + l := by
  constructor
  · simp only [Observable, comp_block, mul_inv_cancel]
  · rfl

end DefectCharge

end SCD.Charges
