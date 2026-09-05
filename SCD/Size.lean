/-
# Sorting the rest of the escapes, and finding two of them are not content

`Content.lean` pulled three of the eight escapes to `ℝ` into one presheaf.  This
file asks the other five, and the answer is more useful than "yes" would have
been: **they are not all the same kind of object**, and what separates them is
exactly where the cosmological sector went wrong.

## The sort

| escape | what it is | fits `ContentSystem`? |
|---|---|---|
| `Emergence.resolved` | content on the scale axis | yes — `Content.lean` |
| `Resolution.Filtration` | content on the resolutions | yes — `Content.lean` |
| `Internal.record` | content on the parts, opposite variance | yes — `Content.lean` |
| `Particle.Species.threshold` | **the same content, described by thresholds** | yes — `ofThreshold` |
| `Spectrum.thresholdOfMass` | a reparameterisation of the *base* | not content, and not an escape |
| `Running.resolvedCount` | a **size** of content | no — one step away |
| `Scanning.scanRate` | a **rate**, the derivative of a size | no — two steps away |
| `Defect.ScaleDefect` | a section of a covering — a local system | no, and not a size either |

`ofThreshold` and `emergence_is_ofThreshold` do the fourth row: a threshold
function generates a content system and `Emergence.resolved` *is* the one it
generates, definitionally.  So thresholds and content are **two descriptions of
one datum**, and the count of independent escapes was too high.

## What the sort finds

**The cosmological sector is not "content nobody wrote as a presheaf".**  It is a
*size* and its *derivative*: `Running.resolvedCount` measures how much content
there is, and `Scanning.scanRate` differentiates that.  Neither is a presheaf and
neither was ever going to become one.

> They are two and three steps away from content, and the framework has never
> defined the step between: **what it means to measure how much content there
> is.**

`SizeSystem` names it, `resolvedSize` shows `resolvedCount` is one, and
`uniform_density_is_a_restriction` shows the shape it is given is a genuine
assumption — a size need not be affine in the index, and `t ↦ max t 0` is a
monotone count that is no `resolvedCount`.  That is the register's
long-standing uniform-density item, in the vocabulary and as a theorem rather
than a note.

## And a gap turns out to be one gap

`Layers.lean` closed with G4 open: outcomes are indistinguishability classes and
**nothing weights them**.  This file's missing step is *how much content there
is*.  Those are the same missing object — a measure on the content — approached
from the observer side and from the cosmological side.

> **G4 and the cosmological disconnection are one gap**, and it is the size, not
> the covering.

That settles what to do next in this direction, and it is not what was expected:
before asking when a family of resolutions *covers* a scale, ask what it means to
say how much is there.  A sheaf needs a site; a size needs less, and the
framework needs the size in two places already.

## What is not claimed

`Defect.ScaleDefect` fits nothing here.  It is a section of a covering with
quasiperiodic monodromy — a local system, which is a *sheaf* notion and not a
presheaf-on-a-preorder one.  So one of the eight remains outside the vocabulary
entirely, and it is the one carrying the winding.  That is a reason to keep the
sheaf direction open rather than a reason to take it now.
-/
import SCD.Content
import SCD.Running
import SCD.Scanning

namespace SCD.Size

open SCD Content


/-- **A size system**: a monotone real number attached to each index.

Not content — a *measure of* content.  The distinction is the finding of this
file: several of the remaining escapes to `ℝ` are not presheaves that nobody
wrote down, they are **sizes and their derivatives**, which is a different kind
of object living one and two steps away from content. -/
structure SizeSystem (I : Type*) [Preorder I] where
  /-- How much there is at index `i`. -/
  size : I → ℝ
  /-- And it does not decrease. -/
  mono : Monotone size

/-- **`Running.resolvedCount` is a size system**, for a non-negative density. -/
noncomputable def resolvedSize (ρ t₀ : ℝ) (hρ : 0 ≤ ρ) : SizeSystem ℝ where
  size t := Running.resolvedCount ρ t₀ t
  mono := by
    intro a b hab
    simp only [Running.resolvedCount]
    have : a - t₀ ≤ b - t₀ := by linarith
    exact mul_le_mul_of_nonneg_left this hρ

/-- **And its linearity is a restriction, not a shape it must have.**

A size system need not be affine in the index: `t ↦ max t 0` is monotone — it is
a count that stays at zero and then rises — and is no `resolvedCount`.  So "the thresholds are uniformly dense" — the register's
long-standing assumed item — is a genuine assumption about the size, and this is
that in the vocabulary. -/
theorem uniform_density_is_a_restriction :
    ∃ Z : SizeSystem ℝ, ∀ ρ t₀ : ℝ, Z.size ≠ fun t => Running.resolvedCount ρ t₀ t := by
  refine ⟨⟨fun t => max t 0, fun a b hab => max_le_max hab le_rfl⟩, ?_⟩
  intro ρ t₀ h
  have h0 := congrFun h 0
  have h1 := congrFun h (-1)
  have h2 := congrFun h 1
  simp only [Running.resolvedCount] at h0 h1 h2
  norm_num at h0 h1 h2
  rcases h0 with h0 | h0
  · rw [h0] at h2; norm_num at h2
  · rcases h1 with h1 | h1
    · rw [h1] at h2; norm_num at h2
    · rw [h0] at h1; norm_num at h1

/-! ## Thresholds are content, described the other way round -/

/-- **A threshold function generates a content system.**

`x` is present from `thr x` onwards.  So a threshold and a content are two
descriptions of one datum, not two data. -/
def ofThreshold {X : Type*} (thr : X → ℝ) : Content.ContentSystem ℝ X where
  content t := {x | thr x ≤ t}
  mono h _ hx := le_trans hx h

/-- **And `Emergence.resolved` is exactly that.**

So `Emergence`'s `μ` and `Particle.Species.threshold` are not two of the eight
escapes: they are the threshold description of the content system already
counted.  The list of independent escapes is shorter than it looked. -/
theorem emergence_is_ofThreshold (μ : ℕ → ℝ) :
    (ofThreshold μ).content = (Content.emergenceSystem μ).content := rfl


end SCD.Size
