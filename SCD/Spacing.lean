/-
# Taking the missing link, and watching it fail

§V.x registered a gap and named it precisely: **nothing connects `Spectrum.gaps`
to `Internal.record`.**  `Layers.lean` narrowed it — the thresholds a filtration
assigns are *computed from the ring*, not postulated — and then said, correctly,
that identifying them with the measured ones was still not done.

This file does it, in the simplest case, and the identification **dies against
the data**.

## The chain

`Layers.monomial_threshold` gives `Xʲ` the threshold `j`: a filtration by powers
of one element spaces its thresholds evenly.  With a step of size `c` that is
`a + c·j`, which is `PowerSpaced`.  Then

* `gapList_replicate` — the gaps are a constant list;
* `powerSpaced_variance_zero` — so their variance is zero, which is
  `Spectrum.equal_gaps_variance_zero` reached from the filtration side rather
  than from the geometric tower;
* `observed_variance_ne_zero` — and the observed gaps have variance ≈ 1.17;
* `thresholds_not_power_spaced` — **so the physical thresholds are not
  power-spaced.**

The hypothesis doing the identifying appears in the statement, where
`Anchor.Falsifiable`'s discipline says it must: what is proved is that *if* the
measured gaps are a filtration's, the filtration is not by powers of one element.

## Why this is worth more than a negative result

**It is the third time the framework has met equal spacing and lost.**
`MassAudit` retracted the geometric mass tower `m_k = m₀e^{kΔ}`;
`Period.retraction_closed_the_route` recorded that the same retraction closed the
only route from the spectrum to the gravitational coupling; and now the
*algebraic* notion of resolution, taken in its simplest form, **reproduces the
tower that was already excluded.**  Equal spacing is this framework's recurring
wrong answer, and that is now a theorem rather than a memory.

**And it specifies the replacement.**  The gaps must have `CV = 1` — exponential,
not constant — so the filtration's layers cannot be indexed by `ℕ` with a fixed
step.  They must themselves be placed by a constant-rate process on the scale
axis.  That is a sharp target: *a filtration whose layer set is Poisson rather
than arithmetic*, and it is the shape `Spectrum.lean`'s prediction demands.

## What this does not do

* it excludes **power-spaced** thresholds, not every filtration.  §V.x's gap is
  narrowed, not closed: the link is now testable and its simplest instance is
  refuted;
* it says nothing about `Δρ`, and cannot.  `gapList_shift_invariant` is half the
  reason — every gap statistic is blind to a shift, which is A5 — and the other
  half is the reading that A5's full shift-invariance leaves no gap statistic
  able to single out a *period*.  If that reading holds, **no statistic of the
  spectrum can ever fix the scale period**, and the second relation the framework
  needs must be combinatorial: how many windings there are per threshold.  That
  is stated as a reading and not proved here.
-/
import SCD.Layers
import SCD.Spectrum

namespace SCD.Spacing

open SCD


open SCD

/-- **Power-spaced thresholds**: an arithmetic progression on the scale axis.

This is what a filtration by powers of a single element gives —
`Layers.monomial_threshold` assigns `Xʲ` the threshold `j`, and a step of size
`c` rescales that to `a + c·j`. -/
def PowerSpaced (thr : ℕ → ℝ) : Prop := ∃ a c : ℝ, ∀ j : ℕ, thr j = a + c * j

/-- The power filtration of `Layers.lean` is power-spaced, with step one. -/
theorem monomial_powerSpaced : PowerSpaced (fun j => (j : ℝ)) :=
  ⟨0, 1, fun j => by ring⟩

/-- The consecutive gaps of a threshold sequence. -/
noncomputable def gapList (thr : ℕ → ℝ) (m : ℕ) : List ℝ :=
  (List.range m).map (fun j => thr (j + 1) - thr j)

/-- **Power spacing gives a constant gap list.** -/
theorem gapList_replicate {thr : ℕ → ℝ} (h : PowerSpaced thr) (m : ℕ) :
    ∃ c : ℝ, gapList thr m = List.replicate m c := by
  obtain ⟨a, c, hthr⟩ := h
  refine ⟨c, ?_⟩
  have : (fun j : ℕ => thr (j + 1) - thr j) = fun _ => c := by
    funext j
    rw [hthr (j + 1), hthr j]
    push_cast
    ring
  rw [gapList, this]
  rw [show (fun _ : ℕ => c) = Function.const ℕ c from rfl, List.map_const,
    List.length_range]

/-- **Hence zero variance**, which is `Spectrum.equal_gaps_variance_zero`
reached from the filtration side. -/
theorem powerSpaced_variance_zero {thr : ℕ → ℝ} (h : PowerSpaced thr) {m : ℕ}
    (hm : 0 < m) : Spectrum.variance (gapList thr m) = 0 := by
  obtain ⟨c, hc⟩ := gapList_replicate h m
  rw [hc]
  exact Spectrum.equal_gaps_variance_zero m hm c

/-- **But the observed gaps do not have zero variance.** -/
theorem observed_variance_ne_zero : Spectrum.gapVariance ≠ 0 := by
  norm_num [Spectrum.gapVariance, Spectrum.meanGap, Spectrum.gapSum, Spectrum.gapSqSum]

/-- **So the physical thresholds are not power-spaced.**

The hypothesis `hid` is §V.x's missing link in its simplest form — that the
thresholds the spectrum measures are the ones a filtration assigns.  Taking that
link and a filtration by powers of one element together contradicts the data. -/
theorem thresholds_not_power_spaced {thr : ℕ → ℝ} (h : PowerSpaced thr) {m : ℕ}
    (hm : 0 < m) (hid : Spectrum.gapVariance = Spectrum.variance (gapList thr m)) :
    False := by
  rw [powerSpaced_variance_zero h hm] at hid
  exact observed_variance_ne_zero hid

/-- **The gaps cannot see a shift of the whole spectrum.**

Cheap, and it is half of why the spectrum cannot measure the scale period: every
statistic of the gaps is invariant under `σ ↦ σ + c`, which is A5.  The other
half — that no gap statistic singles out a *period* either — follows from A5's
full shift invariance and is a reading, not this theorem. -/
theorem gapList_shift_invariant (thr : ℕ → ℝ) (c : ℝ) (m : ℕ) :
    gapList (fun j => thr j + c) m = gapList thr m := by
  simp only [gapList]
  congr 1
  funext j
  ring


end SCD.Spacing
