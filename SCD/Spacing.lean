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
* it says nothing about `Δρ`.  How *little* it says is measured in §II below,
  and the measurement corrects a tempting overstatement.

## II.  How wide the blindness is — exactly one pure number

It is easy to say the spectrum "cannot see the scale period" and stop.  That is
too strong, and §II is what happens when it is checked.

`gapList_shift_invariant` and `gapList_rescale` fix the gaps' behaviour: they are
blind to a shift of the whole spectrum, and they scale with it.  So the period
and the mean gap have the **same weight**, `ratio_invariant` makes their ratio
the invariant, and `unique_pure_number` says exactly one real number relates
them.  Therefore

> the spectrum determines the period **up to one pure factor**, and that factor
> is `Δρ`.

**Which means the blindness is not structural, and the claim that it is would be
wrong.**  `Δρ` has weight zero; the gap data *has* weight-zero content — `CV²`;
so a relation `Δρ = f(CV², …)` is type-correct.  Nothing excludes a spectral
determination of `Δρ`.  **Nobody has proposed one.**  The route is empty, not
closed, and saying "the second relation must be combinatorial" claims an
exclusion that has not been proved.  It remains one plausible direction beside
another.

That correction matters because the whole reason for looking at the winding count
was that the spectral route had been ruled out.  It has not.
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


/-! ## II.  The width of the blindness -/


/-- **Rescaling the scale axis scales every gap by the same factor.**

`Weight.lean` gives the gaps weight one, and this is that, computed rather than
assigned. -/
theorem gapList_rescale (thr : ℕ → ℝ) (c : ℝ) (m : ℕ) :
    gapList (fun j => c * thr j) m = (gapList thr m).map (fun g => c * g) := by
  simp only [gapList, List.map_map]
  congr 1
  funext j
  simp only [Function.comp_apply]
  ring

/-- **The period has the same weight as a gap, so their ratio is the invariant.**

Under `σ ↦ cσ` both the period and the mean gap scale by `c`, so the pure number
they form does not move.  This is `Weight.product_invariant` for the pair that
matters. -/
theorem ratio_invariant (Δ mg c : ℝ) (hc : c ≠ 0) (hmg : mg ≠ 0) :
    (c * Δ) / (c * mg) = Δ / mg := by
  field_simp

/-- **And exactly one pure number relates them.**

Given the gaps — hence the mean gap — the period is fixed by one real number and
no more.  The blindness of the spectrum to the period is therefore *exactly one
pure number wide*: it is not that the spectrum says nothing about `Δ`, it is that
it says everything except this. -/
theorem unique_pure_number (Δ mg : ℝ) (hmg : mg ≠ 0) : ∃! r : ℝ, Δ = r * mg := by
  refine ⟨Δ / mg, by field_simp, ?_⟩
  intro r hr
  field_simp at hr ⊢
  rw [hr]

/-- **The gaps do determine the mean gap**, which is the weight-one datum they
carry; nothing here is claiming the spectrum is uninformative. -/
theorem meanGap_from_gaps : Spectrum.meanGap = Spectrum.gapSum / 11 := rfl


end SCD.Spacing
