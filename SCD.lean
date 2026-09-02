/-
# SCD — Scale-Coupled Dynamics

A dimensionless axiomatisation in which the scale, not spacetime, is the
primitive.  Local energy-momentum *is* the local scale by A3; differences of
scale appear as curvature; and what exists at all is a slice across the scale
axis.

This file is the intended reading order.  It is not an accumulation: the
imports below follow the theory's own logic, and the two places where the
development branches are marked.  Read the postulates, then Part I in order,
then take the branch that interests you.

**Before relying on any result, read `SCD.Audit`** — the single register of what
has been retracted, corrected, cited without proof, and assumed.

────────────────────────────────────────────────────────────────────────
PART 0 — THE POSTULATES
────────────────────────────────────────────────────────────────────────

`SCD.Pattern` is the vocabulary the whole development is written in — isotropy,
parallelism, the wedge, and the two sector counts A7 compares.  Each of those
was previously written out three or four times in the vocabulary of whichever
file needed it, and reconnected afterwards by equivalence theorems; they are
stated once, so the reconnecting theorems are identities.

`SCD.Basic` is A1 itself: a ring with `n` commuting derivations.  Commutativity
of the ring is *not* part of the axiom, so `SCD.Conformal`'s objects and
`SCD.NCConformal`'s are the same objects and the classical curvature computation
is the commuting locus of the general one, not a separate development.

`SCD.Postulates` states A1–A7 in one place with the formal carrier and honest
status of each.

────────────────────────────────────────────────────────────────────────
PART I — WHAT THE AXIOMS FORCE  (a single chain, in order)
────────────────────────────────────────────────────────────────────────

    Foundation   the scale/rotation split is not a choice
    Signature    time is the direction the scale runs; 1 + (n−1)
    Invariant    the bookkeeping form is τ(xy), from a trace alone
    Direction    directions are the defining representation
    Connection   curvature is the commutator of transports; Bianchi
    Coupling     ★ two scalings bracket to a rotation — forced by the words
    Algebra      real rank one ⟹ the Lorentz family
    Dimension    n = k+1 is not independent; A7 ⟹ k = 3
    Axes         the pattern is ONE vector; more axes are unavailable

`Coupling` is the hinge.  Everything before it is about what a scale is;
everything after it follows from scalings failing to commute.

────────────────────────────────────────────────────────────────────────
PART II — THE BRANCH POINT
────────────────────────────────────────────────────────────────────────

`SCD.Locus` is where the theory divides, and the division is sharp:

    isotropic pattern    →  no order parameter, no charge, no multiplet,
                            no rotation.  Nothing is labelled.
    anisotropic pattern  →  the order parameter appears, and the charges,
                            multiplets and curvature appear with it — all at
                            once, because they have one source.

Whether a pattern is isotropic is a **scale-dependent** fact.  That is why the
labels are not scale-invariant properties despite being homotopy invariants,
and it is the framework's derivation of "the interactions separate as the
energy scale falls".

  II.a  THE ISOTROPIC SECTOR — geometry and gravity
        Conformal, Frame, Unify, Newton, Schwarzschild, RicciDiag, Vacuum,
        Deflection, PPN, Precession, Covariance, Singularity, Horizon
        The quantitative chain: metric → connection → Ricci → cancellation →
        stationary scale sum → asymptotic flatness → s_t·s_r = 1 → γ = 1 →
        1.7515″ and 42.99″/century, with no assumption in between.

  II.b  THE ANISOTROPIC SECTOR — labels and charges
        Gauge, Transport, Axis, Defect, Charges, Particle, Emergence
        A particle is (threshold, ℤ/2, ℤ) and nothing else.

────────────────────────────────────────────────────────────────────────
PART III — THE QUANTUM SECTOR
────────────────────────────────────────────────────────────────────────

    Quantum      commutators give Leibniz, Jacobi, the power rule, Heisenberg
    Deformation  the first-order star product, and its limit
    Crossed      exact non-commutativity from a scale shift — ħ is a step
    NCConformal  ★ curvature without commutativity; the whole quantum
                 correction is [σᵢ, σⱼ], and it is purely antisymmetric
    Dynamics     conservation is the condition for a field equation to exist
    Ordering     ★ the lift of the gravity chain's cancellation to a
                 non-commutative ring is *not* unique — and the static
                 configuration the chain runs in does not notice
    Screen       predictions of the world survive the observer joining the
                 configuration; what is *recorded* does not — and that is where
                 the one discriminating prediction lives
    ExpPoly      ★ the first configuration: `e^p` is a unit, so the scale can
                 vary — A2 and A4′ acquire terms, and reciprocity holds at
                 finite amplitude

    Circle       and the other branch: a scale whose gradient has no potential.
                 A periodic scale field is a contradiction in terms, so the join
                 keeps the gradient and drops the potential

────────────────────────────────────────────────────────────────────────
PART IV — SCALE FLOW AND CONTENT
────────────────────────────────────────────────────────────────────────

    RG, Running, Slice, Spectrum, Entropy, Light, Observation, Particles,
    DarkMatter, DarkEnergy, QCD, Color, Codimension, Expressive, Deformation

    Content is a slice; label proliferation measures range, not depth; the
    threshold density is measured, not predicted.

────────────────────────────────────────────────────────────────────────
PART V — PREDICTIONS, AND THE DATA
────────────────────────────────────────────────────────────────────────

    Predictions  the conversion table
    Cosmos       w on its stated domain; there is no initial value; dark matter
    Horizon      no horizon; waves on the light cone; entropy ∝ ln R
    Waves        inspiral dynamics: conservation kills monopole and dipole,
                 so the quadrupole leads; Hulse–Taylor bounds the dipole
    Native       the seven questions only this framework can ask
    Data         ★ the confrontation.  A5 does **not** forbid an evolving w —
                 that reading was withdrawn in `Scanning` — and the framework's
                 own w(z) has never been computed, so DESI compares against
                 nothing yet.  One live open question (the f₀(500) pole).

────────────────────────────────────────────────────────────────────────
PART VI — THE REGISTER
────────────────────────────────────────────────────────────────────────

    Audit        retracted, corrected, cited, assumed — read this first
    MassAudit, ColorAudit, CrossCheck   the individual retractions

`SCD.Verify` sits above this root and is not imported by it: it imports `SCD`
and puts every principal theorem through `#print axioms`.  Build it to check
the development, not to use it.

────────────────────────────────────────────────────────────────────────

**The one free number.**  Every prediction is a ratio.  The overall magnitude of
the scale pattern is not predicted and cannot be — it is the unit the
predictions are expressed in, and a dimensionless theory must carry exactly one.
-/

-- Part 0 — the postulates
import SCD.Pattern
import SCD.Basic
import SCD.Axioms
import SCD.Postulates

-- Part I — what the axioms force
import SCD.Foundation
import SCD.Signature
import SCD.Invariant
import SCD.Quantum
import SCD.Direction
import SCD.Connection
import SCD.Coupling
import SCD.Algebra
import SCD.Dimension
import SCD.Slice
import SCD.Axes

-- Part II — the branch point
import SCD.Locus

-- Part II.a — the isotropic sector: geometry and gravity
import SCD.Conformal
import SCD.Frame
import SCD.Unify
import SCD.Newton
import SCD.Diagonal
import SCD.Schwarzschild
import SCD.RicciDiag
import SCD.Vacuum
import SCD.Reciprocity
import SCD.Chain
import SCD.Deflection
import SCD.PPN
import SCD.Precession
import SCD.Nonlinearity
import SCD.Covariance
import SCD.Singularity
import SCD.Horizon
import SCD.Waves

-- Part II.b — the anisotropic sector: labels and charges
import SCD.Gauge
import SCD.Transport
import SCD.Axis
import SCD.Defect
import SCD.Charges
import SCD.Particle
import SCD.Emergence

-- Part III — the quantum sector
import SCD.Deformation
import SCD.Crossed
import SCD.Dual
import SCD.NCConformal
import SCD.Anisotropic
import SCD.Dynamics
import SCD.Determination
import SCD.Explanation
import SCD.Anchor
import SCD.Observer
import SCD.Observed
import SCD.Internal
import SCD.Triple
import SCD.Mutual
import SCD.NCSize
import SCD.Ordering
import SCD.Screen
import SCD.ExpPoly
import SCD.Circle

-- Part IV — scale flow and content
import SCD.RG
import SCD.Running
import SCD.Spectrum
import SCD.Period
import SCD.Sources
import SCD.Weight
import SCD.Entropy
import SCD.Light
import SCD.Observation
import SCD.Positivity
import SCD.Well
import SCD.Momentum
import SCD.Openness
import SCD.Index
import SCD.Flux
import SCD.Particles
import SCD.DarkMatter
import SCD.DarkEnergy
import SCD.QCD
import SCD.Color
import SCD.Codimension
import SCD.Expressive

-- Part V — predictions and data
import SCD.Predictions
import SCD.Cosmos
import SCD.Scanning
import SCD.Response
import SCD.Attraction
import SCD.Native
import SCD.Data

-- Part VI — the register
import SCD.MassAudit
import SCD.ColorAudit
import SCD.CrossCheck
import SCD.Witness
import SCD.Audit
