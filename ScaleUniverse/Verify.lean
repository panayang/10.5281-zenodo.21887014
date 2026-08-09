/-
# Verification

Machine audit of the whole development.

`#print axioms` reports, for each theorem, the complete set of unproved
assumptions it ultimately rests on.  Every theorem below must report only

  `propext`, `Classical.choice`, `Quot.sound`

which are Lean's three standard logical axioms (they are what makes the
ambient logic classical set-theoretic mathematics).  Any occurrence of
`sorryAx` would mean an unfinished proof and would be reported here.

Note that `ScaleAlgebra`, `ScaleField` and the various physical hypotheses are
*not* Lean axioms.  They are typeclasses, structures and explicit hypotheses,
so they appear in the statements of the theorems rather than being smuggled in
behind them.  Nothing in this development postulates a physical result and
then calls it proved.
-/
import ScaleUniverse

namespace ScaleUniverse.Verify

/-! ## Sector I — emergence of geometry -/

-- Curvature is exactly the Kulkarni–Nomizu product of δ with scale deformation
#print axioms ScaleUniverse.two_Rm_eq
#print axioms ScaleUniverse.Ric_eq
#print axioms ScaleUniverse.RscBare_eq
#print axioms ScaleUniverse.Rm_eq_zero_of_Defm_eq_zero
#print axioms ScaleUniverse.Ric_eq_zero_of_Defm_eq_zero
#print axioms ScaleUniverse.two_Ric_eq

-- Integrable Weyl geometry: no second clock effect
#print axioms ScaleUniverse.scaleCurv_eq_zero

/-! ## Sector II — the axiom system -/

#print axioms ScaleUniverse.ScaleField.en_mul_scale
#print axioms ScaleUniverse.ScaleField.d_en
#print axioms ScaleUniverse.geometry_fiducial_invariant

/-! ## Sector III — the Newtonian limit -/

#print axioms ScaleUniverse.RscBare_linear
#print axioms ScaleUniverse.poisson
#print axioms ScaleUniverse.poisson_three
#print axioms ScaleUniverse.Dual.gradsq_inr
#print axioms ScaleUniverse.Dual.poisson_exact

/-! ## Sector IV — renormalisation group and the EFT tower -/

#print axioms ScaleUniverse.RG.callan_symanzik
#print axioms ScaleUniverse.RG.scale_invariant_of_fixedPoint
#print axioms ScaleUniverse.RG.ScaleFlow.observable_const_at_fixedPoint
#print axioms ScaleUniverse.RG.active_mono
#print axioms ScaleUniverse.RG.active_eq_of_no_threshold
#print axioms ScaleUniverse.RG.active_finite_range

/-! ## Sector V — particle scales -/

#print axioms ScaleUniverse.Particles.one_le_scaleRatio
#print axioms ScaleUniverse.Particles.lifetime_ge
#print axioms ScaleUniverse.Particles.lifetime_mono
#print axioms ScaleUniverse.Particles.lifetime_at_rest

/-! ## Sector VI — dark matter -/

#print axioms ScaleUniverse.Dark.detection_failure
#print axioms ScaleUniverse.Dark.dark_matter_exists
#print axioms ScaleUniverse.Dark.response_vanishes

/-! ## Sector VII — dark energy -/

#print axioms ScaleUniverse.Cosmology.dissipation_solution
#print axioms ScaleUniverse.Cosmology.energy_strictly_decreasing
#print axioms ScaleUniverse.Cosmology.scaleFactor_eq
#print axioms ScaleUniverse.Cosmology.hasDerivAt_scaleFactor
#print axioms ScaleUniverse.Cosmology.acceleration_pos
#print axioms ScaleUniverse.Cosmology.open_universe_accelerates

/-! ## Sector VIII — arrow of time -/

#print axioms ScaleUniverse.Entropy.entropy_nondecreasing
#print axioms ScaleUniverse.Entropy.no_reverse_law
#print axioms ScaleUniverse.Entropy.evolve_no_reverse_law
#print axioms ScaleUniverse.Entropy.entropy_production_implies_nonequilibrium

/-! ## Sector X — the non-commutative foundation and quantum mechanics -/

#print axioms ScaleUniverse.Quantum.ad_leibniz
#print axioms ScaleUniverse.Quantum.ad_jacobi
#print axioms ScaleUniverse.Quantum.ad_comm_of_commute
#print axioms ScaleUniverse.Quantum.ad_pow
#print axioms ScaleUniverse.Quantum.robertson
#print axioms ScaleUniverse.Quantum.heisenberg

/-! ## Sector XI — local covariance under dissipation -/

#print axioms ScaleUniverse.Covariance.CosmicHistory.Rm_eq
#print axioms ScaleUniverse.Covariance.CosmicHistory.field_equation_form_invariant
#print axioms ScaleUniverse.Covariance.CosmicHistory.no_local_expansion

/-! ## Sector XII — singularity resolution -/

#print axioms ScaleUniverse.Singularity.ScaleField.scale_ne_zero
#print axioms ScaleUniverse.Singularity.ScaleField.energy_ne_zero
#print axioms ScaleUniverse.Singularity.ScaleField.conformal_factor_isUnit
#print axioms ScaleUniverse.Singularity.curvature_indep_of_scale_value

/-! ## Sector XIII — testable predictions -/

#print axioms ScaleUniverse.Predictions.powerlaw_accel_numerator
#print axioms ScaleUniverse.Predictions.accelerates_iff
#print axioms ScaleUniverse.Predictions.eos_dissipationExponent
#print axioms ScaleUniverse.Predictions.eos_eq_neg_one_iff
#print axioms ScaleUniverse.Predictions.eos_lt_third_iff
#print axioms ScaleUniverse.Predictions.muon_matches_experiment
#print axioms ScaleUniverse.Predictions.poundRebka_value
#print axioms ScaleUniverse.Predictions.darkEnergyDensity_value
#print axioms ScaleUniverse.Predictions.logScale_ratio_const

/-! ## Sector XIV — A4 weakened: the directional scale -/

#print axioms ScaleUniverse.Frame.DirScale.reciprocal_metric
#print axioms ScaleUniverse.Frame.DirScale.isotropic_reciprocal_forces_flat
#print axioms ScaleUniverse.Frame.DirScale.isotropic_reciprocal_metric_bare
#print axioms ScaleUniverse.Frame.exists_reciprocal_nonisotropic

/-! ## Sector XV — the classical limit (deformation quantization) -/

#print axioms ScaleUniverse.Deformation.star_assoc
#print axioms ScaleUniverse.Deformation.star_classical
#print axioms ScaleUniverse.Deformation.star_commutator
#print axioms ScaleUniverse.Deformation.star_comm_iff_poisson_zero
#print axioms ScaleUniverse.Deformation.Biderivation.poisson_leibniz_left
#print axioms ScaleUniverse.Deformation.ccr_of_canonical

/-! ## Sector XVI — particles as scale defects -/

#print axioms ScaleUniverse.Defect.ScaleDefect.winding_unique
#print axioms ScaleUniverse.Defect.ScaleDefect.stable_of_winding_ne_zero
#print axioms ScaleUniverse.Defect.ScaleDefect.winding_eq_zero_of_trivial
#print axioms ScaleUniverse.Defect.ScaleDefect.pair_winding_zero
#print axioms ScaleUniverse.Defect.ScaleDefect.antiparticle_same_mass
#print axioms ScaleUniverse.Defect.ScaleDefect.mass_ratio_geometric
#print axioms ScaleUniverse.Defect.ScaleDefect.mass_ratio_const

/-! ## Sector XVII — axiom coherence: A4 is the isotropic locus of A4' -/

#print axioms ScaleUniverse.Unify.toMetric_of_isotropic
#print axioms ScaleUniverse.Unify.isotropic_iff_ofScalar
#print axioms ScaleUniverse.Unify.sector_coherence
#print axioms ScaleUniverse.Unify.not_isotropic_of_ne

/-! ## Sector XVIII — the strong sector -/

#print axioms ScaleUniverse.QCD.running_inv_sq
#print axioms ScaleUniverse.QCD.asymptotic_freedom
#print axioms ScaleUniverse.QCD.lambda_invariant
#print axioms ScaleUniverse.QCD.hadron_mass_ratio
#print axioms ScaleUniverse.QCD.geometric_tower_fails
#print axioms ScaleUniverse.QCD.lightestGlueballInLambda_value

/-! ## Sector XIX — curvature as a commutator (anisotropic sector) -/

#print axioms ScaleUniverse.Connection.comm_covD
#print axioms ScaleUniverse.Connection.bianchi
#print axioms ScaleUniverse.Connection.curv_of_central
#print axioms ScaleUniverse.Connection.curv_gradient_eq_zero
#print axioms ScaleUniverse.Connection.curv_split
#print axioms ScaleUniverse.Connection.curv_eq_rotation_part
#print axioms ScaleUniverse.Connection.curv_pure_scale_eq_zero
#print axioms ScaleUniverse.Connection.F_antisymm

/-! ## Sector XX — scale-native origin of the beta function -/

#print axioms ScaleUniverse.RG.beta_const_between_thresholds
#print axioms ScaleUniverse.RG.beta_finite_range
#print axioms ScaleUniverse.RG.beta_eq_of_all_active

/-! ## Sector XXI — non-commutativity, exactly (no ħ-expansion) -/

#print axioms ScaleUniverse.Crossed.shift_mul_eq
#print axioms ScaleUniverse.Crossed.commutator_eq
#print axioms ScaleUniverse.Crossed.comm_iff_shift_trivial
#print axioms ScaleUniverse.Crossed.delta_twisted_leibniz
#print axioms ScaleUniverse.Crossed.delta_leibniz_of_untwisted

/-! ## Sector XXII — internal symmetry as scale-pattern stabilizer -/

#print axioms ScaleUniverse.Gauge.stabilizer_eq_bot_of_injective
#print axioms ScaleUniverse.Gauge.stabilizer_eq_top_of_isotropic
#print axioms ScaleUniverse.Gauge.sameOrbit_iff_eq_scale
#print axioms ScaleUniverse.Gauge.internal_symmetry_determined

/-! ## Sector XXIII — running from counting, not loops -/

#print axioms ScaleUniverse.Running.hasDerivAt_invSqCoupling
#print axioms ScaleUniverse.Running.invSqCoupling_eq_one_loop
#print axioms ScaleUniverse.Running.asympt_free_iff_pos_density

/-! ## Sector XXIV — transport determined by the scale pattern -/

#print axioms ScaleUniverse.Transport.transport_unique_of_nondegenerate
#print axioms ScaleUniverse.Transport.transport_coset
#print axioms ScaleUniverse.Transport.transports_of_stabilizer
#print axioms ScaleUniverse.Transport.transport_unique_iff_stabilizer_trivial
#print axioms ScaleUniverse.Transport.nondegenerate_no_gauge_freedom

/-! ## Sector XXV — confinement and fractional charge -/

#print axioms ScaleUniverse.Color.BlockMonodromy.confinement
#print axioms ScaleUniverse.Color.BlockMonodromy.pair_observable
#print axioms ScaleUniverse.Color.BlockMonodromy.bound_state_size
#print axioms ScaleUniverse.Color.BlockMonodromy.no_partial_state
#print axioms ScaleUniverse.Color.BlockMonodromy.constituent_charge_fraction
#print axioms ScaleUniverse.Color.BlockMonodromy.constituent_charge_rat
#print axioms ScaleUniverse.Color.BlockMonodromy.bound_charge_divisible

/-! ## Sector XXVI — audit: light, redshift, and the observer -/

#print axioms ScaleUniverse.Observation.null_has_energy
#print axioms ScaleUniverse.Observation.redshift_is_scale_ratio
#print axioms ScaleUniverse.Observation.obsEnergy_rescale
#print axioms ScaleUniverse.Observation.redshift_fiducial_invariant
#print axioms ScaleUniverse.Observation.causal_structure_still_blind

/-! ## Sector XXVII — audit: the mass law is not determined by the topology -/

#print axioms ScaleUniverse.MassAudit.mass_law_underdetermined
#print axioms ScaleUniverse.MassAudit.both_laws_antiparticle_degenerate
#print axioms ScaleUniverse.MassAudit.massQuad_ratio_not_constant

/-! ## Sector IX — light -/

#print axioms ScaleUniverse.Light.isNull_iff_bare
#print axioms ScaleUniverse.Light.isNull_scale_invariant
#print axioms ScaleUniverse.Light.scale_determined_of_nonnull
#print axioms ScaleUniverse.Light.physForm_ne_bareForm
#print axioms ScaleUniverse.Light.null_weight_zero

end ScaleUniverse.Verify
