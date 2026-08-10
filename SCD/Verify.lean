/-
# Verification — every theorem, through `#print axioms`

Not part of the library: `SCD.lean` does not import it.  It imports `SCD` and
puts **every** theorem in the development through `#print axioms`, in the
reading order of the root file.

The list is generated from the sources, not curated, so nothing can quietly
fall out of the audit.  A clean run prints only `propext`, `Classical.choice`
and `Quot.sound`, and never `sorryAx`.
-/
import SCD

namespace SCD.Verify


/-! ## PART 0 — the postulates -/


-- Basic.lean
#print axioms SCD.ScaleAlgebra.d_zero
#print axioms SCD.ScaleAlgebra.d_one
#print axioms SCD.ScaleAlgebra.d_neg
#print axioms SCD.ScaleAlgebra.d_sub
#print axioms SCD.ScaleAlgebra.d_sum
#print axioms SCD.ScaleAlgebra.d_natCast
#print axioms SCD.ScaleAlgebra.d_nsmul
#print axioms SCD.kron_self
#print axioms SCD.kron_symm
#print axioms SCD.d_kron
#print axioms SCD.d_kron_mul
#print axioms SCD.sum_kron_left
#print axioms SCD.sum_kron_right

-- Axioms.lean
#print axioms SCD.ScaleField.en_mul_scale
#print axioms SCD.ScaleField.scale_mul_en
#print axioms SCD.ScaleField.d_en
#print axioms SCD.sig_add_const
#print axioms SCD.hess_add_const
#print axioms SCD.lap_add_const
#print axioms SCD.gradsq_add_const
#print axioms SCD.Chr_add_const
#print axioms SCD.Rm_add_const
#print axioms SCD.Ric_add_const
#print axioms SCD.Defm_add_const
#print axioms SCD.geometry_fiducial_invariant
#print axioms SCD.sig_neg
#print axioms SCD.hess_neg
#print axioms SCD.lap_neg
#print axioms SCD.gradsq_neg

-- Postulates.lean
#print axioms SCD.Postulates.scaleAlgebra_is_diffRing_d
#print axioms SCD.Postulates.three_from_A7
#print axioms SCD.Postulates.A7_holds_only_at_three

/-! ## PART I — what the axioms force -/


-- Foundation.lean
#print axioms SCD.Foundation.scale_mul
#print axioms SCD.Foundation.scale_comm
#print axioms SCD.Foundation.scale_inv
#print axioms SCD.Foundation.scale_commutator
#print axioms SCD.Foundation.curvature_is_scale_invisible
#print axioms SCD.Foundation.scale_eq_one_of_mem_commutator
#print axioms SCD.Foundation.mem_commutator_of_scale_eq_one
#print axioms SCD.Foundation.scale_eq_iff_differ_by_rotation
#print axioms SCD.Foundation.commutator_eq_one_of_comm
#print axioms SCD.Foundation.comm_of_scale_injective

-- Signature.lean
#print axioms SCD.Signature.codim_ker_eq_one
#print axioms SCD.Signature.no_time_of_no_drift
#print axioms SCD.Signature.spatial_eq_top_of_no_drift
#print axioms SCD.Signature.spatial_ne_top_of_drift
#print axioms SCD.Signature.drift_direction_unique
#print axioms SCD.Signature.spatial_smul
#print axioms SCD.Signature.signature_from_dissipation

-- Invariant.lean
#print axioms SCD.Invariant.Trace.map_zero
#print axioms SCD.Invariant.Trace.map_sub
#print axioms SCD.Invariant.Trace.form_symm
#print axioms SCD.Invariant.Trace.form_invariant
#print axioms SCD.Invariant.Trace.form_ad_skew
#print axioms SCD.Invariant.Trace.form_commutator_self

-- Quantum.lean
#print axioms SCD.Quantum.ad_zero_left
#print axioms SCD.Quantum.ad_leibniz
#print axioms SCD.Quantum.ad_jacobi
#print axioms SCD.Quantum.ad_comm_of_commute
#print axioms SCD.Quantum.ad_pow
#print axioms SCD.Quantum.robertson
#print axioms SCD.Quantum.heisenberg

-- Direction.lean
#print axioms SCD.Direction.DirTransport.D_zero_dir
#print axioms SCD.Direction.DirTransport.D_neg_dir
#print axioms SCD.Direction.DirTransport.curv_self
#print axioms SCD.Direction.DirTransport.curv_antisymm
#print axioms SCD.Direction.DirTransport.flat_iff_lie_hom
#print axioms SCD.Direction.DirTransport.curv_of_abelian
#print axioms SCD.Direction.DirTransport.commute_iff_bracket_acts_trivially
#print axioms SCD.Direction.DirTransport.transport_determined_by_generators

-- Connection.lean
#print axioms SCD.Connection.DiffRing.D_sub
#print axioms SCD.Connection.F_antisymm
#print axioms SCD.Connection.comm_covD
#print axioms SCD.Connection.bianchi
#print axioms SCD.Connection.curv_of_central
#print axioms SCD.Connection.curv_gradient_eq_zero
#print axioms SCD.Connection.curv_split
#print axioms SCD.Connection.curv_eq_rotation_part
#print axioms SCD.Connection.curv_pure_scale_eq_zero

-- Coupling.lean
#print axioms SCD.Coupling.bracket_scaling_scaling
#print axioms SCD.Coupling.bracket_rotation_scaling
#print axioms SCD.Coupling.bracket_rotation_rotation
#print axioms SCD.Coupling.coupling_structure
#print axioms SCD.Coupling.bracket_self
#print axioms SCD.Coupling.no_rotation_of_commuting
#print axioms SCD.Coupling.boost_bracket_eq_rotation
#print axioms SCD.Coupling.scalings_do_not_commute

-- Algebra.lean
#print axioms SCD.Algebra.scaling_rotation_orthogonal
#print axioms SCD.Algebra.boost_zero_zero
#print axioms SCD.Algebra.boost_zero_succ
#print axioms SCD.Algebra.boost_succ_zero
#print axioms SCD.Algebra.boost_succ_succ
#print axioms SCD.Algebra.boost_isScaling
#print axioms SCD.Algebra.boost_add
#print axioms SCD.Algebra.boost_smul
#print axioms SCD.Algebra.boost_mul_succ_succ
#print axioms SCD.Algebra.boost_bracket_spatial
#print axioms SCD.Algebra.boosts_commute_iff_parallel
#print axioms SCD.Algebra.commuting_boosts_lie_on_a_line
#print axioms SCD.Algebra.commuting_family_one_parameter
#print axioms SCD.Algebra.no_two_dimensional_commuting_family
#print axioms SCD.Algebra.boost_drift
#print axioms SCD.Algebra.commuting_drifts_proportional
#print axioms SCD.Algebra.boost_spatial_block_zero
#print axioms SCD.Algebra.boost_eq_zero_iff

-- Dimension.lean
#print axioms SCD.Dimension.algebra_bigger_than_directions
#print axioms SCD.Dimension.rep_dim_determined
#print axioms SCD.Dimension.rot_matches_scale_iff
#print axioms SCD.Dimension.alg_matches_rep_iff
#print axioms SCD.Dimension.two_matching_conditions_differ
#print axioms SCD.Dimension.wedge_smul_both
#print axioms SCD.Dimension.wedge_ratio_invariant
#print axioms SCD.Dimension.only_ratios_are_fixed
#print axioms SCD.Dimension.density_normalization_relation
#print axioms SCD.Dimension.normalization_returns_input

-- Slice.lean
#print axioms SCD.Slice.mem_newContent
#print axioms SCD.Slice.newContent_nonempty_of_threshold
#print axioms SCD.Slice.newContent_mono
#print axioms SCD.Slice.newContent_empty_of_no_threshold
#print axioms SCD.Slice.no_finite_universal_labelling
#print axioms SCD.Slice.label_count_measures_range
#print axioms SCD.Slice.wedge_eq_bracket
#print axioms SCD.Slice.wedge_antisymm
#print axioms SCD.Slice.wedge_bilinear_left
#print axioms SCD.Slice.wedge_eq_zero_iff_parallel
#print axioms SCD.Slice.homogeneous_carries_no_rotation
#print axioms SCD.Slice.rotation_requires_biaxial
#print axioms SCD.Slice.wedge_dim_eq_iff
#print axioms SCD.Slice.three_is_unique
#print axioms SCD.Slice.more_wedges_than_directions
#print axioms SCD.Slice.fewer_wedges_than_directions

-- Axes.lean
#print axioms SCD.Axes.rotation_needs_variation
#print axioms SCD.Axes.combable_no_rotation
#print axioms SCD.Axes.wound_carries_rotation
#print axioms SCD.Axes.rotationless_is_trivial
#print axioms SCD.Axes.rotation_iff_variation
#print axioms SCD.Axes.no_second_axis
#print axioms SCD.Axes.axis_or_variation
#print axioms SCD.Axes.axis_stabilizer_nontrivial
#print axioms SCD.Axes.multiplet_flatness_needs_per_direction_scalings

/-! ## PART II — the branch point -/


-- Locus.lean
#print axioms SCD.Locus.observability_eq_postulate
#print axioms SCD.Locus.three_from_observability
#print axioms SCD.Locus.observability_fails_elsewhere
#print axioms SCD.Locus.observability_iff_three
#print axioms SCD.Locus.no_scale_invariant_interaction
#print axioms SCD.Locus.constant_coupling_iff_no_content
#print axioms SCD.Locus.isotropic_pair_parallel
#print axioms SCD.Locus.isotropic_no_rotation
#print axioms SCD.Locus.labels_require_anisotropy
#print axioms SCD.Locus.everything_switches_on_together
#print axioms SCD.Locus.particle_locus_is_anisotropic

-- Dynamics.lean
#print axioms SCD.Dynamics.no_flatness_from_commuting_derivations
#print axioms SCD.Dynamics.nonflat_witness
#print axioms SCD.Dynamics.commutative_sector_transports_commute
#print axioms SCD.Dynamics.commutative_curvature_undetectable
#print axioms SCD.Dynamics.source_conserved_of_field_equation
#print axioms SCD.Dynamics.no_field_equation_of_nonconserved
#print axioms SCD.Dynamics.source_antisymm
#print axioms SCD.Dynamics.field_equation_content
#print axioms SCD.Dynamics.same_multiplet_no_rotation
#print axioms SCD.Dynamics.rotation_implies_different_multiplet
#print axioms SCD.Dynamics.larger_multiplet_fewer_generators
#print axioms SCD.Dynamics.multiplets_fixed_by_pattern
#print axioms SCD.Dynamics.multiplet_change_needs_pattern_change

/-! ## PART II.a — the isotropic sector -/


-- Conformal.lean
#print axioms SCD.hess_symm
#print axioms SCD.d_sig_comm
#print axioms SCD.sum_mul_gradsq
#print axioms SCD.sum_const_fin
#print axioms SCD.scaleCurv_eq_zero
#print axioms SCD.Chr_symm
#print axioms SCD.sum_d_Chr
#print axioms SCD.sum_Chr_diag
#print axioms SCD.sum_d_Chr_trace
#print axioms SCD.sum_ChrTrace_Chr
#print axioms SCD.sum_Chr_Chr_full
#print axioms SCD.sum_Chr_Chr
#print axioms SCD.Ric_eq
#print axioms SCD.RscBare_eq
#print axioms SCD.Defm_symm
#print axioms SCD.d_Chr_diff
#print axioms SCD.two_Rm_eq
#print axioms SCD.Rm_eq_zero_of_Defm_eq_zero
#print axioms SCD.Ric_eq_zero_of_Defm_eq_zero
#print axioms SCD.two_Ric_eq

-- Frame.lean
#print axioms SCD.Frame.DirScale.isotropic_metric
#print axioms SCD.Frame.DirScale.reciprocal_metric
#print axioms SCD.Frame.DirScale.isotropic_reciprocal_forces_flat
#print axioms SCD.Frame.DirScale.isotropic_reciprocal_metric_bare
#print axioms SCD.Frame.exists_reciprocal_nonisotropic

-- Unify.lean
#print axioms SCD.Unify.toMetric_of_isotropic
#print axioms SCD.Unify.ofScalar_isotropic
#print axioms SCD.Unify.ofScalar_toMetric
#print axioms SCD.Unify.isotropic_iff_ofScalar
#print axioms SCD.Unify.toDirScale_isotropic
#print axioms SCD.Unify.toDirScale_toMetric
#print axioms SCD.Unify.sector_coherence
#print axioms SCD.Unify.isotropic_ratio_const
#print axioms SCD.Unify.not_isotropic_of_ne

-- Newton.lean
#print axioms SCD.lap_newtPot
#print axioms SCD.RscBare_linear
#print axioms SCD.poisson
#print axioms SCD.poisson_three
#print axioms SCD.Dual.sig_inr
#print axioms SCD.Dual.gradsq_inr
#print axioms SCD.Dual.poisson_exact

-- Schwarzschild.lean
#print axioms SCD.Schwarzschild.ricci_combination
#print axioms SCD.Schwarzschild.vacuum_log_derivative
#print axioms SCD.Schwarzschild.scale_sum_derivative_zero
#print axioms SCD.Schwarzschild.vacuum_iff_scale_sum_stationary
#print axioms SCD.Schwarzschild.area_element_stationary

-- RicciDiag.lean
#print axioms SCD.RicciDiag.ricciTT_eq
#print axioms SCD.RicciDiag.ricciRR_eq
#print axioms SCD.RicciDiag.gravity_chain
#print axioms SCD.RicciDiag.area_stationary_derived

-- Vacuum.lean
#print axioms SCD.Vacuum.const_of_deriv_zero_and_vanishing
#print axioms SCD.Vacuum.reciprocity_of_asymptotic_flatness
#print axioms SCD.Vacuum.scale_product_eq_one
#print axioms SCD.Vacuum.product_constant_without_flatness
#print axioms SCD.Vacuum.tr_area_element_constant

-- Deflection.lean
#print axioms SCD.Deflection.iso_is_exactly_half
#print axioms SCD.Deflection.iso_ratio_half
#print axioms SCD.Deflection.missing_half
#print axioms SCD.Deflection.solarObs_value
#print axioms SCD.Deflection.solarIso_value
#print axioms SCD.Deflection.solar_ratio
#print axioms SCD.Deflection.iso_fails_by_far

-- PPN.lean
#print axioms SCD.PPN.gamma_zero_is_isotropic
#print axioms SCD.PPN.gamma_one_is_observed
#print axioms SCD.PPN.reciprocal_expansion
#print axioms SCD.PPN.gamma_eq_one_of_reciprocal
#print axioms SCD.PPN.gamma_eq_one_first_order
#print axioms SCD.PPN.deflection_reciprocal_eq_observed
#print axioms SCD.PPN.halves_equal
#print axioms SCD.PPN.solar_reciprocal_value
#print axioms SCD.PPN.gamma_prediction_is_sharp

-- Precession.lean
#print axioms SCD.Precession.coeff_reciprocal
#print axioms SCD.Precession.coeff_isotropic
#print axioms SCD.Precession.isotropic_is_third
#print axioms SCD.Precession.coeff_affine_in_gamma
#print axioms SCD.Precession.mercuryFactor_bounds
#print axioms SCD.Precession.mercury_value
#print axioms SCD.Precession.mercury_isotropic_value
#print axioms SCD.Precession.two_tests_different_factors

-- Covariance.lean
#print axioms SCD.Covariance.CosmicHistory.sig_eq
#print axioms SCD.Covariance.CosmicHistory.Chr_eq
#print axioms SCD.Covariance.CosmicHistory.Rm_eq
#print axioms SCD.Covariance.CosmicHistory.Ric_eq_of_drift
#print axioms SCD.Covariance.CosmicHistory.Defm_eq
#print axioms SCD.Covariance.CosmicHistory.field_equation_form_invariant
#print axioms SCD.Covariance.CosmicHistory.no_local_expansion

-- Singularity.lean
#print axioms SCD.Singularity.ScaleField.scale_ne_zero
#print axioms SCD.Singularity.ScaleField.energy_ne_zero
#print axioms SCD.Singularity.ScaleField.conformal_factor_isUnit
#print axioms SCD.Singularity.ScaleField.conformal_factor_invertible
#print axioms SCD.Singularity.curvature_indep_of_scale_value
#print axioms SCD.Singularity.curvature_zero_of_uniform_scale

-- Horizon.lean
#print axioms SCD.Horizon.gtt_ne_zero
#print axioms SCD.Horizon.reciprocal_never_degenerate
#print axioms SCD.Horizon.redshift_never_infinite
#print axioms SCD.Horizon.no_degeneracy_anywhere
#print axioms SCD.Horizon.null_cone_scale_independent
#print axioms SCD.Horizon.waves_travel_on_the_light_cone
#print axioms SCD.Horizon.no_energy_dependent_speed
#print axioms SCD.Horizon.two_polarizations
#print axioms SCD.Horizon.no_breathing_mode
#print axioms SCD.Horizon.polarization_count
#print axioms SCD.Horizon.entropy_of_scale_ratio
#print axioms SCD.Horizon.entropy_doubling_is_additive
#print axioms SCD.Horizon.entropy_increment_independent_of_size
#print axioms SCD.Horizon.no_minimum_length
#print axioms SCD.Horizon.no_final_description

/-! ## PART II.b — the anisotropic sector -/


-- Gauge.lean
#print axioms SCD.Gauge.mem_stabilizer_iff
#print axioms SCD.Gauge.stabilizer_eq_bot_of_injective
#print axioms SCD.Gauge.stabilizer_eq_top_of_isotropic
#print axioms SCD.Gauge.sameOrbit_iff_eq_scale
#print axioms SCD.Gauge.internal_symmetry_determined

-- Transport.lean
#print axioms SCD.Transport.transports_self_iff
#print axioms SCD.Transport.transport_unique_of_nondegenerate
#print axioms SCD.Transport.transport_coset
#print axioms SCD.Transport.transports_of_stabilizer
#print axioms SCD.Transport.transport_unique_iff_stabilizer_trivial
#print axioms SCD.Transport.nondegenerate_no_gauge_freedom

-- Axis.lean
#print axioms SCD.Axis.bareForm_neg
#print axioms SCD.Axis.physForm_neg
#print axioms SCD.Axis.neg_indistinguishable
#print axioms SCD.Axis.physForm_indistinguishable
#print axioms SCD.Axis.isotropic_no_order_parameter
#print axioms SCD.Axis.nondegenerate_full_frame
#print axioms SCD.Axis.uniaxial_stabilizer
#print axioms SCD.Axis.uniaxial_axis_distinguished
#print axioms SCD.Axis.scalar_picture_is_the_isotropic_locus

-- Defect.lean
#print axioms SCD.Defect.ScaleDefect.winding_unique
#print axioms SCD.Defect.ScaleDefect.vacuum_winding
#print axioms SCD.Defect.ScaleDefect.combine_winding
#print axioms SCD.Defect.ScaleDefect.anti_winding
#print axioms SCD.Defect.ScaleDefect.pair_winding_zero
#print axioms SCD.Defect.ScaleDefect.vacuum_isTrivial
#print axioms SCD.Defect.ScaleDefect.stable_of_winding_ne_zero
#print axioms SCD.Defect.ScaleDefect.winding_eq_zero_of_trivial
#print axioms SCD.Defect.ScaleDefect.mass_pos
#print axioms SCD.Defect.ScaleDefect.antiparticle_same_mass
#print axioms SCD.Defect.ScaleDefect.mass_zero
#print axioms SCD.Defect.ScaleDefect.mass_ratio_geometric
#print axioms SCD.Defect.ScaleDefect.mass_ratio_const

-- Charges.lean
#print axioms SCD.Charges.DefectCharge.comp_block
#print axioms SCD.Charges.DefectCharge.comp_hedgehog
#print axioms SCD.Charges.DefectCharge.anti_block
#print axioms SCD.Charges.DefectCharge.anti_hedgehog
#print axioms SCD.Charges.DefectCharge.triv_observable
#print axioms SCD.Charges.DefectCharge.block_confined
#print axioms SCD.Charges.DefectCharge.hedgehog_free
#print axioms SCD.Charges.DefectCharge.hedgehog_surjective_on_observables
#print axioms SCD.Charges.DefectCharge.exactly_one_confined
#print axioms SCD.Charges.DefectCharge.hedgehog_not_determined_by_block
#print axioms SCD.Charges.DefectCharge.block_not_determined_by_hedgehog
#print axioms SCD.Charges.DefectCharge.charges_independent
#print axioms SCD.Charges.DefectCharge.pair_observable
#print axioms SCD.Charges.DefectCharge.pair_hedgehog_zero
#print axioms SCD.Charges.DefectCharge.observable_pair_any_hedgehog

-- Particle.lean
#print axioms SCD.Particle.boost_injective
#print axioms SCD.Particle.pattern_is_one_vector
#print axioms SCD.Particle.mixture_second_moment
#print axioms SCD.Particle.mixture_cvSq_ge_one
#print axioms SCD.Particle.mixture_cvSq_eq_one_iff
#print axioms SCD.Particle.observed_disfavours_higher_rank
#print axioms SCD.Particle.rate_value_not_fixed
#print axioms SCD.Particle.block_two_valued
#print axioms SCD.Particle.block_cannot_be_three_valued
#print axioms SCD.Particle.block_self_inverse
#print axioms SCD.Particle.bind_hedgehog
#print axioms SCD.Particle.bind_block
#print axioms SCD.Particle.two_odd_make_even
#print axioms SCD.Particle.hedgehog_conserved_in_splitting
#print axioms SCD.Particle.no_further_label
#print axioms SCD.Particle.particle_label_structure

-- Emergence.lean
#print axioms SCD.Emergence.mem_resolved
#print axioms SCD.Emergence.resolved_mono
#print axioms SCD.Emergence.content_never_complete
#print axioms SCD.Emergence.always_more_above
#print axioms SCD.Emergence.no_fundamental_list
#print axioms SCD.Emergence.mass_iff_threshold
#print axioms SCD.Emergence.mass_mono
#print axioms SCD.Emergence.content_eq_of_no_threshold
#print axioms SCD.Emergence.content_changes_only_at_threshold

/-! ## PART III — the quantum sector -/


-- Deformation.lean
#print axioms SCD.Deformation.Biderivation.poisson_antisymm
#print axioms SCD.Deformation.Biderivation.poisson_self
#print axioms SCD.Deformation.Biderivation.poisson_leibniz_left
#print axioms SCD.Deformation.Biderivation.poisson_leibniz_right
#print axioms SCD.Deformation.star_assoc
#print axioms SCD.Deformation.star_classical
#print axioms SCD.Deformation.star_comm_classical
#print axioms SCD.Deformation.star_commutator
#print axioms SCD.Deformation.star_comm_iff_poisson_zero
#print axioms SCD.Deformation.canonical_poisson
#print axioms SCD.Deformation.ccr_of_canonical
#print axioms SCD.Deformation.canonical_poisson_self

-- Crossed.lean
#print axioms SCD.Crossed.ScaleShift.map_zero
#print axioms SCD.Crossed.ScaleShift.shiftOp_apply
#print axioms SCD.Crossed.mulOp_apply
#print axioms SCD.Crossed.shift_mul_eq
#print axioms SCD.Crossed.commutator_eq
#print axioms SCD.Crossed.comm_iff_shift_trivial
#print axioms SCD.Crossed.delta_twisted_leibniz
#print axioms SCD.Crossed.delta_leibniz_of_untwisted
#print axioms SCD.Crossed.delta_eq_zero_iff
#print axioms SCD.Crossed.ScaleShift
#print axioms SCD.Crossed.shift_mul_eq_comp

-- NCConformal.lean
#print axioms SCD.NCConformal.kr_symm
#print axioms SCD.NCConformal.kr_comm
#print axioms SCD.NCConformal.kr_self
#print axioms SCD.NCConformal.sum_kr_left
#print axioms SCD.NCConformal.sum_kr_right
#print axioms SCD.NCConformal.kr_swap
#print axioms SCD.NCConformal.scalar_mul_scalar
#print axioms SCD.NCConformal.hess_symm
#print axioms SCD.NCConformal.Chr_symm
#print axioms SCD.NCConformal.Defm_antisymm_part
#print axioms SCD.NCConformal.Defm_symm_iff_commutator
#print axioms SCD.NCConformal.Defm_symm_iff_commute
#print axioms SCD.NCConformal.symmetric_part_uncorrected
#print axioms SCD.NCConformal.correction_is_pure_antisymmetric
#print axioms SCD.NCConformal.sum_Chr_Chr_full_nc
#print axioms SCD.NCConformal.sum_Chr_Chr_full_classical
#print axioms SCD.NCConformal.quantum_correction_couples_to_rotation
#print axioms SCD.NCConformal.correction_vanishes_on_commuting

/-! ## PART IV — scale flow and content -/


-- RG.lean
#print axioms SCD.RG.ScaleFlow.observable_const_at_fixedPoint
#print axioms SCD.RG.ScaleFlow.fixedPoint_invariant
#print axioms SCD.RG.callan_symanzik
#print axioms SCD.RG.scale_invariant_of_fixedPoint
#print axioms SCD.RG.mem_active
#print axioms SCD.RG.active_mono
#print axioms SCD.RG.active_eq_of_no_threshold
#print axioms SCD.RG.active_finite_range
#print axioms SCD.RG.active_eq_univ_of_ge
#print axioms SCD.RG.active_eq_empty_of_lt
#print axioms SCD.RG.beta_const_between_thresholds
#print axioms SCD.RG.beta_finite_range
#print axioms SCD.RG.beta_eq_of_all_active

-- Running.lean
#print axioms SCD.Running.resolvedCount_self
#print axioms SCD.Running.invSqCoupling_at_base
#print axioms SCD.Running.hasDerivAt_invSqCoupling
#print axioms SCD.Running.slope_eq_two_b
#print axioms SCD.Running.invSqCoupling_eq_one_loop
#print axioms SCD.Running.asympt_free_iff_pos_density

-- QCD.lean
#print axioms SCD.QCD.running_inv_sq
#print axioms SCD.QCD.asymptotic_freedom
#print axioms SCD.QCD.lambda_invariant
#print axioms SCD.QCD.lambda_pos
#print axioms SCD.QCD.hadron_mass_ratio
#print axioms SCD.QCD.spectrum_rigid
#print axioms SCD.QCD.geometric_tower_fails
#print axioms SCD.QCD.ratio₁_value
#print axioms SCD.QCD.ratio₂_value
#print axioms SCD.QCD.lightestGlueballInLambda_value

-- Spectrum.lean
#print axioms SCD.Spectrum.mass_threshold_inverse
#print axioms SCD.Spectrum.equal_gaps_variance_zero
#print axioms SCD.Spectrum.observed_cvSq_value
#print axioms SCD.Spectrum.meanGap_value
#print axioms SCD.Spectrum.observed_not_geometric
#print axioms SCD.Spectrum.observed_within_scale_invariant_range
#print axioms SCD.Spectrum.densityFromGaps_value
#print axioms SCD.Spectrum.deltaN_inverse
#print axioms SCD.Spectrum.density_gap_inverse

-- Entropy.lean
#print axioms SCD.Entropy.mem_sat
#print axioms SCD.Entropy.subset_sat
#print axioms SCD.Entropy.card_le_card_sat
#print axioms SCD.Entropy.card_image_perm
#print axioms SCD.Entropy.entropy_nondecreasing
#print axioms SCD.Entropy.no_reverse_law
#print axioms SCD.Entropy.evolve_no_reverse_law
#print axioms SCD.Entropy.charge_change_implies_nonequilibrium
#print axioms SCD.Entropy.entropy_production_implies_nonequilibrium

-- Light.lean
#print axioms SCD.Light.unit_sq_mul_eq_zero_iff
#print axioms SCD.Light.isNull_iff_bare
#print axioms SCD.Light.isNull_scale_invariant
#print axioms SCD.Light.scale_determined_of_nonnull
#print axioms SCD.Light.physForm_ne_bareForm
#print axioms SCD.Light.null_weight_zero

-- Observation.lean
#print axioms SCD.Observation.null_has_energy
#print axioms SCD.Observation.redshift_is_scale_ratio
#print axioms SCD.Observation.no_redshift_of_equal_scale
#print axioms SCD.Observation.obsEnergy_rescale
#print axioms SCD.Observation.redshift_fiducial_invariant
#print axioms SCD.Observation.causal_structure_still_blind

-- Particles.lean
#print axioms SCD.Particles.energy_pos
#print axioms SCD.Particles.energy_ge
#print axioms SCD.Particles.one_le_scaleRatio
#print axioms SCD.Particles.scaleRatio_mono
#print axioms SCD.Particles.lifetime_ge
#print axioms SCD.Particles.lifetime_mono
#print axioms SCD.Particles.lifetime_at_rest
#print axioms SCD.Particles.available_mono
#print axioms SCD.Particles.not_available_of_lt

-- DarkMatter.lean
#print axioms SCD.Dark.detResp_pos
#print axioms SCD.Dark.detection_failure
#print axioms SCD.Dark.dark_matter_exists
#print axioms SCD.Dark.response_vanishes

-- DarkEnergy.lean
#print axioms SCD.Cosmology.hasDerivAt_exp_mul
#print axioms SCD.Cosmology.dissipation_solution
#print axioms SCD.Cosmology.energy_strictly_decreasing
#print axioms SCD.Cosmology.scaleFactor_eq
#print axioms SCD.Cosmology.hasDerivAt_scaleFactor
#print axioms SCD.Cosmology.hasDerivAt_hubble
#print axioms SCD.Cosmology.acceleration_pos
#print axioms SCD.Cosmology.open_universe_accelerates

/-! ## PART V — predictions and data -/


-- Predictions.lean
#print axioms SCD.Predictions.accel_numerator
#print axioms SCD.Predictions.powerlaw_accel_numerator
#print axioms SCD.Predictions.accelerates_iff
#print axioms SCD.Predictions.eos_dissipationExponent
#print axioms SCD.Predictions.dissipationExponent_eos
#print axioms SCD.Predictions.eos_one
#print axioms SCD.Predictions.eos_eq_neg_one_iff
#print axioms SCD.Predictions.eos_lt_third_iff
#print axioms SCD.Predictions.eos_lt_neg_one_iff
#print axioms SCD.Predictions.worked_inversion
#print axioms SCD.Predictions.muon_lifetime_value
#print axioms SCD.Predictions.muon_matches_experiment
#print axioms SCD.Predictions.poundRebka_value
#print axioms SCD.Predictions.darkEnergyDensity_value
#print axioms SCD.Predictions.logScale_step
#print axioms SCD.Predictions.logScale_ratio_const
#print axioms SCD.Predictions.logScale_closed

-- Cosmos.lean
#print axioms SCD.Cosmos.shift_invariant_is_constant
#print axioms SCD.Cosmos.rate_constant_of_fiducial_invariance
#print axioms SCD.Cosmos.w_does_not_evolve
#print axioms SCD.Cosmos.scale_ratio_depends_only_on_difference
#print axioms SCD.Cosmos.no_first_moment
#print axioms SCD.Cosmos.finite_lookback_no_origin
#print axioms SCD.Cosmos.isotropic_gravitates_without_labels
#print axioms SCD.Cosmos.dark_matter_has_no_species
#print axioms SCD.Cosmos.two_dark_routes_differ
#print axioms SCD.Cosmos.resolvable_needs_width_below_gap
#print axioms SCD.Cosmos.mean_gap_bound
#print axioms SCD.Cosmos.broad_structures_unresolvable
#print axioms SCD.Cosmos.resolvability_boundary

-- Native.lean
#print axioms SCD.Native.not_two_places_of_parallel
#print axioms SCD.Native.separation_is_oriented
#print axioms SCD.Native.single_anisotropy_boundary
#print axioms SCD.Native.label_forces_anisotropy
#print axioms SCD.Native.zero_window_resolves_nothing
#print axioms SCD.Native.content_is_interval_valued
#print axioms SCD.Native.no_global_field_equation
#print axioms SCD.Native.ordering_discrepancy_is_the_observable
#print axioms SCD.Native.parity_conserved_under_binding
#print axioms SCD.Native.both_labels_conserved
#print axioms SCD.Native.no_maximum_anisotropy
#print axioms SCD.Native.no_cutoff_either_end

-- Data.lean
#print axioms SCD.Data.desi_tension_exceeds_three_sigma
#print axioms SCD.Data.desi_significance_dataset_dependent
#print axioms SCD.Data.desi_combinations_disagree_internally
#print axioms SCD.Data.falsification_threshold
#print axioms SCD.Data.ccl_above_bound
#print axioms SCD.Data.gkpy_below_bound
#print axioms SCD.Data.determinations_straddle_bound
#print axioms SCD.Data.gkpy_updated_inside
#print axioms SCD.Data.kappa_below_bound
#print axioms SCD.Data.rho_below_bound
#print axioms SCD.Data.delta_below_bound
#print axioms SCD.Data.z_boson_far_inside
#print axioms SCD.Data.bound_separates_kappa_from_sigma
#print axioms SCD.Data.breit_wigner_spans_the_bound
#print axioms SCD.Data.dispersion_limit_above_planck
#print axioms SCD.Data.framework_predicts_no_finite_scale
#print axioms SCD.Data.one_charge_prediction
#print axioms SCD.Data.zero_nu_beta_beta_decides
#print axioms SCD.Data.scorecard

/-! ## PART VI — the register -/


-- Color.lean
#print axioms SCD.Color.BlockMonodromy.comp_perm
#print axioms SCD.Color.BlockMonodromy.anti_perm
#print axioms SCD.Color.BlockMonodromy.triv_perm
#print axioms SCD.Color.BlockMonodromy.charge_comp
#print axioms SCD.Color.BlockMonodromy.charge_anti
#print axioms SCD.Color.BlockMonodromy.triv_observable
#print axioms SCD.Color.BlockMonodromy.confinement
#print axioms SCD.Color.BlockMonodromy.pair_observable
#print axioms SCD.Color.BlockMonodromy.pair_charge
#print axioms SCD.Color.BlockMonodromy.rep_perm
#print axioms SCD.Color.BlockMonodromy.rep_charge
#print axioms SCD.Color.BlockMonodromy.bound_state_observable
#print axioms SCD.Color.BlockMonodromy.bound_state_size
#print axioms SCD.Color.BlockMonodromy.no_partial_state
#print axioms SCD.Color.BlockMonodromy.constituent_charge_fraction
#print axioms SCD.Color.BlockMonodromy.constituent_charge_rat
#print axioms SCD.Color.BlockMonodromy.bound_charge_divisible

-- ColorAudit.lean
#print axioms SCD.ColorAudit.identification_predicts_two
#print axioms SCD.ColorAudit.identification_predicts_halves
#print axioms SCD.ColorAudit.identification_fails_baryon
#print axioms SCD.ColorAudit.identification_fails_charge
#print axioms SCD.ColorAudit.spatial_block_is_not_colour_block
#print axioms SCD.ColorAudit.three_is_forced_by_data
#print axioms SCD.ColorAudit.three_matches_charge
#print axioms SCD.ColorAudit.geometry_offers_two_data_needs_three

-- Codimension.lean
#print axioms SCD.Codimension.defectDim_two
#print axioms SCD.Codimension.defectDim_three
#print axioms SCD.Codimension.defectDim_four
#print axioms SCD.Codimension.pointlike_iff_two_dim
#print axioms SCD.Codimension.three_dim_gives_strings
#print axioms SCD.Codimension.pointlike_forces_three
#print axioms SCD.Codimension.our_world_gives_strings
#print axioms SCD.Codimension.no_pointlike_in_four
#print axioms SCD.Codimension.string_mass_not_topological
#print axioms SCD.Codimension.stringMass_strictMono
#print axioms SCD.Codimension.stringMass_zero
#print axioms SCD.Codimension.extended_or_low_dimensional

-- Expressive.lean
#print axioms SCD.Expressive.diffPattern_shift
#print axioms SCD.Expressive.invariant_factors
#print axioms SCD.Expressive.diffPattern_invariant
#print axioms SCD.Expressive.invariant_iff_diffPattern
#print axioms SCD.Expressive.eval_not_invariant
#print axioms SCD.Expressive.scale_says_nothing_about_rotation
#print axioms SCD.Expressive.rotation_says_nothing_about_scale
#print axioms SCD.Expressive.channels_independent
#print axioms SCD.Expressive.neither_channel_complete
#print axioms SCD.Expressive.no_channel_coupling

-- CrossCheck.lean
#print axioms SCD.CrossCheck.rhoAll_value
#print axioms SCD.CrossCheck.rhoQuark_value
#print axioms SCD.CrossCheck.densities_differ
#print axioms SCD.CrossCheck.density_ratio_near_two
#print axioms SCD.CrossCheck.sector_relation_is_identity
#print axioms SCD.CrossCheck.qcd_extraction_returns_input
#print axioms SCD.CrossCheck.no_second_determination
#print axioms SCD.CrossCheck.quarkCvSq_value
#print axioms SCD.CrossCheck.quark_not_geometric

-- MassAudit.lean
#print axioms SCD.MassAudit.massExp_neg
#print axioms SCD.MassAudit.massQuad_neg
#print axioms SCD.MassAudit.massExp_pos
#print axioms SCD.MassAudit.massQuad_pos
#print axioms SCD.MassAudit.massExp_zero
#print axioms SCD.MassAudit.massQuad_zero
#print axioms SCD.MassAudit.mass_law_underdetermined
#print axioms SCD.MassAudit.both_laws_antiparticle_degenerate
#print axioms SCD.MassAudit.massQuad_ratio_not_constant

-- Audit.lean
#print axioms SCD.Audit.scalar_for_directional_count
#print axioms SCD.Audit.register_nonempty
#print axioms SCD.Audit.more_corrected_than_retracted
#print axioms SCD.Audit.clean_count

end SCD.Verify
