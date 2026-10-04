import RCAS.Reference
import RCAS.Constraint
import RCAS.Layers
import RCAS.RuleUpdate
import RCAS.Efficacy
import RCAS.Capability
import RCAS.Dependence
import RCAS.Decision
import RCAS.FutureChoice
import RCAS.SelfManaging
import RCAS.Field.Forcing
import RCAS.Field.StuartLandau
import RCAS.Field.Coupling
import RCAS.Field.Threshold
import RCAS.Field.Attention
import RCAS.Field.MutualInduction
import RCAS.Field.SelfManagingField

/-!
# Axiom audit

Two checks:

1. `#print axioms` for every main theorem, for the human reader.
2. `#assert_standard_axioms_in RCAS`, which makes the build **fail** if any declaration in the
   namespace `RCAS` depends on an axiom other than `propext`, `Classical.choice` and
   `Quot.sound`. In particular a leftover `sorry` (`sorryAx`) fails the build.
-/

open Lean Elab Command in
/-- `#assert_standard_axioms_in N` fails if some declaration whose name starts with `N` depends
on an axiom other than `propext`, `Classical.choice`, `Quot.sound`; otherwise it reports how
many declarations were checked. -/
elab "#assert_standard_axioms_in " ns:ident : command => do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if ns.getId.isPrefixOf n then acc.push n else acc
  let mut bad : Array (Name × Array Name) := #[]
  for n in names do
    let axs ← collectAxioms n
    let extra := axs.filter (fun a => !std.contains a)
    unless extra.isEmpty do bad := bad.push (n, extra)
  unless bad.isEmpty do
    throwError "non-standard axioms: {bad.toList}"
  logInfo m!"{names.size} declarations under `{ns.getId}` use only standard axioms"

#assert_standard_axioms_in RCAS

/-! ### §4.1 Reference -/
#print axioms RCAS.GenuineChoice.not_prescription
#print axioms RCAS.IsReferenceChoice.not_prescription_and_not_laissezFaire
#print axioms RCAS.GenuineChoice.exists_distinct_acceptable
#print axioms RCAS.Example.regimes_nonempty_and_distinct
#print axioms RCAS.GenuineChoice.outcome_standardized_and_method_diverse
#print axioms RCAS.Example.standardization_with_autonomy

/-! ### §4.2 Constraint -/
#print axioms RCAS.exists_minSufficient
#print axioms RCAS.exists_minSufficient_univ
#print axioms RCAS.prefers_of_cost_lt
#print axioms RCAS.not_minSufficient_of_prefers
#print axioms RCAS.not_minSufficient_of_erase
#print axioms RCAS.MinSufficient.not_admissible_erase
#print axioms RCAS.not_minSufficient_of_erase_needs_mem

/-! ### §4.3 Layers -/
#print axioms RCAS.ThreeLayer.mem_orgAllowed
#print axioms RCAS.sound_not_automatic

/-! ### §4.4 RuleUpdate -/
#print axioms RCAS.RuleDynamics.J_iterate_succ_ge
#print axioms RCAS.RuleDynamics.monotone_J_iterate
#print axioms RCAS.stay_needed
#print axioms RCAS.RuleDynamics.tendsto_J_iterate
#print axioms RCAS.RuleDynamics.J_update_gt_of_erase
#print axioms RCAS.Example.card_not_monotone

/-! ### §4.5 Efficacy -/
#print axioms RCAS.efficacy_monotone
#print axioms RCAS.efficacy_eq
#print axioms RCAS.efficacy_eq_init_of_not_selfChosen
#print axioms RCAS.efficacy_lt_of_selfChosen_success

/-! ### §4.6 Capability -/
#print axioms RCAS.SuperManager.collectiveCover
#print axioms RCAS.Example.cover_without_superManager
#print axioms RCAS.Example.cover_not_imp_superManager
#print axioms RCAS.hall_iff_exists_assignment
#print axioms RCAS.hall_iff_exists_assignment_capOf
#print axioms RCAS.collectiveCover_of_hall
#print axioms RCAS.diffusion_monotone
#print axioms RCAS.diffusion_cover_preserved
#print axioms RCAS.diffusion_needs_le_one
#print axioms RCAS.cover_without_of_redundant
#print axioms RCAS.Example.concentrated_cover_breaks

/-! ### §4.7 Dependence -/
#print axioms RCAS.dependence_eq
#print axioms RCAS.dependence_succ_lt
#print axioms RCAS.dependence_strictAnti
#print axioms RCAS.dependence_strictAnti_needs
#print axioms RCAS.dependence_tendsto_zero
#print axioms RCAS.dependence_eventually_le
#print axioms RCAS.dependence_tendsto_zero_of_timeVarying
#print axioms RCAS.dependence_eventually_le_of_timeVarying
#print axioms RCAS.dependence_timeVarying_needs_upper_bound

/-! ### §4.8 Decision -/
#print axioms RCAS.Decision.instDecidableReopenable
#print axioms RCAS.Decision.not_reopenable_of_premises_eq_empty
#print axioms RCAS.Decision.Reopenable.mono

/-! ### §4.9 FutureChoice -/
#print axioms RCAS.sup'_le_sup'_of_subset
#print axioms RCAS.sup'_le_sup'_insert
#print axioms RCAS.IsChoice.sup'_le
#print axioms RCAS.sup'_le_of_choose_new
#print axioms RCAS.information_dependent_counterexample

/-! ### §4.10 SelfManaging -/
#print axioms RCAS.eventually_selfManaging
#print axioms RCAS.SelfManaging.J_le_succ
#print axioms RCAS.performance_not_derivable

/-! ### §5.1 Field/Forcing -/
#print axioms RCAS.tendsto_of_eventually_contracting
#print axioms RCAS.forcing_does_not_persist
#print axioms RCAS.forcing_history_irrelevant
#print axioms RCAS.scalar_tendsto
#print axioms RCAS.affine_fixed_injective
#print axioms RCAS.directive_vs_constraint
#print axioms RCAS.eventually_le_of_affine_bound
#print axioms RCAS.eventually_near_of_stableBand
#print axioms RCAS.tendsto_of_stableBand_zero

/-! ### §5.2 Field/StuartLandau -/
#print axioms RCAS.slRhs_eq_zero_iff_of_nonpos
#print axioms RCAS.slRhs_eq_zero_iff_of_pos
#print axioms RCAS.deriv_slRhs
#print axioms RCAS.deriv_slRhs_zero
#print axioms RCAS.deriv_slRhs_sqrt
#print axioms RCAS.deriv_slRhs_sqrt_needs_nonneg
#print axioms RCAS.deriv_slRhs_zero_at_criticality
#print axioms RCAS.deriv_slRhs_signs

/-! ### §5.3 Field/Coupling -/
#print axioms RCAS.propagate_eq
#print axioms RCAS.influence_eq
#print axioms RCAS.influence_eq_zero_of_uncoupled
#print axioms RCAS.pow_apply_eq_zero_of_not_walk
#print axioms RCAS.influence_eq_zero_of_no_walk

/-! ### §5.4 Field/Threshold -/
#print axioms RCAS.subset_step
#print axioms RCAS.monotone_iterate_step
#print axioms RCAS.step_mono
#print axioms RCAS.iterate_step_mono
#print axioms RCAS.iterate_step_mono_weight
#print axioms RCAS.step_singleton_of_isolated
#print axioms RCAS.iterate_step_singleton_of_isolated
#print axioms RCAS.step_finalAdopters
#print axioms RCAS.iterate_step_subset_finalAdopters

/-! ### §5.5 Field/Attention -/
#print axioms RCAS.effWeight_le
#print axioms RCAS.effWeight_eq_of_aligned
#print axioms RCAS.iterate_step_effWeight_subset_aligned
#print axioms RCAS.finalAdopters_effWeight_subset_aligned

/-! ### §5.6 Field/MutualInduction -/
#print axioms RCAS.mutual_sum_eq
#print axioms RCAS.mutual_diff_succ
#print axioms RCAS.mutual_diff_eq
#print axioms RCAS.mutual_tendsto
#print axioms RCAS.mutual_limit_ne

/-! ### §4.10 strong definition, Field/SelfManagingField -/
#print axioms RCAS.SelfManagingStrong.toSelfManaging
#print axioms RCAS.eventually_selfManagingStrong
#print axioms RCAS.SelfManagingStrong.mem_stableBand
#print axioms RCAS.SelfManagingStrong.eventually_near
#print axioms RCAS.SelfManagingStrong.eventually_near_of_invariant
#print axioms RCAS.SelfManagingStrong.tendsto_of_fixed_level
