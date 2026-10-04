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
