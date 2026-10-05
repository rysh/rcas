import RCAS.Performance

/-!
# Steiner's task types and the components of performance (survey addition §2)

Steiner (1972) classifies team tasks as disjunctive (the best member decides), additive (the
contributions add up) and conjunctive (the weakest member decides). The disjunctive aggregate of
the members' effective levels `k i * e i` is the frontier of `RCAS.Performance`; the additive
aggregate of `e i * φ (k i)` is the volume.

Under knowledge sharing (`RCAS.KnowledgeSharing`, used as is):

* disjunctive: the aggregate of capabilities (the ceiling) does not change with sharing only (ST1,
  ST4). The aggregate of *effective* levels (the frontier) does not change either **provided the
  top member is the most engaged**; without that, sharing can raise it
  (`RCAS.Example.disjunctive_can_rise`), because a more engaged member catches up with the top
  member's capability. In general it is non-decreasing and bounded by the initial ceiling;
* additive: non-decreasing (ST2, = PV1);
* conjunctive: non-decreasing (ST3); with sharing only and a rate bounded below, the weakest
  member's capability converges to the top member's.

## Main results

* `RCAS.aggregate_mono`
* `RCAS.KnowledgeSharing.aggregate_disjunctive_const`, `..._not_rise` (ST1, ST4, capability)
* `RCAS.KnowledgeSharing.aggregate_disjunctive_eff_const`, `..._eff_not_rise` (ST1, ST4,
  effective levels, top member most engaged)
* `RCAS.Example.disjunctive_can_rise` (without the top member being most engaged)
* `RCAS.KnowledgeSharing.aggregate_additive_monotone` (ST2)
* `RCAS.KnowledgeSharing.aggregate_conjunctive_monotone`,
  `RCAS.KnowledgeSharing.tendsto_aggregate_conjunctive` (ST3)
-/

noncomputable section

namespace RCAS

open Filter Topology

/-- Steiner's task types. -/
inductive TaskType where
  /-- The team's result is the best member's result. -/
  | disjunctive
  /-- The team's result is the sum of the members' results. -/
  | additive
  /-- The team's result is the weakest member's result. -/
  | conjunctive

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The team's result for a task type, from the members' results `perf`. -/
def aggregate (tt : TaskType) (perf : ι → ℝ) : ℝ :=
  match tt with
  | .disjunctive => Finset.univ.sup' Finset.univ_nonempty perf
  | .additive => ∑ i, perf i
  | .conjunctive => Finset.univ.inf' Finset.univ_nonempty perf

theorem aggregate_disjunctive_eq_ceiling (k : ι → ℝ) : aggregate .disjunctive k = ceiling k :=
  rfl

theorem aggregate_disjunctive_eq_frontier (k e : ι → ℝ) :
    aggregate .disjunctive (fun i => k i * e i) = frontier k e :=
  rfl

theorem aggregate_additive_eq_volume (φ : ℝ → ℝ) (k e : ι → ℝ) :
    aggregate .additive (fun i => e i * φ (k i)) = volume φ k e :=
  rfl

/-- Every task type aggregates monotonically. -/
theorem aggregate_mono (tt : TaskType) {perf perf' : ι → ℝ} (h : ∀ i, perf i ≤ perf' i) :
    aggregate tt perf ≤ aggregate tt perf' := by
  cases tt with
  | disjunctive =>
    exact Finset.sup'_le Finset.univ_nonempty _ fun i _ =>
      (h i).trans (Finset.le_sup' perf' (Finset.mem_univ i))
  | additive => exact Finset.sum_le_sum fun i _ => h i
  | conjunctive =>
    exact Finset.le_inf' Finset.univ_nonempty _ fun i _ =>
      (Finset.inf'_le perf (Finset.mem_univ i)).trans (h i)

namespace KnowledgeSharing

variable {k : ℕ → ι → ℝ} {h : ι} {η : ℕ → ι → ℝ} (hS : KnowledgeSharing k h η)
include hS

/-- **ST1** (capability): with sharing only, the disjunctive aggregate of capabilities does not
change (PS2). -/
theorem aggregate_disjunctive_const (hfix : ∀ t, k (t + 1) h = k t h) (t : ℕ) :
    aggregate .disjunctive (k t) = aggregate .disjunctive (k 0) :=
  hS.ceiling_const hfix t

/-- **ST4** (capability): sharing alone never raises the disjunctive aggregate of capabilities. -/
theorem aggregate_disjunctive_not_rise (hfix : ∀ t, k (t + 1) h = k t h) (t : ℕ) :
    ¬ aggregate .disjunctive (k 0) < aggregate .disjunctive (k t) := by
  rw [hS.aggregate_disjunctive_const hfix t]
  exact lt_irrefl _

/-- **ST1** (effective levels): with sharing only, if the top member is the most engaged, the
disjunctive aggregate of effective levels stays at `k 0 h * e h`. -/
theorem aggregate_disjunctive_eff_const (hfix : ∀ t, k (t + 1) h = k t h)
    (hk0 : ∀ i, 0 ≤ k 0 i) {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) (heh : ∀ i, e i ≤ e h) (t : ℕ) :
    aggregate .disjunctive (fun i => k t i * e i) = k 0 h * e h := by
  refine le_antisymm (Finset.sup'_le Finset.univ_nonempty _ fun i _ => ?_) ?_
  · rw [← top_const hfix t]
    exact mul_le_mul (hS.le_top t i) (heh i) (he0 i) (hS.nonneg hk0 t h)
  · rw [← top_const hfix t]
    exact Finset.le_sup' (fun i => k t i * e i) (Finset.mem_univ h)

/-- **ST4** (effective levels): under the same hypotheses, sharing alone never raises the
disjunctive aggregate of effective levels. -/
theorem aggregate_disjunctive_eff_not_rise (hfix : ∀ t, k (t + 1) h = k t h)
    (hk0 : ∀ i, 0 ≤ k 0 i) {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) (heh : ∀ i, e i ≤ e h) (t : ℕ) :
    ¬ aggregate .disjunctive (fun i => k 0 i * e i) <
      aggregate .disjunctive (fun i => k t i * e i) := by
  rw [hS.aggregate_disjunctive_eff_const hfix hk0 he0 heh t,
    hS.aggregate_disjunctive_eff_const hfix hk0 he0 heh 0]
  exact lt_irrefl _

/-- In general (top member not necessarily most engaged), the disjunctive aggregate of effective
levels is non-decreasing (PS3) and bounded by the initial ceiling (PS2). -/
theorem aggregate_disjunctive_eff_bounds (hfix : ∀ t, k (t + 1) h = k t h)
    (hk0 : ∀ i, 0 ≤ k 0 i) {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1) :
    Monotone (fun t => aggregate .disjunctive (fun i => k t i * e i)) ∧
      ∀ t, aggregate .disjunctive (fun i => k t i * e i) ≤ aggregate .disjunctive (k 0) :=
  ⟨hS.frontier_monotone he0, hS.frontier_le_initial_ceiling hfix hk0 he1⟩

/-- **ST2**: the additive aggregate (the volume) is non-decreasing (PV1). -/
theorem aggregate_additive_monotone {φ : ℝ → ℝ} (hφ : Monotone φ) {e : ι → ℝ}
    (he0 : ∀ i, 0 ≤ e i) : Monotone fun t => aggregate .additive (fun i => e i * φ (k t i)) :=
  hS.volume_monotone hφ he0

/-- **ST3**: the conjunctive aggregate of effective levels is non-decreasing (engagement fixed):
the weakest member's level rises. -/
theorem aggregate_conjunctive_monotone {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) :
    Monotone fun t => aggregate .conjunctive (fun i => k t i * e i) :=
  monotone_nat_of_le_succ fun t =>
    aggregate_mono _ fun i => mul_le_mul_of_nonneg_right (hS.le_succ t i) (he0 i)

/-- **ST3** (where it goes): with sharing only and a rate bounded below, the weakest member's
capability converges to the top member's. -/
theorem tendsto_aggregate_conjunctive (hfix : ∀ t, k (t + 1) h = k t h) {ηMin : ℝ}
    (hηMin : 0 < ηMin) (hη : ∀ t i, i ≠ h → ηMin ≤ η t i) :
    Tendsto (fun t => aggregate .conjunctive (k t)) atTop (𝓝 (k 0 h)) := by
  have := Tendsto.finset_inf'_nhds (s := Finset.univ) (f := fun i t => k t i)
    (g := fun _ => k 0 h) Finset.univ_nonempty fun i _ => hS.tendsto_top hfix hηMin hη i
  rw [Finset.inf'_const] at this
  exact this.congr fun t => by simp [aggregate, Finset.inf'_apply]

end KnowledgeSharing

namespace Example

/-- Engagement: the expert (member `0`) is half engaged, the others fully. -/
def eHalfTop : Fin 3 → ℝ := ![1 / 2, 1, 1]

/-- Without the top member being the most engaged, sharing alone raises the disjunctive aggregate
of effective levels: from `1/2` at `t = 0` to at least `3/4` at `t = 2`. All other hypotheses of
ST1 (effective levels) hold. -/
theorem disjunctive_can_rise :
    KnowledgeSharing kShare 0 (fun _ _ => 1 / 2) ∧ (∀ t, kShare (t + 1) 0 = kShare t 0) ∧
      (∀ i, 0 ≤ eHalfTop i) ∧ ¬ (∀ i, eHalfTop i ≤ eHalfTop 0) ∧
      aggregate .disjunctive (fun i => kShare 0 i * eHalfTop i) <
        aggregate .disjunctive (fun i => kShare 2 i * eHalfTop i) := by
  refine ⟨kShare_sharing, kShare_fix, fun i => by fin_cases i <;> norm_num [eHalfTop],
    fun h => by have := h 1; norm_num [eHalfTop] at this, ?_⟩
  calc aggregate .disjunctive (fun i => kShare 0 i * eHalfTop i) ≤ 1 / 2 :=
        Finset.sup'_le Finset.univ_nonempty _ fun i _ => by
          fin_cases i <;> norm_num [kShare, eHalfTop]
    _ < aggregate .disjunctive (fun i => kShare 2 i * eHalfTop i) :=
        (Finset.lt_sup'_iff Finset.univ_nonempty).mpr
          ⟨1, Finset.mem_univ _, by norm_num [kShare, eHalfTop]⟩

end Example

end RCAS
