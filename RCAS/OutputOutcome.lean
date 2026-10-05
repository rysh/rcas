import RCAS.Performance

/-!
# Capability → output → outcome, and the scope of the team's responsibility

Extension requested by the author (2026-10-05); specification in `docs/OUTPUT_OUTCOME_SPEC.md`.

task (difficulty, volume) and capability → output; output and business fit → outcome.

* Given from above (`GivenFromAbove`): the task — the level its purpose and criteria demand
  (`difficulty`), its amount (`workload`), the period, its inherent value — and how well the
  purpose and criteria fit the business (`fit ∈ [0, 1]`). The team cannot answer for these.
* The team side (`TeamSide`): its frontier, throughput, and the efficiency of its way of working
  (`mechanism`). The team answers for achieving the task, for improving the way of working, and
  for developing its capability.
* Output (`output`): the fraction of the task completed to the criteria, in `[0, 1]`; it is `1`
  exactly when the purpose and criteria are met, and stays `1` however much more capable the team
  becomes.
* Outcome (`outcome = fit · value · output`): varies with the business fit, and never exceeds
  the task's inherent value. That outcome is this product is a premise of the model.

The bound `fit · value` on the outcome is made only of quantities given from above; once the
criteria are met, the shortfall from the inherent value is `(1 - fit) · value`, whatever the team
does. Further improvement on the team side then changes only the time required.

## Main results

* `RCAS.output_nonneg`, `RCAS.output_le_one`, `RCAS.output_eq_one_iff` (OP1)
* `RCAS.output_eq_one_of_improves` (OP2), `RCAS.output_mono` (OP3)
* `RCAS.outcome_le_fit_value`, `RCAS.outcome_le_value` (OC1), `RCAS.outcome_eq_of_meets`,
  `RCAS.outcome_lt_of_fit_lt` (OC2)
* `RCAS.outcome_eq_fit_value_iff` (RS1), `RCAS.shortfall_eq_of_meets` (RS2),
  `RCAS.outcome_sub_eq` (RS3), `RCAS.outcome_eq_of_improves`, `RCAS.requiredTime_le_of_improves`
  (RS4)
* `RCAS.KnowledgeSharing.output_monotone`, `RCAS.KnowledgeSharing.requiredTime_antitone` (CP1),
  `RCAS.KnowledgeSharing.output_eq_zero_of_ceiling_lt` (CP2)
* `RCAS.Example.responsibility_example`
-/

noncomputable section

namespace RCAS

/-- A task given from above. Its purpose and criteria fix the level the output must reach and the
amount; the task carries an inherent value. -/
structure Task where
  /-- The level the purpose and criteria demand. -/
  difficulty : ℝ
  /-- The amount of work. -/
  workload : ℝ
  /-- The period in which the output is produced. -/
  period : ℝ
  /-- The value inherent in the task. -/
  value : ℝ
  workload_pos : 0 < workload
  period_nonneg : 0 ≤ period
  value_nonneg : 0 ≤ value

/-- What is given from above: the task and how well its purpose and criteria fit the business. -/
structure GivenFromAbove where
  /-- The task. -/
  task : Task
  /-- Business fit of the purpose and criteria. -/
  fit : ℝ
  fit_nonneg : 0 ≤ fit
  fit_le_one : fit ≤ 1

/-- The team side: what the team answers for. -/
structure TeamSide where
  /-- The highest level someone on the team delivers (`RCAS.frontier`). -/
  frontier : ℝ
  /-- Output volume per unit time (`RCAS.volume`). -/
  throughput : ℝ
  /-- Efficiency of the way of working (a multiplier on throughput). -/
  mechanism : ℝ

/-- Effective throughput: throughput under the current way of working. -/
def TeamSide.effThroughput (s : TeamSide) : ℝ :=
  s.mechanism * s.throughput

/-- `s'` is at least as capable as `s`: frontier and effective throughput do not decrease. -/
def TeamSide.Improves (s s' : TeamSide) : Prop :=
  s.frontier ≤ s'.frontier ∧ s.effThroughput ≤ s'.effThroughput

/-- Output: the fraction of the task completed to its purpose and criteria. Nothing counts if
the criteria's level is out of reach; otherwise it is the fraction of the work done in the
period. -/
def output (g : Task) (s : TeamSide) : ℝ :=
  if g.difficulty ≤ s.frontier then min 1 (s.effThroughput * g.period / g.workload) else 0

/-- The output meets the purpose and criteria: the level is reached and the work is done in the
period. -/
def MeetsCriteria (g : Task) (s : TeamSide) : Prop :=
  g.difficulty ≤ s.frontier ∧ g.workload ≤ s.effThroughput * g.period

/-- Outcome: business fit × inherent value × output. -/
def outcome (a : GivenFromAbove) (s : TeamSide) : ℝ :=
  a.fit * a.task.value * output a.task s

/-- Time required to complete the task. -/
def requiredTime (g : Task) (s : TeamSide) : ℝ :=
  g.workload / s.effThroughput

variable {g : Task} {a a' : GivenFromAbove} {s s' : TeamSide}

/-! ### Output -/

/-- **OP1**: output is nonnegative (for nonnegative effective throughput). -/
theorem output_nonneg (hs : 0 ≤ s.effThroughput) : 0 ≤ output g s := by
  unfold output
  split_ifs
  · exact le_min zero_le_one (div_nonneg (mul_nonneg hs g.period_nonneg) g.workload_pos.le)
  · exact le_rfl

/-- **OP1**: output is at most `1`. -/
theorem output_le_one : output g s ≤ 1 := by
  unfold output
  split_ifs
  · exact min_le_left _ _
  · exact zero_le_one

/-- **OP1**: output is `1` exactly when the purpose and criteria are met. -/
theorem output_eq_one_iff : output g s = 1 ↔ MeetsCriteria g s := by
  unfold output MeetsCriteria
  split_ifs with hd
  · rw [min_eq_left_iff, one_le_div g.workload_pos]
    exact ⟨fun h => ⟨hd, h⟩, fun h => h.2⟩
  · exact ⟨fun h => absurd h zero_ne_one, fun h => absurd h.1 hd⟩

/-- Meeting the criteria is preserved by improvement. -/
theorem MeetsCriteria.of_improves (h : MeetsCriteria g s) (hss' : s.Improves s') :
    MeetsCriteria g s' :=
  ⟨h.1.trans hss'.1, h.2.trans (mul_le_mul_of_nonneg_right hss'.2 g.period_nonneg)⟩

/-- **OP2** (output is constant once the criteria are met): further capability or a better way of
working leaves the output at `1`. -/
theorem output_eq_one_of_improves (h : MeetsCriteria g s) (hss' : s.Improves s') :
    output g s' = 1 :=
  output_eq_one_iff.mpr (h.of_improves hss')

/-- **OP3**: output is monotone in the team side. -/
theorem output_mono (hss' : s.Improves s') (hs' : 0 ≤ s'.effThroughput) :
    output g s ≤ output g s' := by
  unfold output
  split_ifs with h h'
  · gcongr
    · exact g.workload_pos.le
    · exact g.period_nonneg
    · exact hss'.2
  · exact absurd (h.trans hss'.1) h'
  · exact le_min zero_le_one (div_nonneg (mul_nonneg hs' g.period_nonneg) g.workload_pos.le)
  · exact le_rfl

/-! ### Outcome -/

theorem fit_value_nonneg (a : GivenFromAbove) : 0 ≤ a.fit * a.task.value :=
  mul_nonneg a.fit_nonneg a.task.value_nonneg

/-- **OC1** / **RS1**: whatever the team side, the outcome is at most `fit · value`, a bound made
only of quantities given from above. -/
theorem outcome_le_fit_value (a : GivenFromAbove) (s : TeamSide) :
    outcome a s ≤ a.fit * a.task.value :=
  mul_le_of_le_one_right (fit_value_nonneg a) output_le_one

/-- **OC1**: the outcome never exceeds the value inherent in the task. -/
theorem outcome_le_value (a : GivenFromAbove) (s : TeamSide) : outcome a s ≤ a.task.value :=
  (outcome_le_fit_value a s).trans (mul_le_of_le_one_left a.task.value_nonneg a.fit_le_one)

/-- **OC2**: once the criteria are met, the outcome is `fit · value`. -/
theorem outcome_eq_of_meets (h : MeetsCriteria a.task s) : outcome a s = a.fit * a.task.value := by
  rw [outcome, output_eq_one_iff.mpr h, mul_one]

/-- **OC2**: with the same task met to the criteria, better business fit gives a strictly larger
outcome (for a task of positive value). -/
theorem outcome_lt_of_fit_lt (htask : a.task = a'.task) (hv : 0 < a.task.value)
    (hfit : a.fit < a'.fit) (h : MeetsCriteria a.task s) : outcome a s < outcome a' s := by
  rw [outcome_eq_of_meets h, outcome_eq_of_meets (htask ▸ h), ← htask]
  exact mul_lt_mul_of_pos_right hfit hv

/-- **RS1**: when `fit · value > 0`, the team reaches the bound `fit · value` exactly when it meets
the purpose and criteria. -/
theorem outcome_eq_fit_value_iff (hpos : 0 < a.fit * a.task.value) :
    outcome a s = a.fit * a.task.value ↔ MeetsCriteria a.task s := by
  rw [← output_eq_one_iff, outcome]
  constructor
  · intro h
    exact mul_left_cancel₀ hpos.ne' (h.trans (mul_one _).symm)
  · intro h
    rw [h, mul_one]

/-- **RS2**: once the criteria are met, the shortfall from the inherent value is
`(1 - fit) · value`, whatever the team side is. -/
theorem shortfall_eq_of_meets (h : MeetsCriteria a.task s) :
    a.task.value - outcome a s = (1 - a.fit) * a.task.value := by
  rw [outcome_eq_of_meets h]
  ring

/-- Output depends on the task only through its criteria (difficulty, workload, period). -/
theorem output_eq_of_same_criteria {g g' : Task} (hd : g.difficulty = g'.difficulty)
    (hw : g.workload = g'.workload) (hp : g.period = g'.period) (s : TeamSide) :
    output g s = output g' s := by
  simp only [output, hd, hw, hp]

/-- **RS3**: for the same team side and the same criteria, the difference in outcome comes only
from quantities given from above (business fit and inherent value). -/
theorem outcome_sub_eq (hd : a.task.difficulty = a'.task.difficulty)
    (hw : a.task.workload = a'.task.workload) (hp : a.task.period = a'.task.period)
    (s : TeamSide) :
    outcome a s - outcome a' s =
      (a.fit * a.task.value - a'.fit * a'.task.value) * output a.task s := by
  rw [outcome, outcome, ← output_eq_of_same_criteria hd hw hp]
  ring

/-- **RS4**: once the criteria are met, improving capability or the way of working leaves the
outcome unchanged. -/
theorem outcome_eq_of_improves (h : MeetsCriteria a.task s) (hss' : s.Improves s') :
    outcome a s' = outcome a s := by
  rw [outcome_eq_of_meets h, outcome_eq_of_meets (h.of_improves hss')]

/-- **RS4**: what improvement still changes is the time required, which does not increase. -/
theorem requiredTime_le_of_improves (hs : 0 < s.effThroughput) (hss' : s.Improves s') :
    requiredTime g s' ≤ requiredTime g s :=
  div_le_div_of_nonneg_left g.workload_pos.le hs hss'.2

/-! ### Connection to capability development (`RCAS.Performance`) -/

/-- The team side built from capabilities `k` and engagement `e`: frontier `RCAS.frontier`,
throughput `RCAS.volume`, and a way-of-working multiplier `μ`. -/
def teamSideOf {ι : Type*} [Fintype ι] [Nonempty ι] (φ : ℝ → ℝ) (μ : ℝ) (k e : ι → ℝ) :
    TeamSide :=
  ⟨frontier k e, volume φ k e, μ⟩

namespace KnowledgeSharing

variable {ι : Type*} [Fintype ι] [Nonempty ι] {k : ℕ → ι → ℝ} {h : ι} {η : ℕ → ι → ℝ}
  (hS : KnowledgeSharing k h η)
include hS

theorem teamSideOf_improves {φ : ℝ → ℝ} (hφ : Monotone φ) {μ : ℝ} (hμ : 0 ≤ μ) {e : ι → ℝ}
    (he0 : ∀ i, 0 ≤ e i) {t t' : ℕ} (htt' : t ≤ t') :
    (teamSideOf φ μ (k t) e).Improves (teamSideOf φ μ (k t') e) :=
  ⟨hS.frontier_monotone he0 htt',
    mul_le_mul_of_nonneg_left (hS.volume_monotone hφ he0 htt') hμ⟩

/-- **CP1**: under knowledge sharing, the output on a fixed task is non-decreasing in time. -/
theorem output_monotone (g : Task) {φ : ℝ → ℝ} (hφ : Monotone φ) (hφ0 : ∀ x, 0 ≤ φ x) {μ : ℝ}
    (hμ : 0 ≤ μ) {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) :
    Monotone fun t => output g (teamSideOf φ μ (k t) e) := fun _ _ htt' =>
  output_mono (hS.teamSideOf_improves hφ hμ he0 htt')
    (mul_nonneg hμ (Finset.sum_nonneg fun i _ => mul_nonneg (he0 i) (hφ0 _)))

/-- **CP1**: under knowledge sharing, the time required for a fixed task does not increase. -/
theorem requiredTime_antitone (g : Task) {φ : ℝ → ℝ} (hφ : Monotone φ) {μ : ℝ} (hμ : 0 ≤ μ)
    {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) (hpos : 0 < (teamSideOf φ μ (k 0) e).effThroughput) :
    Antitone fun t => requiredTime g (teamSideOf φ μ (k t) e) := fun t _ htt' =>
  requiredTime_le_of_improves
    (hpos.trans_le (hS.teamSideOf_improves hφ hμ he0 (Nat.zero_le t)).2)
    (hS.teamSideOf_improves hφ hμ he0 htt')

/-- **CP2**: with sharing only, a task whose level is above the initial capability ceiling is
never achieved, however long sharing goes on. The range of tasks the team can take on widens only
when the ceiling rises (the top member learns, PM1; or specialization, OM3). -/
theorem output_eq_zero_of_ceiling_lt (hfix : ∀ t, k (t + 1) h = k t h) (hk0 : ∀ i, 0 ≤ k 0 i)
    {e : ι → ℝ} (he1 : ∀ i, e i ≤ 1) (φ : ℝ → ℝ) (μ : ℝ) {g : Task}
    (hg : ceiling (k 0) < g.difficulty) (t : ℕ) :
    output g (teamSideOf φ μ (k t) e) = 0 := by
  have hF : frontier (k t) e < g.difficulty :=
    (hS.frontier_le_initial_ceiling hfix hk0 he1 t).trans_lt hg
  simp [output, teamSideOf, not_le.mpr hF]

end KnowledgeSharing

namespace Example

/-- A task of level `1`, workload `10`, period `1`, inherent value `100`. -/
def task : Task := ⟨1, 10, 1, 100, by norm_num, by norm_num, by norm_num⟩

/-- Given with business fit `0.6`, and the same task with fit `0.9`. -/
def given : GivenFromAbove := ⟨task, 3 / 5, by norm_num, by norm_num⟩
def givenBetterFit : GivenFromAbove := ⟨task, 9 / 10, by norm_num, by norm_num⟩

/-- A team that reaches level `1` and processes `10` per unit time; and the same team with its
way of working improved to double the throughput. -/
def team : TeamSide := ⟨1, 10, 1⟩
def teamImproved : TeamSide := ⟨1, 10, 2⟩

/-- The team meets the criteria; its outcome is `60` of the inherent `100`. Improving its way of
working leaves the outcome at `60` and halves the required time. With better business fit, the
same team's outcome is `90`. -/
theorem responsibility_example :
    MeetsCriteria task team ∧ outcome given team = 60 ∧ outcome given teamImproved = 60 ∧
      requiredTime task team = 1 ∧ requiredTime task teamImproved = 1 / 2 ∧
      outcome givenBetterFit team = 90 := by
  have hm : MeetsCriteria task team := by
    norm_num [MeetsCriteria, task, team, TeamSide.effThroughput]
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [outcome_eq_of_meets (a := given) hm]; norm_num [given, task]
  · rw [outcome_eq_of_improves (a := given) (s' := teamImproved) hm
      ⟨le_rfl, by norm_num [team, teamImproved, TeamSide.effThroughput]⟩,
      outcome_eq_of_meets (a := given) hm]
    norm_num [given, task]
  · norm_num [requiredTime, task, team, TeamSide.effThroughput]
  · norm_num [requiredTime, task, teamImproved, TeamSide.effThroughput]
  · rw [outcome_eq_of_meets (a := givenBetterFit) hm]; norm_num [givenBetterFit, task]

end Example

end RCAS
