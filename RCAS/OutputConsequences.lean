import RCAS.SelfManaging
import RCAS.OutputOutcome
import RCAS.NoAllocation

/-!
# Consequences of the output/outcome decomposition

Specification in `docs/OUTPUT_CONSEQUENCES_SPEC.md`.

**A. Condition ③ of the self-managing state means output** (author's confirmation, 2026-10-05):
`q t := output g (team side at t)`, `qMin := 1`. Phase 1 could not derive ③
(`RCAS.performance_not_derivable`) because nothing linked capability to `q`; `RCAS.OutputOutcome`
supplies the link. Under knowledge sharing, once the criteria are met they stay met (SO2); and if
the task lies strictly within the team's capability once sharing has spread (its level below the
limiting frontier, its workload below the limiting effective throughput times the period), the
criteria are eventually met (SO3). SM1 then holds with ③ derived instead of assumed (SO4). What
remains assumed is the feasibility of the task given from above, not the performance itself.

**B. Effort-based allocation of profit ties pay to what the team does not answer for.** The
author's model has no allocation; this section records what an allocation would do. With profit
`outcome a s` shared in proportion to effort, take tasks given from above that may differ in
quality, amount and business fit, and the same team side meeting their criteria with the same
efforts: pay differs exactly by the difference in `fit · potentialValue`, a quantity fixed from
above (AR1, AR2). Once the criteria are met, the total to share is `fit · potentialValue`, whatever
the team improves and however efforts are keyed (AR3).

## Main results

* `RCAS.one_le_output_iff` (SO1), `RCAS.KnowledgeSharing.meets_of_meets` (SO2),
  `RCAS.KnowledgeSharing.eventually_meets` (SO3), `RCAS.eventually_selfManaging_output` (SO4)
* `RCAS.pay_sub_eq` (AR1), `RCAS.pay_eq_iff`, `RCAS.pay_ne_of_fit_ne` (AR2),
  `RCAS.total_pay_eq_of_meets` (AR3)
-/

noncomputable section

namespace RCAS

open Filter Topology

/-! ### A. Condition ③ as output -/

/-- **SO1**: reaching `qMin = 1` in output terms is meeting the purpose and criteria. -/
theorem one_le_output_iff {g : Task} {s : TeamSide} : 1 ≤ output g s ↔ MeetsCriteria g s := by
  rw [← output_eq_one_iff]
  exact ⟨fun h => le_antisymm output_le_one h, fun h => h.ge⟩

namespace KnowledgeSharing

variable {ι : Type*} [Fintype ι] [Nonempty ι] {k : ℕ → ι → ℝ} {h : ι} {η : ℕ → ι → ℝ}
  (hS : KnowledgeSharing k h η)
include hS

/-- **SO2**: under knowledge sharing, once the criteria of a fixed task are met, they stay met. -/
theorem meets_of_meets {g : Task} {φ : ℝ → ℝ} (hφ : Monotone φ) {μ : ℝ} (hμ : 0 ≤ μ)
    {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) {T : ℕ} (hT : MeetsCriteria g (teamSideOf φ μ (k T) e)) :
    ∀ t ≥ T, MeetsCriteria g (teamSideOf φ μ (k t) e) := fun _ ht =>
  hT.of_improves (hS.teamSideOf_improves hφ hμ he0 ht)

/-- The frontier converges to the frontier of a team in which everyone has the top member's
capability. -/
theorem tendsto_frontier (hfix : ∀ t, k (t + 1) h = k t h) {ηMin : ℝ} (hηMin : 0 < ηMin)
    (hη : ∀ t i, i ≠ h → ηMin ≤ η t i) (e : ι → ℝ) :
    Tendsto (fun t => frontier (k t) e) atTop (𝓝 (frontier (fun _ => k 0 h) e)) := by
  have := Tendsto.finset_sup'_nhds (s := Finset.univ) (f := fun i t => k t i * e i)
    (g := fun i => k 0 h * e i) Finset.univ_nonempty
    fun i _ => (hS.tendsto_top hfix hηMin hη i).mul_const (e i)
  exact this.congr fun t => by simp [frontier, Finset.sup'_apply]

/-- **SO3**: with sharing only, a rate bounded below and `φ` continuous, if the task's level is
below the limiting frontier and its workload below the limiting effective throughput times the
period, the criteria are met from some time on. -/
theorem eventually_meets (hfix : ∀ t, k (t + 1) h = k t h) {ηMin : ℝ} (hηMin : 0 < ηMin)
    (hη : ∀ t i, i ≠ h → ηMin ≤ η t i) {φ : ℝ → ℝ} (hφc : Continuous φ) (μ : ℝ) (e : ι → ℝ)
    {g : Task} (hd : g.difficulty < frontier (fun _ => k 0 h) e)
    (hw : g.workload < μ * ((∑ i, e i) * φ (k 0 h)) * g.period) :
    ∃ T, ∀ t ≥ T, MeetsCriteria g (teamSideOf φ μ (k t) e) := by
  have hF := (hS.tendsto_frontier hfix hηMin hη e).eventually (lt_mem_nhds hd)
  have hV := (((hS.volume_tendsto hfix hηMin hη hφc e).const_mul μ).mul_const g.period).eventually
    (lt_mem_nhds hw)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hF.and hV)
  exact ⟨T, fun t ht => ⟨(hT t ht).1.le, (hT t ht).2.le⟩⟩

end KnowledgeSharing

/-- **SO4** (SM1 with ③ derived): the hypotheses of SM1 except the performance hypothesis, plus
knowledge sharing in the task's domain with the task strictly within the team's limiting
capability, give the self-managing state from some time on, with ③ read as output (`q t` = the
output on the task, `qMin = 1`). -/
theorem eventually_selfManaging_output {ι κ 𝓡 ι' : Type*} [Fintype ι'] [Nonempty ι']
    {kc : ℕ → ι → κ → ℝ} {ηc : ℝ} {L : ℕ → ι → κ → ℝ} {θ : κ → ℝ} {D : ℕ → ℝ} {p δ : ℝ}
    {RD : RuleDynamics 𝓡} {R : ℕ → 𝓡}
    -- SM1 without the performance hypothesis
    (hk : ∀ t i j, kc (t + 1) i j = min 1 (kc t i j + ηc * L t i j)) (hηc : 0 ≤ ηc)
    (hL : ∀ t i j, 0 ≤ L t i j) (hk0 : ∀ i j, kc 0 i j ≤ 1) {T₁ : ℕ}
    (hcov : CollectiveCover (kc T₁) θ)
    (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ)
    (hR : ∃ T₄, ∀ t ≥ T₄, R (t + 1) = RD.update (R t))
    -- knowledge sharing in the task's domain, and a task within the limiting capability
    {k : ℕ → ι' → ℝ} {h : ι'} {η : ℕ → ι' → ℝ} (hS : KnowledgeSharing k h η)
    (hfix : ∀ t, k (t + 1) h = k t h) {ηMin : ℝ} (hηMin : 0 < ηMin)
    (hη : ∀ t i, i ≠ h → ηMin ≤ η t i) {φ : ℝ → ℝ} (hφc : Continuous φ) (μ : ℝ) (e : ι' → ℝ)
    {g : Task} (hd : g.difficulty < frontier (fun _ => k 0 h) e)
    (hw : g.workload < μ * ((∑ i, e i) * φ (k 0 h)) * g.period) :
    ∃ T, ∀ t ≥ T,
      SelfManaging kc θ D δ (fun t => output g (teamSideOf φ μ (k t) e)) 1 RD R t := by
  obtain ⟨T₃, hT₃⟩ := hS.eventually_meets hfix hηMin hη hφc μ e hd hw
  exact eventually_selfManaging hk hηc hL hk0 hcov hD hp hp1 hδ
    ⟨T₃, fun t ht => one_le_output_iff.mpr (hT₃ t ht)⟩ hR

/-! ### B. Effort-based allocation of profit and the scope of responsibility -/

section Allocation

variable {a a' : GivenFromAbove} {s : TeamSide} {e : Fin 2 → ℝ}

/-- **AR1**: take any two tasks given from above — they may differ in quality, amount and business
fit — and the same team side meeting both sets of criteria. Sharing the profit in proportion to the
same efforts gives pay differing by the effort share times the difference in
`fit · potentialValue`; nothing on the team side enters the difference. -/
theorem pay_sub_eq (hm : MeetsCriteria a.task s) (hm' : MeetsCriteria a'.task s) (i : Fin 2) :
    proportionalShare i e (outcome a s) - proportionalShare i e (outcome a' s) =
      e i / (e 0 + e 1) *
        (a.fit * a.task.potentialValue - a'.fit * a'.task.potentialValue) := by
  rw [proportionalShare, proportionalShare, outcome_eq_of_meets hm, outcome_eq_of_meets hm']
  ring

/-- **AR2**: under the same conditions, with positive effort, pay is equal exactly when the
quantities given from above, `fit · potentialValue`, are equal. -/
theorem pay_eq_iff (hm : MeetsCriteria a.task s) (hm' : MeetsCriteria a'.task s) {i : Fin 2}
    (hei : 0 < e i) (he : 0 < e 0 + e 1) :
    proportionalShare i e (outcome a s) = proportionalShare i e (outcome a' s) ↔
      a.fit * a.task.potentialValue = a'.fit * a'.task.potentialValue := by
  rw [← sub_eq_zero, pay_sub_eq hm hm', mul_eq_zero, sub_eq_zero]
  simp [(div_pos hei he).ne']

/-- **AR2** (same task): with the same efforts and the same (complete) output, pay differs whenever
the business fit differs. -/
theorem pay_ne_of_fit_ne (htask : a.task = a'.task) (hm : MeetsCriteria a.task s) {i : Fin 2}
    (hei : 0 < e i) (he : 0 < e 0 + e 1) (hv : 0 < a.task.potentialValue)
    (hfit : a.fit ≠ a'.fit) :
    proportionalShare i e (outcome a s) ≠ proportionalShare i e (outcome a' s) := by
  intro h
  have := (pay_eq_iff hm (htask ▸ hm) hei he).mp h
  rw [← htask] at this
  exact hfit (mul_right_cancel₀ hv.ne' this)

/-- **AR3**: once the criteria are met, the total to share is `fit · potentialValue`, fixed from
above:
however the team improves and however efforts are keyed (positive total), effort only changes the
shares, not the total. -/
theorem total_pay_eq_of_meets (hm : MeetsCriteria a.task s) {s' : TeamSide}
    (hss' : s.Improves s') (he : 0 < e 0 + e 1) :
    ∑ i, proportionalShare i e (outcome a s') = a.fit * a.task.potentialValue := by
  rw [proportionalShare_budgetBalanced he, outcome_eq_of_improves hm hss', outcome_eq_of_meets hm]

end Allocation

namespace Example

/-- AR2 in the running example: the team meets the criteria on the same task with fit `0.6` or
`0.9`; with equal efforts `(1, 1)`, member `0` receives `30` or `45`. -/
example : proportionalShare 0 ![1, 1] (outcome given team) = 30 ∧
    proportionalShare 0 ![1, 1] (outcome givenBetterFit team) = 45 := by
  have hm : MeetsCriteria task team := responsibility_example.1
  rw [outcome_eq_of_meets (a := given) hm, outcome_eq_of_meets (a := givenBetterFit) hm]
  norm_num [proportionalShare, given, givenBetterFit, task]

end Example

end RCAS
