import RCAS.Performance

/-!
# Knowledge hierarchy and escalation (survey addition §5)

Garicano (2000): problems have difficulties distributed with cumulative distribution `F`; a
worker with knowledge `z` solves the problems up to `z` and escalates the rest, at rate
`1 - F z`. As front-line knowledge spreads, escalations fall. This file connects the knowledge
sharing of `RCAS.Performance` with the decay of manager dependence in `RCAS.Dependence`.

* ESC1: escalation falls as knowledge rises; under knowledge sharing each member's escalation
  rate is non-increasing in time.
* ESC2: with sharing only and a rate bounded below, each member's escalation rate (and the team
  average) converges to the top member's — **provided `F` is continuous at the top member's
  level** (otherwise a jump of `F` there blocks convergence).
* ESC3: *if* the escalation rate is proportional to the dependence `D t` (`r t = α D t`, `α > 0`)
  — an empirical hypothesis (#23) — then the two follow the same recurrence. If moreover `D`
  decays to `0` and the team average converges as in ESC2, the top member's escalation rate must be
  `0`: the top member solves every problem (`RCAS.top_solves_all_of_proportional`).

Problems that nobody in the team can solve, `1 - F (ceiling (k t))`, are not reduced by sharing
alone (`RCAS.KnowledgeSharing.ceilingEscalation_const`, from PS2).

## Main results

* `RCAS.escalationRate_antitone`, `RCAS.KnowledgeSharing.escalation_antitone` (ESC1)
* `RCAS.KnowledgeSharing.tendsto_escalation`, `RCAS.KnowledgeSharing.tendsto_teamEscalation`
  (ESC2), `RCAS.Example.escalation_needs_continuity`
* `RCAS.proportional_recurrence_iff`, `RCAS.proportional_escalation_eq`,
  `RCAS.proportional_escalation_tendsto_zero`, `RCAS.proportional_escalation_eventually_le`
  (ESC3), `RCAS.top_solves_all_of_proportional`
-/

noncomputable section

namespace RCAS

open Filter Topology

/-- Escalation rate of a worker with knowledge `z`, problem difficulties with distribution
function `F`. -/
def escalationRate (z : ℝ) (F : ℝ → ℝ) : ℝ :=
  1 - F z

/-- **ESC1**: more knowledge, no more escalation. Immediate from the definition. -/
theorem escalationRate_antitone {F : ℝ → ℝ} (hF : Monotone F) :
    Antitone fun z => escalationRate z F :=
  fun _ _ h => sub_le_sub_left (hF h) 1

/-- Average escalation rate of the team. -/
def teamEscalation {ι : Type*} [Fintype ι] (k : ι → ℝ) (F : ℝ → ℝ) : ℝ :=
  (∑ i, escalationRate (k i) F) / Fintype.card ι

namespace KnowledgeSharing

variable {ι : Type*} {k : ℕ → ι → ℝ} {h : ι} {η : ℕ → ι → ℝ} (hS : KnowledgeSharing k h η)
include hS

/-- **ESC1** under knowledge sharing: each member's escalation rate is non-increasing in time. -/
theorem escalation_antitone {F : ℝ → ℝ} (hF : Monotone F) (i : ι) :
    Antitone fun t => escalationRate (k t i) F :=
  fun _ _ htt' => escalationRate_antitone hF (hS.monotone_member i htt')

/-- **ESC2**: with sharing only, a rate bounded below and `F` continuous at the top member's
level, each member's escalation rate converges to the top member's. -/
theorem tendsto_escalation (hfix : ∀ t, k (t + 1) h = k t h) {ηMin : ℝ} (hηMin : 0 < ηMin)
    (hη : ∀ t i, i ≠ h → ηMin ≤ η t i) {F : ℝ → ℝ} (hF : ContinuousAt F (k 0 h)) (i : ι) :
    Tendsto (fun t => escalationRate (k t i) F) atTop (𝓝 (escalationRate (k 0 h) F)) :=
  tendsto_const_nhds.sub (hF.tendsto.comp (hS.tendsto_top hfix hηMin hη i))

/-- **ESC2** for the team average. -/
theorem tendsto_teamEscalation [Fintype ι] (hfix : ∀ t, k (t + 1) h = k t h) {ηMin : ℝ}
    (hηMin : 0 < ηMin) (hη : ∀ t i, i ≠ h → ηMin ≤ η t i) {F : ℝ → ℝ}
    (hF : ContinuousAt F (k 0 h)) :
    Tendsto (fun t => teamEscalation (k t) F) atTop (𝓝 (escalationRate (k 0 h) F)) := by
  have hne : (Fintype.card ι : ℝ) ≠ 0 := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨h⟩
    exact_mod_cast this.ne'
  have hsum := (tendsto_finsetSum Finset.univ fun i _ =>
    hS.tendsto_escalation hfix hηMin hη hF i).div_const (Fintype.card ι : ℝ)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hne] at hsum
  exact hsum

/-- Problems nobody in the team can solve: with sharing only, their rate does not change (PS2). -/
theorem ceilingEscalation_const [Fintype ι] [Nonempty ι] (hfix : ∀ t, k (t + 1) h = k t h)
    (F : ℝ → ℝ) (t : ℕ) : escalationRate (ceiling (k t)) F = escalationRate (ceiling (k 0)) F := by
  rw [hS.ceiling_const hfix t]

end KnowledgeSharing

/-! ### ESC3: proportional escalation and the dependence recurrence -/

section Proportional

variable {r D : ℕ → ℝ} {α p : ℝ}

/-- **ESC3**: if escalations are proportional to dependence with `α > 0`, the dependence
recurrence and the escalation recurrence (same factor `1 - p`) are equivalent. -/
theorem proportional_recurrence_iff (hα : 0 < α) (hr : ∀ t, r t = α * D t) :
    (∀ t, D (t + 1) = (1 - p) * D t) ↔ (∀ t, r (t + 1) = (1 - p) * r t) := by
  constructor
  · intro hD t
    rw [hr, hr, hD]
    ring
  · intro hR t
    have := hR t
    rw [hr, hr] at this
    have hα' : α ≠ 0 := hα.ne'
    apply mul_left_cancel₀ hα'
    linear_combination this

/-- **ESC3** (closed form, D1 transferred). -/
theorem proportional_escalation_eq (hα : 0 < α) (hr : ∀ t, r t = α * D t)
    (hD : ∀ t, D (t + 1) = (1 - p) * D t) (t : ℕ) : r t = (1 - p) ^ t * r 0 :=
  dependence_eq ((proportional_recurrence_iff hα hr).mp hD) t

/-- **ESC3** (limit, D3 transferred). -/
theorem proportional_escalation_tendsto_zero (hα : 0 < α) (hr : ∀ t, r t = α * D t)
    (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp : 0 < p) (hp1 : p ≤ 1) :
    Tendsto r atTop (𝓝 0) :=
  dependence_tendsto_zero ((proportional_recurrence_iff hα hr).mp hD) hp hp1

/-- **ESC3** (below any threshold in finite time, D4 transferred). -/
theorem proportional_escalation_eventually_le (hα : 0 < α) (hr : ∀ t, r t = α * D t)
    (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp : 0 < p) (hp1 : p ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T, ∀ t ≥ T, r t ≤ δ :=
  dependence_eventually_le ((proportional_recurrence_iff hα hr).mp hD) hp hp1 hδ

end Proportional

/-- **ESC3** (what proportionality implies): suppose the team's average escalation rate is
proportional to the dependence, the dependence decays as in §4.7, and the conditions of ESC2
hold. Then the top member's escalation rate is `0`, i.e. `F (k 0 h) = 1`: the top member solves
every problem. -/
theorem top_solves_all_of_proportional {ι : Type*} [Fintype ι] {k : ℕ → ι → ℝ} {h : ι}
    {η : ℕ → ι → ℝ} (hS : KnowledgeSharing k h η) (hfix : ∀ t, k (t + 1) h = k t h)
    {ηMin : ℝ} (hηMin : 0 < ηMin) (hη : ∀ t i, i ≠ h → ηMin ≤ η t i) {F : ℝ → ℝ}
    (hF : ContinuousAt F (k 0 h)) {D : ℕ → ℝ} {α p : ℝ} (hα : 0 < α)
    (hr : ∀ t, teamEscalation (k t) F = α * D t) (hD : ∀ t, D (t + 1) = (1 - p) * D t)
    (hp : 0 < p) (hp1 : p ≤ 1) : F (k 0 h) = 1 := by
  have h1 := hS.tendsto_teamEscalation hfix hηMin hη hF
  have h2 := proportional_escalation_tendsto_zero hα hr hD hp hp1
  have := tendsto_nhds_unique h1 h2
  unfold escalationRate at this
  linarith

namespace Example

/-- A distribution with a jump at the expert's level `1`: every problem has difficulty exactly
`1`. -/
def stepF (z : ℝ) : ℝ :=
  if 1 ≤ z then 1 else 0

/-- Continuity at the top member's level is needed in ESC2: in the sharing example (`kShare`,
expert at `1`, member `1` at `1 - (1/2)^t < 1`), with the jump distribution `stepF` member `1`
escalates every problem at every time, while the expert escalates none. -/
theorem escalation_needs_continuity :
    (∀ t, escalationRate (kShare t 1) stepF = 1) ∧ escalationRate (kShare 0 0) stepF = 0 ∧
      ¬ Tendsto (fun t => escalationRate (kShare t 1) stepF) atTop
        (𝓝 (escalationRate (kShare 0 0) stepF)) := by
  have hmem : ∀ t, escalationRate (kShare t 1) stepF = 1 := fun t => by
    simp [escalationRate, stepF, kShare]
  have htop : escalationRate (kShare 0 0) stepF = 0 := by
    simp [escalationRate, stepF, kShare]
  refine ⟨hmem, htop, fun hlim => ?_⟩
  rw [htop] at hlim
  have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun t => (hmem t).symm)
  norm_num at this

end Example

end RCAS
