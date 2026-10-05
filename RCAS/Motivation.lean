import RCAS.Performance

/-!
# Engagement on the self-determination continuum (survey addition §4)

Self-Determination Theory (Deci & Ryan; Gagné & Deci 2005) places motivation on a continuum
amotivation → external → introjected → identified → integrated → intrinsic; identified and above
are autonomous, external and introjected are controlled. This file expresses that structure as
Lean types and connects it to the engagement variable `e` of `RCAS.Performance`.

It is not a psychological model. The engagement dynamics below have two channels whose effects
are **premises**: competence-affirming verbal feedback while motivation stays autonomous adds
`β ≥ 0`; a controlling (contingent) reward subtracts `γ ≥ 0`. SDT1 shows by explicit numbers that
the vocabulary can express a drop of engagement after a reward; it does not derive the effect
size of Deci et al. (1999). Transitions between motivation types are inputs, not modelled.

## Main results

* `RCAS.MotivationType.isAutonomous_iff`, `RCAS.MotivationType.not_isAutonomous_and_isControlled`
* `RCAS.volume_mono_engagement`, `RCAS.carriers_mono_engagement`,
  `RCAS.frontier_mono_engagement` (performance is monotone in engagement)
* `RCAS.engagementPath_le_succ`, `RCAS.engagementPath_monotone`, `RCAS.engagementPath_lt_succ`
  (SDT2)
* `RCAS.engagementPath_succ_lt`, `RCAS.Example.sdt1` (SDT1)
-/

noncomputable section

namespace RCAS

/-- The self-determination continuum, in order. -/
inductive MotivationType where
  | amotivation
  | external
  | introjected
  | identified
  | integrated
  | intrinsic
  deriving DecidableEq, Repr

namespace MotivationType

/-- Position on the continuum (`0` = amotivation, …, `5` = intrinsic). -/
def rank : MotivationType → ℕ
  | amotivation => 0
  | external => 1
  | introjected => 2
  | identified => 3
  | integrated => 4
  | intrinsic => 5

/-- Autonomous motivation: identified and above. -/
def isAutonomous : MotivationType → Prop
  | .identified | .integrated | .intrinsic => True
  | _ => False

/-- Controlled motivation: external and introjected. -/
def isControlled : MotivationType → Prop
  | .external | .introjected => True
  | _ => False

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

theorem isAutonomous_iff (m : MotivationType) : m.isAutonomous ↔ 3 ≤ m.rank := by
  cases m <;> simp [isAutonomous, rank]

theorem isControlled_iff (m : MotivationType) : m.isControlled ↔ m.rank = 1 ∨ m.rank = 2 := by
  cases m <;> simp [isControlled, rank]

instance : DecidablePred isAutonomous := fun m => decidable_of_iff _ (isAutonomous_iff m).symm

instance : DecidablePred isControlled := fun m => decidable_of_iff _ (isControlled_iff m).symm

/-- Autonomous and controlled motivation exclude each other. -/
theorem not_isAutonomous_and_isControlled (m : MotivationType) :
    ¬ (m.isAutonomous ∧ m.isControlled) := by
  cases m <;> simp [isAutonomous, isControlled]

/-- Amotivation is neither autonomous nor controlled. -/
theorem amotivation_neither : ¬ amotivation.isAutonomous ∧ ¬ amotivation.isControlled := by
  simp [isAutonomous, isControlled]

end MotivationType

/-- Engagement rests on autonomous motivation: if there is any engagement, motivation is
autonomous. -/
def AutonomousEngagement (e : ℝ) (m : MotivationType) : Prop :=
  0 < e → m.isAutonomous

/-! ### Performance is monotone in engagement -/

section Static

variable {ι : Type*} [Fintype ι] {k e e' : ι → ℝ}

/-- Higher engagement gives at least the volume (for nonnegative per-member output `φ (k i)`). -/
theorem volume_mono_engagement {φ : ℝ → ℝ} (hφ : ∀ i, 0 ≤ φ (k i)) (hee' : ∀ i, e i ≤ e' i) :
    volume φ k e ≤ volume φ k e' :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hee' i) (hφ i)

/-- Higher engagement keeps everyone who could carry the domain (capability nonnegative). -/
theorem carriers_mono_engagement {θ : ℝ} (hk : ∀ i, 0 ≤ k i) (hee' : ∀ i, e i ≤ e' i) :
    carriers θ k e ⊆ carriers θ k e' := fun i hi =>
  mem_carriers.mpr ((mem_carriers.mp hi).trans (mul_le_mul_of_nonneg_left (hee' i) (hk i)))

/-- Higher engagement gives at least the frontier (capability nonnegative). -/
theorem frontier_mono_engagement [Nonempty ι] (hk : ∀ i, 0 ≤ k i) (hee' : ∀ i, e i ≤ e' i) :
    frontier k e ≤ frontier k e' :=
  Finset.sup'_le _ _ fun i _ =>
    (mul_le_mul_of_nonneg_left (hee' i) (hk i)).trans (mul_le_frontier k e' i)

end Static

/-! ### Engagement dynamics with two channels -/

/-- Engagement over time: competence-affirming verbal feedback while motivation is autonomous adds
`β`; a controlling reward subtracts `γ`. -/
def engagementPath (β γ e₀ : ℝ) (verbal reward : ℕ → Prop) [DecidablePred verbal]
    [DecidablePred reward] (m : ℕ → MotivationType) : ℕ → ℝ
  | 0 => e₀
  | t + 1 => engagementPath β γ e₀ verbal reward m t
      + (if verbal t ∧ (m t).isAutonomous then β else 0) - (if reward t then γ else 0)

variable {β γ e₀ : ℝ} {verbal reward : ℕ → Prop} [DecidablePred verbal] [DecidablePred reward]
  {m : ℕ → MotivationType}

/-- **SDT2** (one step): in a step without a controlling reward, engagement does not drop
(premise `β ≥ 0`). -/
theorem engagementPath_le_succ (hβ : 0 ≤ β) {t : ℕ} (hr : ¬ reward t) :
    engagementPath β γ e₀ verbal reward m t ≤ engagementPath β γ e₀ verbal reward m (t + 1) := by
  simp only [engagementPath, hr, ↓reduceIte, sub_zero]
  split_ifs <;> linarith

/-- **SDT2**: without controlling rewards, engagement is non-decreasing (the engagement version
of E1). -/
theorem engagementPath_monotone (hβ : 0 ≤ β) (hr : ∀ t, ¬ reward t) :
    Monotone (engagementPath β γ e₀ verbal reward m) :=
  monotone_nat_of_le_succ fun t => engagementPath_le_succ hβ (hr t)

/-- **SDT2** (strict): verbal feedback while motivation stays autonomous, without a controlling
reward, strictly raises engagement when `β > 0`. -/
theorem engagementPath_lt_succ (hβ : 0 < β) {t : ℕ} (hv : verbal t) (ha : (m t).isAutonomous)
    (hr : ¬ reward t) :
    engagementPath β γ e₀ verbal reward m t < engagementPath β γ e₀ verbal reward m (t + 1) := by
  simp only [engagementPath, hr, ↓reduceIte, sub_zero, hv, ha, and_self]
  linarith

/-- **SDT1** (one step): a controlling reward without verbal feedback lowers engagement when
`γ > 0` (premise). -/
theorem engagementPath_succ_lt (hγ : 0 < γ) {t : ℕ} (hr : reward t)
    (hv : ¬ (verbal t ∧ (m t).isAutonomous)) :
    engagementPath β γ e₀ verbal reward m (t + 1) < engagementPath β γ e₀ verbal reward m t := by
  simp only [engagementPath, hr, hv, ↓reduceIte, add_zero]
  linarith

namespace Example

/-- Motivation: identified before the reward, external after it. -/
def mShift (t : ℕ) : MotivationType :=
  if t = 0 then .identified else .external

/-- Engagement `0.8`, a ranked contingent reward at time `0` with `γ = 0.3`, no verbal feedback. -/
def eShift : ℕ → ℝ :=
  engagementPath 0 (3 / 10) (4 / 5) (fun _ => False) (fun t => t = 0) mShift

/-- **SDT1** (explicit numbers): engagement `0.8` resting on identified motivation drops to `0.5`
after a controlling reward, with motivation moved to external; before, engagement is autonomous,
after, it is not. A member of capability `1` facing threshold `0.6` could carry the domain before
and cannot after, so a one-member team loses the domain. -/
theorem sdt1 :
    eShift 0 = 4 / 5 ∧ eShift 1 = 1 / 2 ∧ eShift 1 < eShift 0 ∧
    AutonomousEngagement (eShift 0) (mShift 0) ∧ ¬ AutonomousEngagement (eShift 1) (mShift 1) ∧
    ToleratesLoss 0 (3 / 5) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => eShift 0) ∧
    ¬ ToleratesLoss 0 (3 / 5) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => eShift 1) := by
  have h0 : eShift 0 = 4 / 5 := rfl
  have h1 : eShift 1 = 1 / 2 := by norm_num [eShift, engagementPath]
  refine ⟨h0, h1, by rw [h0, h1]; norm_num, fun _ => by simp [mShift,
    MotivationType.isAutonomous], fun h => ?_, ?_, ?_⟩
  · have := h (by rw [h1]; norm_num)
    simp [mShift, MotivationType.isAutonomous] at this
  · rw [toleratesLoss_iff, h0]
    exact Finset.card_pos.mpr ⟨0, mem_carriers.mpr (by norm_num)⟩
  · rw [toleratesLoss_iff, h1]
    have : carriers (3 / 5) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1 / 2) = ∅ := by
      ext i
      norm_num [mem_carriers]
    rw [this]
    simp

end Example

end RCAS
