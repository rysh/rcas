import RCAS.Observable
import RCAS.Motivation

/-!
# Why the model has no profit allocation

The author's model has no allocation of profit (author's decision, 2026-10-05), for two reasons:

1. an allocation undermines engagement however large it is;
2. profit fluctuates, so an allocation commensurate with effort cannot always be made.

Reason 2 is a theorem: under budget balance, everyone can receive at least the amount
commensurate with their effort exactly when the profit covers the total of those amounts; at any
time the profit falls short, every allocation rule leaves someone short (NA1–NA3). With
effort-proportional sharing (OB2), pay is not determined by effort alone but follows the profit
(NA4).

Reason 1 is a **premise**: the engagement dynamics of `RCAS.Motivation` are generalized so that an
allocation of size `x > 0` lowers engagement by `γ x ≥ γMin > 0`, whatever `x` is (NA5–NA7). The
results only restate this premise in the dynamics; whether it holds is empirical.

`RCAS.Observable` is kept as a contrast with Holmström's framework; it is outside the author's
model.

## Main results

* `RCAS.exists_commensurate_iff` (NA1), `RCAS.exists_short_of_profit_lt` (NA2),
  `RCAS.exists_neg_of_loss`
* `RCAS.exists_commensurate_path_iff` (NA3)
* `RCAS.proportionalShare_ne_of_profit_ne` (NA4)
* `RCAS.Example.fluctuating_profit`
* `RCAS.engagementPathSized_succ_le` (NA5), `RCAS.engagementPathSized_le_engagementPath` (NA6),
  `RCAS.engagementPathSized_monotone_of_no_allocation` (NA7)
-/

noncomputable section

namespace RCAS

/-! ### Reason 2: profit fluctuates -/

section Profit

variable {ι : Type*} [Fintype ι]

/-- **NA2**: under budget balance, if the profit is below the total of the commensurate amounts,
some member receives less than their commensurate amount, whatever the allocation rule. -/
theorem exists_short_of_profit_lt {s c : ι → ℝ} {q : ℝ} (hbb : ∑ i, s i = q)
    (hq : q < ∑ i, c i) : ∃ i, s i < c i := by
  by_contra h
  push Not at h
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  linarith

/-- Under budget balance, a loss makes someone's allocation negative. -/
theorem exists_neg_of_loss {s : ι → ℝ} {q : ℝ} (hbb : ∑ i, s i = q) (hq : q < 0) :
    ∃ i, s i < 0 := by
  obtain ⟨i, hi⟩ := exists_short_of_profit_lt (c := fun _ => 0) hbb (by simpa using hq)
  exact ⟨i, hi⟩

variable [Nonempty ι]

/-- **NA1**: a budget-balanced allocation giving everyone at least their commensurate amount
exists exactly when the profit covers the total of the commensurate amounts. -/
theorem exists_commensurate_iff (c : ι → ℝ) (q : ℝ) :
    (∃ s : ι → ℝ, ∑ i, s i = q ∧ ∀ i, c i ≤ s i) ↔ ∑ i, c i ≤ q := by
  constructor
  · rintro ⟨s, hbb, hs⟩
    rw [← hbb]
    exact Finset.sum_le_sum fun i _ => hs i
  · intro hq
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    refine ⟨fun i => c i + (q - ∑ j, c j) / Fintype.card ι, ?_, fun i => ?_⟩
    · rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
      ring
    · exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hq) hcard.le)

/-- **NA3**: over time, a sequence of budget-balanced allocations giving everyone at least their
commensurate amount at every time exists exactly when the profit covers the commensurate total at
every time. If the profit ever falls short, no allocation rule can keep allocations commensurate
at that time. -/
theorem exists_commensurate_path_iff (c : ℕ → ι → ℝ) (q : ℕ → ℝ) :
    (∃ s : ℕ → ι → ℝ, ∀ t, ∑ i, s t i = q t ∧ ∀ i, c t i ≤ s t i) ↔
      ∀ t, ∑ i, c t i ≤ q t := by
  constructor
  · rintro ⟨s, hs⟩ t
    exact (exists_commensurate_iff (c t) (q t)).mp ⟨s t, hs t⟩
  · intro hq
    choose s hs using fun t => (exists_commensurate_iff (c t) (q t)).mpr (hq t)
    exact ⟨s, hs⟩

end Profit

/-- **NA4**: with effort-proportional sharing, the same efforts receive different pay when the
profit differs: pay follows the profit, not effort alone. -/
theorem proportionalShare_ne_of_profit_ne {e : Fin 2 → ℝ} {i : Fin 2} (hei : 0 < e i)
    (he : 0 < e 0 + e 1) {q₁ q₂ : ℝ} (hq : q₁ ≠ q₂) :
    proportionalShare i e q₁ ≠ proportionalShare i e q₂ := by
  unfold proportionalShare
  intro h
  exact hq (mul_left_cancel₀ (div_pos hei he).ne' h)

namespace Example

/-- Two members, each with commensurate amount `3`. The profit is `10` at time `0` and `4` at
time `1`. At time `0` a commensurate allocation exists; at time `1` every budget-balanced
allocation leaves someone below `3`. -/
theorem fluctuating_profit :
    (∃ s : Fin 2 → ℝ, ∑ i, s i = 10 ∧ ∀ i, (3 : ℝ) ≤ s i) ∧
      ∀ s : Fin 2 → ℝ, ∑ i, s i = 4 → ∃ i, s i < 3 := by
  refine ⟨(exists_commensurate_iff (fun _ => (3 : ℝ)) 10).mpr (by norm_num), fun s hs => ?_⟩
  exact exists_short_of_profit_lt (c := fun _ => 3) hs (by norm_num)

end Example

/-! ### Reason 1: undermining whatever the size (premise) -/

/-- Engagement with an allocation of size `x t` at time `t` (`x t = 0`: no allocation): verbal
feedback while motivation is autonomous adds `β`; an allocation of size `x > 0` subtracts
`γ x`. -/
def engagementPathSized (β e₀ : ℝ) (γ : ℝ → ℝ) (verbal : ℕ → Prop) [DecidablePred verbal]
    (m : ℕ → MotivationType) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => e₀
  | t + 1 => engagementPathSized β e₀ γ verbal m x t
      + (if verbal t ∧ (m t).isAutonomous then β else 0) - (if 0 < x t then γ (x t) else 0)

variable {β e₀ γMin : ℝ} {γ : ℝ → ℝ} {verbal : ℕ → Prop} [DecidablePred verbal]
  {m : ℕ → MotivationType} {x : ℕ → ℝ}

/-- **NA5**: with the premise `γ x ≥ γMin` for every size `x > 0`, an allocation of any size at a
time without verbal feedback lowers engagement by at least `γMin`. -/
theorem engagementPathSized_succ_le (hγ : ∀ y, 0 < y → γMin ≤ γ y) {t : ℕ} (hx : 0 < x t)
    (hv : ¬ (verbal t ∧ (m t).isAutonomous)) :
    engagementPathSized β e₀ γ verbal m x (t + 1) ≤
      engagementPathSized β e₀ γ verbal m x t - γMin := by
  simp only [engagementPathSized, hv, hx, ↓reduceIte, add_zero]
  linarith [hγ (x t) hx]

/-- **NA6**: with the same premise, engagement under allocations of any sizes stays at or below
engagement under a uniform drop of `γMin` per allocation. Making allocations larger never makes
the drop smaller than `γMin`. -/
theorem engagementPathSized_le_engagementPath (hγ : ∀ y, 0 < y → γMin ≤ γ y) (t : ℕ) :
    engagementPathSized β e₀ γ verbal m x t ≤
      engagementPath β γMin e₀ verbal (fun t => 0 < x t) m t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    simp only [engagementPathSized, engagementPath]
    by_cases hx : 0 < x t
    · simp only [hx, ↓reduceIte]
      linarith [hγ (x t) hx]
    · simp only [hx, ↓reduceIte]
      linarith

/-- **NA7**: without any allocation, verbal feedback alone never lowers engagement (as SDT2). -/
theorem engagementPathSized_monotone_of_no_allocation (hβ : 0 ≤ β) (hx : ∀ t, x t ≤ 0) :
    Monotone (engagementPathSized β e₀ γ verbal m x) := by
  refine monotone_nat_of_le_succ fun t => ?_
  simp only [engagementPathSized, not_lt.mpr (hx t), ↓reduceIte, sub_zero]
  split_ifs <;> linarith

end RCAS
