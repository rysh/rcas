import RCAS.Basic

/-!
# Decay of dependence on the manager (§4.7)

`D (t+1) = (1 - p) * D t`, where `p` is the probability that the team internalizes the
principle when a question is answered by returning it to the principle.

The recurrence is taken as a hypothesis on an arbitrary sequence `D : ℕ → ℝ`. That `p > 0` holds
in a real organization is a premise (see `docs/EMPIRICAL.md`).

## Main results

* `RCAS.dependence_eq` (D1, closed form)
* `RCAS.dependence_strictAnti` (D2, with `p < 1` and `0 < D 0`)
* `RCAS.dependence_succ_lt` (D2, the one-step form with `0 < D t`)
* `RCAS.dependence_tendsto_zero` (D3)
* `RCAS.dependence_eventually_le` (D4)
* `RCAS.dependence_tendsto_zero_of_timeVarying`, `RCAS.dependence_eventually_le_of_timeVarying`
  (D5, with `p t ≤ 1`; `RCAS.dependence_timeVarying_needs_upper_bound` shows an upper bound is
  needed)
-/

namespace RCAS

open Filter Topology

/-- A real sequence tending to `0` is eventually at most any `δ > 0`. -/
theorem eventuallyAlways_le_of_tendsto_zero {D : ℕ → ℝ} (hD : Tendsto D atTop (𝓝 0)) {δ : ℝ}
    (hδ : 0 < δ) : EventuallyAlways (fun t => D t ≤ δ) :=
  eventuallyAlways_iff.mpr (hD.eventually (Iic_mem_nhds hδ))

variable {p : ℝ} {D : ℕ → ℝ}

/-- **D1** (closed form): `D t = (1 - p)^t * D 0`. -/
theorem dependence_eq (hD : ∀ t, D (t + 1) = (1 - p) * D t) (t : ℕ) :
    D t = (1 - p) ^ t * D 0 := by
  induction t with
  | zero => simp
  | succ t ih => rw [hD, ih, pow_succ]; ring

/-- **D2** (one-step form): if `p > 0` and current dependence is positive, it strictly drops. -/
theorem dependence_succ_lt (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp : 0 < p) {t : ℕ}
    (hDt : 0 < D t) : D (t + 1) < D t := by
  rw [hD]
  nlinarith

/-- With `p < 1` and `D 0 > 0`, dependence stays positive. -/
theorem dependence_pos (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp1 : p < 1) (hD0 : 0 < D 0)
    (t : ℕ) : 0 < D t := by
  rw [dependence_eq hD]
  exact mul_pos (pow_pos (by linarith) t) hD0

/-- **D2** (strict decrease): with `0 < p < 1` and `D 0 > 0`, dependence is strictly
decreasing. Both `p < 1` and `D 0 > 0` are needed; see `RCAS.dependence_strictAnti_needs`. -/
theorem dependence_strictAnti (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp : 0 < p) (hp1 : p < 1)
    (hD0 : 0 < D 0) : StrictAnti D :=
  strictAnti_nat_of_succ_lt fun _ => dependence_succ_lt hD hp (dependence_pos hD hp1 hD0 _)

/-- The extra hypotheses of D2 are needed: with `p = 1` the sequence reaches `0` and stays
there, and with `D 0 = 0` it is constant. -/
theorem dependence_strictAnti_needs :
    (∃ D : ℕ → ℝ, (∀ t, D (t + 1) = (1 - 1) * D t) ∧ 0 < D 0 ∧ ¬ StrictAnti D) ∧
    (∃ D : ℕ → ℝ, (∀ t, D (t + 1) = (1 - (1 / 2 : ℝ)) * D t) ∧ D 0 = 0 ∧ ¬ StrictAnti D) := by
  refine ⟨⟨fun t => if t = 0 then 1 else 0, fun t => by simp, by simp, fun h => ?_⟩,
    ⟨fun _ => 0, fun _ => by simp, rfl, fun h => ?_⟩⟩
  · have := h (show 1 < 2 by norm_num)
    simp at this
  · exact lt_irrefl _ (h (show 0 < 1 by norm_num))

/-- **D3** (limit): with `0 < p ≤ 1`, dependence tends to `0`. -/
theorem dependence_tendsto_zero (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp : 0 < p)
    (hp1 : p ≤ 1) : Tendsto D atTop (𝓝 0) := by
  have hpow : Tendsto (fun t : ℕ => (1 - p) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have := hpow.mul_const (D 0)
  rw [zero_mul] at this
  exact this.congr fun t => (dependence_eq hD t).symm

/-- **D4** (below any threshold in finite time): for every `δ > 0` there is `T` with
`D t ≤ δ` for all `t ≥ T`. -/
theorem dependence_eventually_le (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp : 0 < p)
    (hp1 : p ≤ 1) {δ : ℝ} (hδ : 0 < δ) : ∃ T, ∀ t ≥ T, D t ≤ δ :=
  eventuallyAlways_le_of_tendsto_zero (dependence_tendsto_zero hD hp hp1) hδ

/-! ### Time-varying internalization probability (D5) -/

/-- **D5**: if `p t` varies in time with `0 < pMin ≤ p t ≤ 1`, dependence still tends to `0`. -/
theorem dependence_tendsto_zero_of_timeVarying {p : ℕ → ℝ} {pMin : ℝ}
    (hD : ∀ t, D (t + 1) = (1 - p t) * D t) (hpMin : 0 < pMin) (hp : ∀ t, pMin ≤ p t)
    (hp1 : ∀ t, p t ≤ 1) : Tendsto D atTop (𝓝 0) := by
  have hbound : ∀ t, |D t| ≤ (1 - pMin) ^ t * |D 0| := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hD, abs_mul, abs_of_nonneg (by linarith [hp1 t]), pow_succ]
      have h1 : 1 - p t ≤ 1 - pMin := by linarith [hp t]
      have h2 : 0 ≤ 1 - p t := by linarith [hp1 t]
      calc (1 - p t) * |D t| ≤ (1 - pMin) * ((1 - pMin) ^ t * |D 0|) :=
            mul_le_mul h1 ih (abs_nonneg _) (by linarith [hp 0, hp1 0])
        _ = (1 - pMin) ^ t * (1 - pMin) * |D 0| := by ring
  have hpow : Tendsto (fun t : ℕ => (1 - pMin) ^ t * |D 0|) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - pMin)
      (by linarith [hp 0, hp1 0]) (by linarith)).mul_const |D 0|
    rwa [zero_mul] at this
  exact squeeze_zero_norm hbound hpow

/-- **D5** (below any threshold in finite time, time-varying `p`). -/
theorem dependence_eventually_le_of_timeVarying {p : ℕ → ℝ} {pMin : ℝ}
    (hD : ∀ t, D (t + 1) = (1 - p t) * D t) (hpMin : 0 < pMin) (hp : ∀ t, pMin ≤ p t)
    (hp1 : ∀ t, p t ≤ 1) {δ : ℝ} (hδ : 0 < δ) : ∃ T, ∀ t ≥ T, D t ≤ δ :=
  eventuallyAlways_le_of_tendsto_zero
    (dependence_tendsto_zero_of_timeVarying hD hpMin hp hp1) hδ

/-- The upper bound `p t ≤ 1` (carried over from D3) cannot simply be dropped in D5: with
`p t = 3` the lower bound `p t ≥ 1/2` holds, but `D t = (-2)^t` does not tend to `0`. -/
theorem dependence_timeVarying_needs_upper_bound :
    ∃ (p D : ℕ → ℝ), (∀ t, D (t + 1) = (1 - p t) * D t) ∧ (∀ t, 1 / 2 ≤ p t) ∧
      ¬ Tendsto D atTop (𝓝 0) := by
  refine ⟨fun _ => 3, fun t => (-2) ^ t, fun t => by dsimp only; rw [pow_succ]; ring,
    fun _ => by norm_num, fun h => ?_⟩
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (h.eventually (Metric.ball_mem_nhds 0 one_pos))
  have h1 := hT T le_rfl
  rw [Real.dist_eq, sub_zero, abs_pow, abs_neg, abs_two] at h1
  exact absurd h1 (not_lt.mpr (one_le_pow₀ one_le_two))

namespace Example

/-- Halving dependence (`p = 1/2`) from `D 0 = 1`: the recurrence holds, and D2 applies. -/
example : StrictAnti fun t : ℕ => (1 / 2 : ℝ) ^ t :=
  dependence_strictAnti (p := 1 / 2) (fun t => by rw [pow_succ]; ring) (by norm_num)
    (by norm_num) (by norm_num)

end Example

end RCAS
