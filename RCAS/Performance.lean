import RCAS.Dependence

/-!
# Domain performance and knowledge sharing (extension)

Extension requested by the author (2026-10-04); specification in `docs/PERFORMANCE_SPEC.md`.
Phase 1 and Phase 2 files are not modified.

Team performance is not collapsed into one number. For each domain it has three components:

* **frontier** `F = max_i k i * e i`: the highest level someone on the team actually delivers.
  It is bounded above by the top member's capability, the **ceiling** `C = max_i k i`;
* **volume** `V = ∑ i, e i * φ (k i)`: how much the team produces;
* **stability**: how many members can carry the domain (`carriers`, `N`), equivalently how many
  departures the team tolerates (`ToleratesLoss`).

Knowledge sharing (`KnowledgeSharing`, premises as structure fields): every member other than
the top member `h` catches up toward `h` at rate `η ∈ [0, 1]`; `h` does not fall back, and may
itself learn (mutual learning).

In this model, sharing alone does not raise the ceiling; it raises volume and stability, and
it raises the realized frontier only up to the ceiling. The ceiling rises exactly when the top
member learns. Engagement is held fixed in the monotonicity results to isolate the effect of
sharing; `KnowledgeSharing.eventually_subset_carriers` lets engagement fluctuate above a floor.

## Main results

* `RCAS.frontier_bounds` (PF1), `RCAS.frontier_eq_ceiling_of_engaged` (PF2)
* `RCAS.KnowledgeSharing.ceiling_eq_top` (PS1), `RCAS.KnowledgeSharing.ceiling_const`,
  `RCAS.KnowledgeSharing.frontier_le_initial_ceiling` (PS2),
  `RCAS.KnowledgeSharing.frontier_monotone` (PS3)
* `RCAS.KnowledgeSharing.ceiling_lt_iff` (PM1; `RCAS.rate_le_one_needed` shows `η ≤ 1` is needed)
* `RCAS.KnowledgeSharing.volume_monotone` (PV1), `RCAS.KnowledgeSharing.volume_lt_succ` (PV2),
  `RCAS.KnowledgeSharing.volume_tendsto` (PV3)
* `RCAS.toleratesLoss_iff` (PR1), `RCAS.KnowledgeSharing.card_carriers_monotone` (PR2),
  `RCAS.KnowledgeSharing.eventually_subset_carriers`,
  `RCAS.KnowledgeSharing.eventually_toleratesLoss` (PR3)
* `RCAS.teamPerformance_monotone` (PT1)
* `RCAS.Example.oneExpert_to_distributed` (one expert → distributed expertise)
-/

noncomputable section

namespace RCAS

open Filter Topology

/-! ### The three components, statically -/

section Static

variable {ι : Type*} [Fintype ι]

/-- The volume of output. -/
def volume (φ : ℝ → ℝ) (k e : ι → ℝ) : ℝ :=
  ∑ i, e i * φ (k i)

/-- The members who can carry the domain at threshold `θ`. -/
def carriers (θ : ℝ) (k e : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun i => θ ≤ k i * e i

/-- Stability: whichever `m` members leave, someone who can carry the domain remains. -/
def ToleratesLoss (m : ℕ) (θ : ℝ) (k e : ι → ℝ) : Prop :=
  ∀ L : Finset ι, L.card ≤ m → ∃ i ∉ L, θ ≤ k i * e i

theorem mem_carriers {θ : ℝ} {k e : ι → ℝ} {i : ι} : i ∈ carriers θ k e ↔ θ ≤ k i * e i := by
  simp [carriers]

/-- **PR1** (meaning of stability): the team tolerates the loss of any `m` members if and only if
more than `m` members can carry the domain. -/
theorem toleratesLoss_iff {m : ℕ} {θ : ℝ} {k e : ι → ℝ} :
    ToleratesLoss m θ k e ↔ m < (carriers θ k e).card := by
  classical
  constructor
  · intro h
    by_contra hle
    obtain ⟨i, hi, hθ⟩ := h (carriers θ k e) (not_lt.mp hle)
    exact hi (mem_carriers.mpr hθ)
  · intro h L hL
    obtain ⟨i, hi, hiL⟩ := Finset.exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt hL h)
    exact ⟨i, hiL, mem_carriers.mp hi⟩

variable [Nonempty ι]

/-- The capability ceiling: the top member's capability. -/
def ceiling (k : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty k

/-- The frontier: the highest level someone on the team actually delivers. -/
def frontier (k e : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => k i * e i

theorem le_ceiling (k : ι → ℝ) (i : ι) : k i ≤ ceiling k :=
  Finset.le_sup' k (Finset.mem_univ i)

theorem mul_le_frontier (k e : ι → ℝ) (i : ι) : k i * e i ≤ frontier k e :=
  Finset.le_sup' (fun i => k i * e i) (Finset.mem_univ i)

/-- If `h` is a top member, the ceiling is `h`'s capability. -/
theorem ceiling_eq_of_top {k : ι → ℝ} {h : ι} (htop : ∀ i, k i ≤ k h) : ceiling k = k h :=
  le_antisymm (Finset.sup'_le _ _ fun i _ => htop i) (le_ceiling k h)

/-- With nonnegative capability and engagement at most `1`, the frontier never exceeds the
ceiling. -/
theorem frontier_le_ceiling {k e : ι → ℝ} (hk : ∀ i, 0 ≤ k i) (he1 : ∀ i, e i ≤ 1) :
    frontier k e ≤ ceiling k :=
  Finset.sup'_le _ _ fun i _ => (mul_le_of_le_one_right (hk i) (he1 i)).trans (le_ceiling k i)

/-- **PF1**: the frontier lies between the top member's own effective level `k h * e h` and the
top member's capability `k h`. -/
theorem frontier_bounds {k e : ι → ℝ} {h : ι} (hk : ∀ i, 0 ≤ k i) (he1 : ∀ i, e i ≤ 1)
    (htop : ∀ i, k i ≤ k h) : k h * e h ≤ frontier k e ∧ frontier k e ≤ k h :=
  ⟨mul_le_frontier k e h, (ceiling_eq_of_top htop) ▸ frontier_le_ceiling hk he1⟩

/-- **PF2**: if the top member is fully engaged, the frontier reaches the ceiling. -/
theorem frontier_eq_ceiling_of_engaged {k e : ι → ℝ} {h : ι} (hk : ∀ i, 0 ≤ k i)
    (he1 : ∀ i, e i ≤ 1) (htop : ∀ i, k i ≤ k h) (heh : e h = 1) :
    frontier k e = ceiling k := by
  refine le_antisymm (frontier_le_ceiling hk he1) ?_
  rw [ceiling_eq_of_top htop]
  simpa [heh] using mul_le_frontier k e h

end Static

/-! ### Knowledge sharing -/

/-- Knowledge sharing in one domain toward the top member `h` (premises, as fields). -/
structure KnowledgeSharing {ι : Type*} (k : ℕ → ι → ℝ) (h : ι) (η : ℕ → ι → ℝ) : Prop where
  /-- Every other member catches up toward `h` at rate `η`. -/
  catchUp : ∀ t i, i ≠ h → k (t + 1) i = k t i + η t i * (k t h - k t i)
  /-- The transfer rate is nonnegative. -/
  rate_nonneg : ∀ t i, 0 ≤ η t i
  /-- The transfer rate is at most `1` (no overshooting the top member). -/
  rate_le_one : ∀ t i, η t i ≤ 1
  /-- The top member does not fall back (and may learn: mutual learning). -/
  top_mono : ∀ t, k t h ≤ k (t + 1) h
  /-- `h` is a top member at the start. -/
  top_initial : ∀ i, k 0 i ≤ k 0 h

namespace KnowledgeSharing

variable {ι : Type*} {k : ℕ → ι → ℝ} {h : ι} {η : ℕ → ι → ℝ} (hS : KnowledgeSharing k h η)
include hS

/-- The top member stays a top member. -/
theorem le_top (t : ℕ) : ∀ i, k t i ≤ k t h := by
  induction t with
  | zero => exact hS.top_initial
  | succ t ih =>
    intro i
    by_cases hi : i = h
    · rw [hi]
    · rw [hS.catchUp t i hi]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hS.rate_le_one t i)) (sub_nonneg.mpr (ih i)),
        hS.top_mono t]

/-- Nobody's capability decreases. -/
theorem le_succ (t : ℕ) (i : ι) : k t i ≤ k (t + 1) i := by
  by_cases hi : i = h
  · rw [hi]
    exact hS.top_mono t
  · rw [hS.catchUp t i hi]
    exact le_add_of_nonneg_right (mul_nonneg (hS.rate_nonneg t i) (sub_nonneg.mpr (hS.le_top t i)))

theorem monotone_member (i : ι) : Monotone fun t => k t i :=
  monotone_nat_of_le_succ fun t => hS.le_succ t i

theorem nonneg (hk0 : ∀ i, 0 ≤ k 0 i) (t : ℕ) (i : ι) : 0 ≤ k t i :=
  (hk0 i).trans (hS.monotone_member i (Nat.zero_le t))

omit hS in
/-- With sharing only, the top member's capability stays at its initial value. -/
theorem top_const (hfix : ∀ t, k (t + 1) h = k t h) (t : ℕ) : k t h = k 0 h := by
  induction t with
  | zero => rfl
  | succ t ih => rw [hfix, ih]

/-- With sharing only and a rate bounded below, every member's capability converges to the top
member's. -/
theorem tendsto_top (hfix : ∀ t, k (t + 1) h = k t h) {ηMin : ℝ} (hηMin : 0 < ηMin)
    (hη : ∀ t i, i ≠ h → ηMin ≤ η t i) (i : ι) :
    Tendsto (fun t => k t i) atTop (𝓝 (k 0 h)) := by
  by_cases hi : i = h
  · subst hi
    exact tendsto_const_nhds.congr fun t => (top_const hfix t).symm
  · have hgap : Tendsto (fun t => k t h - k t i) atTop (𝓝 0) :=
      dependence_tendsto_zero_of_timeVarying (p := fun t => η t i)
        (fun t => by rw [hfix, hS.catchUp t i hi]; ring) hηMin (fun t => hη t i hi)
        (fun t => hS.rate_le_one t i)
    have := (tendsto_const_nhds (x := k 0 h)).sub hgap
    rw [sub_zero] at this
    exact this.congr fun t => by rw [top_const hfix t]; ring

section Fintype

variable [Fintype ι]

/-- **PV1** (volume grows): with `φ` monotone and engagement fixed, volume is non-decreasing. -/
theorem volume_monotone {φ : ℝ → ℝ} (hφ : Monotone φ) {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) :
    Monotone fun t => volume φ (k t) e :=
  monotone_nat_of_le_succ fun t =>
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hφ (hS.le_succ t i)) (he0 i)

/-- **PV2** (volume grows strictly): if some engaged member behind the top member learns at a
positive rate, and `φ` is strictly monotone, volume strictly increases. -/
theorem volume_lt_succ {φ : ℝ → ℝ} (hφ : StrictMono φ) {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i)
    {t : ℕ} {i : ι} (hi : i ≠ h) (hη : 0 < η t i) (hgap : k t i < k t h) (hei : 0 < e i) :
    volume φ (k t) e < volume φ (k (t + 1)) e := by
  refine Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left
    (hφ.monotone (hS.le_succ t j)) (he0 j)) ⟨i, Finset.mem_univ i, ?_⟩
  refine mul_lt_mul_of_pos_left (hφ ?_) hei
  rw [hS.catchUp t i hi]
  exact lt_add_of_pos_right _ (mul_pos hη (sub_pos.mpr hgap))

/-- **PV3** (limit of volume): with sharing only, a rate bounded below and `φ` continuous, volume
converges to the volume of a team in which everyone works at the top member's level. -/
theorem volume_tendsto (hfix : ∀ t, k (t + 1) h = k t h) {ηMin : ℝ} (hηMin : 0 < ηMin)
    (hη : ∀ t i, i ≠ h → ηMin ≤ η t i) {φ : ℝ → ℝ} (hφ : Continuous φ) (e : ι → ℝ) :
    Tendsto (fun t => volume φ (k t) e) atTop (𝓝 ((∑ i, e i) * φ (k 0 h))) := by
  rw [Finset.sum_mul]
  exact tendsto_finsetSum _ fun i _ =>
    ((hφ.tendsto _).comp (hS.tendsto_top hfix hηMin hη i)).const_mul (e i)

/-- **PR2** (stability grows): with engagement fixed, whoever can carry the domain keeps being
able to. -/
theorem carriers_mono {θ : ℝ} {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) {t t' : ℕ} (htt' : t ≤ t') :
    carriers θ (k t) e ⊆ carriers θ (k t') e := fun i hi =>
  mem_carriers.mpr ((mem_carriers.mp hi).trans
    (mul_le_mul_of_nonneg_right (hS.monotone_member i htt') (he0 i)))

/-- **PR2**: the number of members who can carry the domain is non-decreasing. -/
theorem card_carriers_monotone {θ : ℝ} {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) :
    Monotone fun t => (carriers θ (k t) e).card :=
  fun _ _ htt' => Finset.card_le_card (hS.carriers_mono he0 htt')

/-- **PR3** (where stability ends up): with sharing only and a rate bounded below, and with
engagement allowed to fluctuate as long as it stays above a floor `eMin i`, eventually
every member with `θ < k 0 h * eMin i` can carry the domain. -/
theorem eventually_subset_carriers (hfix : ∀ t, k (t + 1) h = k t h) (hk0 : ∀ i, 0 ≤ k 0 i)
    {ηMin : ℝ} (hηMin : 0 < ηMin) (hη : ∀ t i, i ≠ h → ηMin ≤ η t i) {e : ℕ → ι → ℝ}
    {eMin : ι → ℝ} (heMin : ∀ t i, eMin i ≤ e t i) (θ : ℝ) :
    ∃ T, ∀ t ≥ T,
      Finset.univ.filter (fun i => θ < k 0 h * eMin i) ⊆ carriers θ (k t) (e t) := by
  have hall : ∀ᶠ t in atTop, ∀ i, θ < k 0 h * eMin i → i ∈ carriers θ (k t) (e t) := by
    refine Filter.eventually_all.mpr fun i => ?_
    by_cases hi : θ < k 0 h * eMin i
    · have hlim : Tendsto (fun t => k t i * eMin i) atTop (𝓝 (k 0 h * eMin i)) :=
        (hS.tendsto_top hfix hηMin hη i).mul_const _
      filter_upwards [hlim.eventually_const_lt hi] with t ht _
      exact mem_carriers.mpr (ht.le.trans
        (mul_le_mul_of_nonneg_left (heMin t i) (hS.nonneg hk0 t i)))
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' hi
  obtain ⟨T, hT⟩ := eventuallyAlways_iff.mpr hall
  exact ⟨T, fun t ht i hi => hT t ht i (Finset.mem_filter.mp hi).2⟩

/-- **PR3**: if more than `m` members satisfy `θ < k 0 h * eMin i`, the team eventually
tolerates the loss of any `m` members. -/
theorem eventually_toleratesLoss (hfix : ∀ t, k (t + 1) h = k t h)
    (hk0 : ∀ i, 0 ≤ k 0 i) {ηMin : ℝ} (hηMin : 0 < ηMin) (hη : ∀ t i, i ≠ h → ηMin ≤ η t i)
    {e : ℕ → ι → ℝ} {eMin : ι → ℝ} (heMin : ∀ t i, eMin i ≤ e t i)
    {θ : ℝ} {m : ℕ} (hm : m < (Finset.univ.filter fun i => θ < k 0 h * eMin i).card) :
    ∃ T, ∀ t ≥ T, ToleratesLoss m θ (k t) (e t) := by
  classical
  obtain ⟨T, hT⟩ := hS.eventually_subset_carriers hfix hk0 hηMin hη heMin θ
  exact ⟨T, fun t ht => toleratesLoss_iff.mpr (hm.trans_le (Finset.card_le_card (hT t ht)))⟩

variable [Nonempty ι]

/-- **PS1**: the ceiling is always the top member's capability. -/
theorem ceiling_eq_top (t : ℕ) : ceiling (k t) = k t h :=
  ceiling_eq_of_top (hS.le_top t)

/-- **PS2** (frontier preservation): with sharing only, the ceiling never changes. -/
theorem ceiling_const (hfix : ∀ t, k (t + 1) h = k t h) (t : ℕ) :
    ceiling (k t) = ceiling (k 0) := by
  rw [hS.ceiling_eq_top, hS.ceiling_eq_top, top_const hfix]

/-- **PS2**: with sharing only, the frontier never exceeds the initial ceiling. -/
theorem frontier_le_initial_ceiling (hfix : ∀ t, k (t + 1) h = k t h) (hk0 : ∀ i, 0 ≤ k 0 i)
    {e : ι → ℝ} (he1 : ∀ i, e i ≤ 1) (t : ℕ) : frontier (k t) e ≤ ceiling (k 0) :=
  hS.ceiling_const hfix t ▸ frontier_le_ceiling (hS.nonneg hk0 t) he1

/-- **PS3**: the realized frontier is non-decreasing (engagement fixed). -/
theorem frontier_monotone {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) :
    Monotone fun t => frontier (k t) e := by
  refine monotone_nat_of_le_succ fun t => Finset.sup'_le _ _ fun i _ => ?_
  exact (mul_le_mul_of_nonneg_right (hS.le_succ t i) (he0 i)).trans (mul_le_frontier _ e i)

/-- **PM1** (mutual learning expands the frontier): the ceiling rises exactly when the top member
learns. -/
theorem ceiling_lt_iff (t : ℕ) : ceiling (k t) < ceiling (k (t + 1)) ↔ k t h < k (t + 1) h := by
  rw [hS.ceiling_eq_top, hS.ceiling_eq_top]

end Fintype

end KnowledgeSharing

/-- The premise `η ≤ 1` is needed: with `η = 2` a member overshoots the top member (its
capability oscillates `0, 2, 0, 2, …`), and the ceiling rises although the top member does not
learn (PM1 fails). -/
theorem rate_le_one_needed :
    ∃ (k : ℕ → Fin 2 → ℝ) (η : ℕ → Fin 2 → ℝ),
      (∀ t i, i ≠ 0 → k (t + 1) i = k t i + η t i * (k t 0 - k t i)) ∧ (∀ t i, 0 ≤ η t i) ∧
      (∀ t, k (t + 1) 0 = k t 0) ∧ (∀ i, k 0 i ≤ k 0 0) ∧ ceiling (k 0) < ceiling (k 1) := by
  refine ⟨fun t i => if i = 0 then 1 else if t % 2 = 0 then 0 else 2, fun _ _ => 2, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro t i hi
    simp only [hi, ↓reduceIte]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · norm_num [h, show (t + 1) % 2 = 1 by omega]
    · norm_num [h, show (t + 1) % 2 = 0 by omega]
  · intros
    norm_num
  · intros
    simp
  · intro i
    by_cases hi : i = 0 <;> simp [hi]
  · rw [ceiling_eq_of_top (h := 0) fun i => by by_cases hi : i = 0 <;> simp [hi]]
    refine lt_of_lt_of_le ?_ (le_ceiling _ 1)
    norm_num

/-! ### The team as a whole (PT1) -/

section Team

variable {ι Δ : Type*} [Fintype ι] [Nonempty ι] [Fintype Δ]

/-- Team performance: a weighted sum over domains of a score of (frontier, volume, number of
carriers). -/
def teamPerformance (w : Δ → ℝ) (Ψ : ℝ → ℝ → ℕ → ℝ) (F V : Δ → ℝ) (N : Δ → ℕ) : ℝ :=
  ∑ d, w d * Ψ (F d) (V d) (N d)

/-- **PT1**: if knowledge sharing works in every domain (engagement fixed), the weights are
nonnegative, and the score `Ψ` is monotone in each argument, team performance is non-decreasing.
-/
theorem teamPerformance_monotone {k : ℕ → ι → Δ → ℝ} {h : Δ → ι} {η : ℕ → ι → Δ → ℝ}
    (hS : ∀ d, KnowledgeSharing (fun t i => k t i d) (h d) (fun t i => η t i d))
    {e : ι → Δ → ℝ} (he0 : ∀ i d, 0 ≤ e i d) {φ : Δ → ℝ → ℝ} (hφ : ∀ d, Monotone (φ d))
    (θ : Δ → ℝ) {w : Δ → ℝ} (hw : ∀ d, 0 ≤ w d) {Ψ : ℝ → ℝ → ℕ → ℝ}
    (hΨ : ∀ f f' v v' n n', f ≤ f' → v ≤ v' → n ≤ n' → Ψ f v n ≤ Ψ f' v' n') :
    Monotone fun t => teamPerformance w Ψ
      (fun d => frontier (fun i => k t i d) (fun i => e i d))
      (fun d => volume (φ d) (fun i => k t i d) (fun i => e i d))
      (fun d => (carriers (θ d) (fun i => k t i d) (fun i => e i d)).card) := by
  intro t t' htt'
  refine Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hΨ _ _ _ _ _ _ ?_ ?_ ?_) (hw d)
  · exact (hS d).frontier_monotone (fun i => he0 i d) htt'
  · exact (hS d).volume_monotone (hφ d) (fun i => he0 i d) htt'
  · exact (hS d).card_carriers_monotone (fun i => he0 i d) htt'

end Team

/-! ### Example: from one expert to distributed expertise -/

namespace Example

/-- Member `0` is the expert; the others start at `0` and close half of the gap each step. -/
def kShare (t : ℕ) (i : Fin 3) : ℝ :=
  if i = 0 then 1 else 1 - (1 / 2) ^ t

theorem kShare_sharing : KnowledgeSharing kShare 0 (fun _ _ => 1 / 2) where
  catchUp t i hi := by
    simp only [kShare, hi, ↓reduceIte, pow_succ]
    ring
  rate_nonneg _ _ := by norm_num
  rate_le_one _ _ := by norm_num
  top_mono _ := by simp [kShare]
  top_initial i := by by_cases hi : i = 0 <;> simp [kShare, hi]

theorem kShare_fix : ∀ t, kShare (t + 1) 0 = kShare t 0 := fun _ => by simp [kShare]

/-- One expert (`t = 0`) versus one step of sharing (`t = 1`), all fully engaged, threshold
`1/2`, `φ = id`: the frontier stays at `1`, volume goes from `1` to `2`, the number of carriers
goes from `1` to `3`, and the team goes from not tolerating the loss of one member to
tolerating it. -/
theorem oneExpert_to_distributed :
    frontier (kShare 0) (fun _ => 1) = 1 ∧ frontier (kShare 1) (fun _ => 1) = 1 ∧
    volume id (kShare 0) (fun _ => 1) = 1 ∧ volume id (kShare 1) (fun _ => 1) = 2 ∧
    (carriers (1 / 2) (kShare 0) (fun _ => 1)).card = 1 ∧
    (carriers (1 / 2) (kShare 1) (fun _ => 1)).card = 3 ∧
    ¬ ToleratesLoss 1 (1 / 2) (kShare 0) (fun _ => 1) ∧
    ToleratesLoss 1 (1 / 2) (kShare 1) (fun _ => 1) := by
  have hk0 : ∀ i, 0 ≤ kShare 0 i := fun i => by by_cases hi : i = 0 <;> simp [kShare, hi]
  have hF : ∀ t, frontier (kShare t) (fun _ => 1) = 1 := fun t => by
    rw [frontier_eq_ceiling_of_engaged (h := 0) (kShare_sharing.nonneg hk0 t)
      (fun _ => le_rfl) (kShare_sharing.le_top t) rfl, kShare_sharing.ceiling_eq_top]
    simp [kShare]
  have hc0 : carriers (1 / 2) (kShare 0) (fun _ => 1) = {0} := by
    ext i
    fin_cases i <;> norm_num [mem_carriers, kShare]
  have hc1 : carriers (1 / 2) (kShare 1) (fun _ => 1) = Finset.univ := by
    ext i
    fin_cases i <;> norm_num [mem_carriers, kShare]
  refine ⟨hF 0, hF 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [volume, kShare]
  · norm_num [volume, Fin.sum_univ_three, kShare]
  · rw [hc0, Finset.card_singleton]
  · rw [hc1, Finset.card_univ, Fintype.card_fin]
  · rw [toleratesLoss_iff, hc0, Finset.card_singleton]
    exact lt_irrefl 1
  · rw [toleratesLoss_iff, hc1, Finset.card_univ, Fintype.card_fin]
    norm_num

/-- PS2 in the example: sharing alone never moves the ceiling. -/
example (t : ℕ) : ceiling (kShare t) = 1 := by
  rw [kShare_sharing.ceiling_const kShare_fix, kShare_sharing.ceiling_eq_top]
  simp [kShare]

/-- PV3 in the example: volume converges to `3 · 1`, everyone at the expert's level. -/
example : Tendsto (fun t => volume id (kShare t) (fun _ => 1)) atTop (𝓝 3) := by
  have := kShare_sharing.volume_tendsto kShare_fix (ηMin := 1 / 2) (by norm_num)
    (fun _ _ _ => le_rfl) continuous_id (fun _ => 1)
  norm_num [kShare] at this
  exact this

/-- PR3 in the example: eventually the team tolerates the loss of any two members, even if
engagement fluctuates, as long as it stays at least `3/4`. -/
example {e : ℕ → Fin 3 → ℝ} (he : ∀ t i, 3 / 4 ≤ e t i) :
    ∃ T, ∀ t ≥ T, ToleratesLoss 2 (1 / 2) (kShare t) (e t) := by
  refine kShare_sharing.eventually_toleratesLoss kShare_fix
    (fun i => by by_cases hi : i = 0 <;> simp [kShare, hi]) (ηMin := 1 / 2) (by norm_num)
    (fun _ _ _ => le_rfl) he ?_
  have : (Finset.univ.filter fun i : Fin 3 => (1 / 2 : ℝ) < kShare 0 0 * (3 / 4)) =
      Finset.univ := by
    ext i
    norm_num [kShare]
  rw [this, Finset.card_univ, Fintype.card_fin]
  norm_num

end Example

end RCAS
