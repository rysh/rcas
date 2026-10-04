import RCAS.Basic

/-!
# Distribution of capabilities (§4.6)

Capability matrix `k : ι → κ → ℝ` (agent `i`, requirement `j`), thresholds `θ : κ → ℝ`.

* collective cover: every requirement is met by someone, `∀ j, ∃ i, θ j ≤ k i j`;
* super-manager: someone meets every requirement, `∃ i, ∀ j, θ j ≤ k i j`.

## Main results

* `RCAS.SuperManager.collectiveCover` (P6a)
* `RCAS.Example.cover_without_superManager` (P6b)
* `RCAS.hall_iff_exists_assignment`, `RCAS.hall_iff_exists_assignment_capOf` (P7)
* `RCAS.diffusion_monotone`, `RCAS.diffusion_cover_preserved` (K1, with the added hypothesis
  `k 0 ≤ 1`; `RCAS.diffusion_needs_le_one` shows it is needed)
* `RCAS.cover_without_of_redundant`, `RCAS.Example.concentrated_cover_breaks` (K2)
-/

namespace RCAS

variable {ι κ : Type*}

/-- Collective cover: every requirement is met by some agent. -/
def CollectiveCover (k : ι → κ → ℝ) (θ : κ → ℝ) : Prop :=
  ∀ j, ∃ i, θ j ≤ k i j

/-- Super-manager: a single agent meets every requirement. -/
def SuperManager (k : ι → κ → ℝ) (θ : κ → ℝ) : Prop :=
  ∃ i, ∀ j, θ j ≤ k i j

/-- **P6a**: a super-manager gives collective cover. -/
theorem SuperManager.collectiveCover {k : ι → κ → ℝ} {θ : κ → ℝ} (h : SuperManager k θ) :
    CollectiveCover k θ := by
  obtain ⟨i, hi⟩ := h
  exact fun j => ⟨i, hi j⟩

/-- Collective cover is monotone in the capability matrix. -/
theorem CollectiveCover.mono {k k' : ι → κ → ℝ} {θ : κ → ℝ} (h : CollectiveCover k θ)
    (hk : ∀ i j, k i j ≤ k' i j) : CollectiveCover k' θ := by
  intro j
  obtain ⟨i, hi⟩ := h j
  exact ⟨i, hi.trans (hk i j)⟩

/-! ### One agent per requirement: Hall's condition (P7) -/

section Hall

/-- **P7**: distinct agents can be assigned to all requirements (each to one they can carry)
if and only if Hall's condition holds. Direct application of Hall's marriage theorem. -/
theorem hall_iff_exists_assignment [DecidableEq ι] (cap : κ → Finset ι) :
    (∀ s : Finset κ, s.card ≤ (s.biUnion cap).card) ↔
      ∃ f : κ → ι, Function.Injective f ∧ ∀ j, f j ∈ cap j :=
  Finset.all_card_le_biUnion_card_iff_exists_injective cap

variable [Fintype ι]

/-- The agents able to carry requirement `j`. -/
noncomputable def capOf (k : ι → κ → ℝ) (θ : κ → ℝ) (j : κ) : Finset ι :=
  Finset.univ.filter fun i => θ j ≤ k i j

theorem mem_capOf {k : ι → κ → ℝ} {θ : κ → ℝ} {i : ι} {j : κ} :
    i ∈ capOf k θ j ↔ θ j ≤ k i j := by
  simp [capOf]

variable [DecidableEq ι]

/-- **P7** in terms of the capability matrix. -/
theorem hall_iff_exists_assignment_capOf (k : ι → κ → ℝ) (θ : κ → ℝ) :
    (∀ s : Finset κ, s.card ≤ (s.biUnion (capOf k θ)).card) ↔
      ∃ f : κ → ι, Function.Injective f ∧ ∀ j, θ j ≤ k (f j) j := by
  rw [hall_iff_exists_assignment]
  simp only [mem_capOf]

/-- Hall's condition implies collective cover. -/
theorem collectiveCover_of_hall {k : ι → κ → ℝ} {θ : κ → ℝ}
    (h : ∀ s : Finset κ, s.card ≤ (s.biUnion (capOf k θ)).card) : CollectiveCover k θ := by
  obtain ⟨f, -, hf⟩ := (hall_iff_exists_assignment_capOf k θ).mp h
  exact fun j => ⟨f j, hf j⟩

end Hall

/-! ### Diffusion of capability (K1) -/

section Diffusion

variable {η : ℝ} {L : ℕ → ι → κ → ℝ} {k : ℕ → ι → κ → ℝ}

/-- Under the diffusion `k (t+1) = min 1 (k t + η L t)`, capability stays at most `1`. -/
theorem diffusion_le_one (hk : ∀ t i j, k (t + 1) i j = min 1 (k t i j + η * L t i j))
    (hk0 : ∀ i j, k 0 i j ≤ 1) (t : ℕ) (i : ι) (j : κ) : k t i j ≤ 1 := by
  cases t with
  | zero => exact hk0 i j
  | succ t => rw [hk]; exact min_le_left _ _

/-- **K1** (monotonicity of diffusion): with `0 ≤ η`, `0 ≤ L` and the added hypothesis
`k 0 ≤ 1`, every entry of the capability matrix is non-decreasing in time. -/
theorem diffusion_monotone (hk : ∀ t i j, k (t + 1) i j = min 1 (k t i j + η * L t i j))
    (hη : 0 ≤ η) (hL : ∀ t i j, 0 ≤ L t i j) (hk0 : ∀ i j, k 0 i j ≤ 1) (i : ι) (j : κ) :
    Monotone fun t => k t i j := by
  refine monotone_nat_of_le_succ fun t => ?_
  rw [hk]
  exact le_min (diffusion_le_one hk hk0 t i j)
    (le_add_of_nonneg_right (mul_nonneg hη (hL t i j)))

/-- **K1** (cover is preserved): once collective cover holds, it holds at all later times. -/
theorem diffusion_cover_preserved (hk : ∀ t i j, k (t + 1) i j = min 1 (k t i j + η * L t i j))
    (hη : 0 ≤ η) (hL : ∀ t i j, 0 ≤ L t i j) (hk0 : ∀ i j, k 0 i j ≤ 1) {θ : κ → ℝ} {t : ℕ}
    (hcov : CollectiveCover (k t) θ) {t' : ℕ} (htt' : t ≤ t') : CollectiveCover (k t') θ :=
  hcov.mono fun i j => diffusion_monotone hk hη hL hk0 i j htt'

/-- The added hypothesis `k 0 ≤ 1` is needed for K1: starting above the cap, the first step
lowers capability, and a cover at a threshold above `1` is lost. -/
theorem diffusion_needs_le_one :
    ∃ (k : ℕ → Unit → Unit → ℝ) (L : ℕ → Unit → Unit → ℝ) (θ : Unit → ℝ),
      (∀ t i j, k (t + 1) i j = min 1 (k t i j + 0 * L t i j)) ∧ (∀ t i j, 0 ≤ L t i j) ∧
      ¬ Monotone (fun t => k t () ()) ∧ CollectiveCover (k 0) θ ∧ ¬ CollectiveCover (k 1) θ := by
  refine ⟨fun t _ _ => if t = 0 then 2 else 1, fun _ _ _ => 0, fun _ => 2, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _ _
    dsimp only
    split_ifs <;> norm_num at *
  · exact fun _ _ _ => le_rfl
  · intro h
    have := h (Nat.zero_le 1)
    norm_num at this
  · exact fun _ => ⟨(), by norm_num⟩
  · intro h
    obtain ⟨_, hi⟩ := h ()
    norm_num at hi

end Diffusion

/-! ### Losing one agent (K2) -/

/-- **K2**: if every requirement can be carried by at least two distinct agents, collective
cover survives the removal of any one agent. -/
theorem cover_without_of_redundant {k : ι → κ → ℝ} {θ : κ → ℝ}
    (h : ∀ j, ∃ i i', i ≠ i' ∧ θ j ≤ k i j ∧ θ j ≤ k i' j) (i₀ : ι) :
    CollectiveCover (fun i : {i // i ≠ i₀} => k i) θ := by
  intro j
  obtain ⟨i, i', hne, hi, hi'⟩ := h j
  by_cases h₀ : i = i₀
  · exact ⟨⟨i', fun h' => hne (h₀.trans h'.symm)⟩, hi'⟩
  · exact ⟨⟨i, h₀⟩, hi⟩

namespace Example

/-- Two agents, two requirements, identity capability matrix. -/
def kId : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 1 else 0

/-- **P6b**: collective cover without a super-manager. Nobody needs to hold all of the
manager's capabilities. -/
theorem cover_without_superManager :
    CollectiveCover kId (fun _ => 1) ∧ ¬ SuperManager kId (fun _ => 1) := by
  refine ⟨fun j => ⟨j, by simp [kId]⟩, ?_⟩
  rintro ⟨i, hi⟩
  fin_cases i
  · have := hi 1
    norm_num [kId] at this
  · have := hi 0
    norm_num [kId] at this

/-- The converse of P6a fails. -/
theorem cover_not_imp_superManager :
    ¬ ∀ (k : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ), CollectiveCover k θ → SuperManager k θ :=
  fun h => cover_without_superManager.2 (h _ _ cover_without_superManager.1)

/-- A concentrated system: agent `0` carries every requirement, agent `1` none. -/
def kConc : Fin 2 → Fin 2 → ℝ := fun i _ => if i = 0 then 1 else 0

/-- **K2** (concentrated case): cover holds, but removing agent `0` breaks it. -/
theorem concentrated_cover_breaks :
    CollectiveCover kConc (fun _ => 1) ∧
      ¬ CollectiveCover (fun i : {i // i ≠ (0 : Fin 2)} => kConc i) (fun _ => 1) := by
  refine ⟨fun _ => ⟨0, by simp [kConc]⟩, fun h => ?_⟩
  obtain ⟨⟨i, hi⟩, hcov⟩ := h 0
  norm_num [kConc, hi] at hcov

/-- Four agents, two requirements; agents `0, 2` carry requirement `0`, agents `1, 3` carry
requirement `1`. -/
def kDouble : Fin 4 → Fin 2 → ℝ := fun i j => if i.val % 2 = j.val then 1 else 0

/-- **K2** (redundant case): each requirement has two carriers, and cover survives the loss of
anyone. -/
example (i₀ : Fin 4) : CollectiveCover (fun i : {i // i ≠ i₀} => kDouble i) (fun _ => 1) := by
  refine cover_without_of_redundant (fun j => ?_) i₀
  fin_cases j
  · exact ⟨0, 2, by decide, by simp [kDouble], by simp [kDouble]⟩
  · exact ⟨1, 3, by decide, by simp [kDouble], by simp [kDouble]⟩

end Example

end RCAS
