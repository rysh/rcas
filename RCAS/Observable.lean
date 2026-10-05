import RCAS.Basic

/-!
# Observable effort and the moral-hazard premise (survey addition §1)

**Position.** The author's model has no allocation of profit (author's decision, 2026-10-05).
This file is kept only as a contrast with Holmström's framework and is outside the author's
model; the reasons for having no allocation are formalized in `RCAS.NoAllocation`.

Holmström (1982) assumes that individual effort is unobservable and only the joint output is
observable, so that a sharing rule can depend on the output only. When the planning (who does
what) and the daily stand-up (what each did) make individual contributions visible, a sharing
rule may refer to individual effort. This file formalizes only that the *premise* fails; it does
not formalize Holmström's theorem, and it does not claim that an efficient equilibrium is
reached.

The specification's `OutputOnlyReward` is stated for rules `s : ι → ℝ → ℝ`, which can only depend
on the output; for such rules it holds vacuously (`RCAS.outputOnlyReward_trivial`). For rules that
may refer to the effort profile, `s : ι → (ι → ℝ) → ℝ → ℝ`, Holmström's premise is `OutputOnly`.

## Main results

* `RCAS.outputOnlyReward_trivial` (the specification's premise is vacuous on its type)
* `RCAS.not_outputOnly_of_effortObservable` (OB1), `RCAS.outputOnly_iff_not_effortObservable`
* `RCAS.proportionalShare_budgetBalanced`, `RCAS.proportionalShare_effortObservable`,
  `RCAS.proportionalShare_marginal_pos` (OB2)
* `RCAS.proportionalShare_marginal_zero` (the marginal reward needs the other's effort `> 0`)
-/

noncomputable section

namespace RCAS

/-- A team production environment: each member chooses an effort; the joint output is
determined by the effort profile. -/
structure TeamProduction (ι : Type*) where
  /-- Each member's effort. -/
  effort : ι → ℝ
  /-- Joint output as a function of the effort profile. -/
  output : (ι → ℝ) → ℝ

/-- Holmström's premise as written in the specification: the reward is a function of the joint
output only. -/
def OutputOnlyReward (ι : Type*) (s : ι → ℝ → ℝ) : Prop :=
  ∀ i, ∃ f : ℝ → ℝ, ∀ q, s i q = f q

/-- Budget balance: the rewards add up to the output. -/
def BudgetBalanced (ι : Type*) [Fintype ι] (s : ι → ℝ → ℝ) : Prop :=
  ∀ q, ∑ i, s i q = q

/-- Effort is observable and used: some member's reward differs between two effort profiles at
the same output. -/
def EffortObservable (ι : Type*) (s : ι → (ι → ℝ) → ℝ → ℝ) : Prop :=
  ∃ i, ∃ e₁ e₂ : ι → ℝ, ∃ q, s i e₁ q ≠ s i e₂ q

/-- Holmström's premise for a rule that may refer to the effort profile: it depends on the
profile only through the output. -/
def OutputOnly (ι : Type*) (s : ι → (ι → ℝ) → ℝ → ℝ) : Prop :=
  ∀ i, ∃ f : ℝ → ℝ, ∀ e q, s i e q = f q

/-- The specification's `OutputOnlyReward` holds for every rule of its type: such a rule cannot
refer to effort in the first place. -/
theorem outputOnlyReward_trivial (ι : Type*) (s : ι → ℝ → ℝ) : OutputOnlyReward ι s :=
  fun i => ⟨s i, fun _ => rfl⟩

variable {ι : Type*} {s : ι → (ι → ℝ) → ℝ → ℝ}

/-- **OB1**: if effort is observable and used, the reward is not a function of the output only.
Immediate from the definitions. -/
theorem not_outputOnly_of_effortObservable (h : EffortObservable ι s) : ¬ OutputOnly ι s := by
  rintro hout
  obtain ⟨i, e₁, e₂, q, hne⟩ := h
  obtain ⟨f, hf⟩ := hout i
  exact hne (by rw [hf, hf])

/-- OB1 sharpened: a rule depends on the output only exactly when it does not use effort. -/
theorem outputOnly_iff_not_effortObservable : OutputOnly ι s ↔ ¬ EffortObservable ι s := by
  refine ⟨fun h h' => not_outputOnly_of_effortObservable h' h, fun h i => ?_⟩
  refine ⟨fun q => s i 0 q, fun e q => ?_⟩
  by_contra hne
  exact h ⟨i, e, 0, q, hne⟩

/-- An output-only rule seen as a rule on effort profiles does not use effort. -/
theorem not_effortObservable_of_outputOnlyReward (s : ι → ℝ → ℝ) :
    ¬ EffortObservable ι (fun i _ q => s i q) :=
  fun ⟨_, _, _, _, hne⟩ => hne rfl

/-! ### OB2: effort-proportional sharing for two members -/

/-- Effort-proportional sharing: member `i` receives the share `e i / (e 0 + e 1)` of the output. -/
def proportionalShare (i : Fin 2) (e : Fin 2 → ℝ) (q : ℝ) : ℝ :=
  e i / (e 0 + e 1) * q

/-- **OB2** (budget balance): with positive total effort, the shares add up to the output. -/
theorem proportionalShare_budgetBalanced {e : Fin 2 → ℝ} (he : 0 < e 0 + e 1) (q : ℝ) :
    ∑ i, proportionalShare i e q = q := by
  rw [Fin.sum_univ_two]
  unfold proportionalShare
  field_simp

/-- **OB2** (effort is used): the rule refers to individual effort. -/
theorem proportionalShare_effortObservable : EffortObservable (Fin 2) proportionalShare :=
  ⟨0, ![1, 0], ![0, 1], 1, by norm_num [proportionalShare]⟩

/-- The rule as a function of member `0`'s own effort `x`, the other's effort `c` and output `q`
held fixed. -/
theorem proportionalShare_update_zero (e : Fin 2 → ℝ) (q x : ℝ) :
    proportionalShare 0 (Function.update e 0 x) q = x / (x + e 1) * q := by
  simp [proportionalShare]

theorem proportionalShare_update_one (e : Fin 2 → ℝ) (q x : ℝ) :
    proportionalShare 1 (Function.update e 1 x) q = x / (e 0 + x) * q := by
  simp [proportionalShare]

/-- Marginal reward of `x ↦ x / (x + c) * q`. -/
theorem hasDerivAt_share {c q x : ℝ} (hx : x + c ≠ 0) :
    HasDerivAt (fun y => y / (y + c) * q) (c / (x + c) ^ 2 * q) x := by
  have h := ((hasDerivAt_id x).div ((hasDerivAt_id x).add_const c) hx).mul_const q
  convert h using 1
  · rfl
  · simp only [id]
    ring

/-- **OB2** (marginal reward): with the output held fixed, member `0`'s marginal reward is
`e 1 / (e 0 + e 1)² · q`, and symmetrically for member `1`. -/
theorem proportionalShare_marginal {e : Fin 2 → ℝ} (he : 0 < e 0 + e 1) (q : ℝ) :
    deriv (fun x => proportionalShare 0 (Function.update e 0 x) q) (e 0) =
        e 1 / (e 0 + e 1) ^ 2 * q ∧
      deriv (fun x => proportionalShare 1 (Function.update e 1 x) q) (e 1) =
        e 0 / (e 0 + e 1) ^ 2 * q := by
  constructor
  · simp only [proportionalShare_update_zero]
    exact (hasDerivAt_share he.ne').deriv
  · simp only [proportionalShare_update_one]
    have h := hasDerivAt_share (c := e 0) (q := q) (x := e 1) (by linarith)
    simp only [add_comm _ (e 0)] at h
    exact h.deriv

/-- **OB2** (positive marginal reward): if both members exert positive effort and the output is
positive, each member's marginal reward is positive. -/
theorem proportionalShare_marginal_pos {e : Fin 2 → ℝ} (he : ∀ i, 0 < e i) {q : ℝ} (hq : 0 < q) :
    0 < deriv (fun x => proportionalShare 0 (Function.update e 0 x) q) (e 0) ∧
      0 < deriv (fun x => proportionalShare 1 (Function.update e 1 x) q) (e 1) := by
  have hsum : 0 < e 0 + e 1 := add_pos (he 0) (he 1)
  obtain ⟨h0, h1⟩ := proportionalShare_marginal hsum q
  rw [h0, h1]
  exact ⟨by have := he 1; positivity, by have := he 0; positivity⟩

/-- **OB2** (bundled): effort-proportional sharing is budget-balanced at positive total effort,
uses individual effort, and gives each member a positive marginal reward when both efforts and
the output are positive. -/
theorem proportionalShare_spec :
    (∀ e : Fin 2 → ℝ, 0 < e 0 + e 1 → ∀ q, ∑ i, proportionalShare i e q = q) ∧
    EffortObservable (Fin 2) proportionalShare ∧ ¬ OutputOnly (Fin 2) proportionalShare ∧
    (∀ e : Fin 2 → ℝ, (∀ i, 0 < e i) → ∀ q, 0 < q →
      0 < deriv (fun x => proportionalShare 0 (Function.update e 0 x) q) (e 0) ∧
      0 < deriv (fun x => proportionalShare 1 (Function.update e 1 x) q) (e 1)) :=
  ⟨fun _ he q => proportionalShare_budgetBalanced he q, proportionalShare_effortObservable,
    not_outputOnly_of_effortObservable proportionalShare_effortObservable,
    fun _ he _ hq => proportionalShare_marginal_pos he hq⟩

/-- The positive marginal reward needs the other's effort to be positive: if member `1` exerts
no effort, member `0`'s share is the whole output whatever `e 0 > 0`, so the marginal reward is
`0`. -/
theorem proportionalShare_marginal_zero :
    deriv (fun x => proportionalShare 0 (Function.update ![1, 0] 0 x) 1) 1 = 0 := by
  simp only [proportionalShare_update_zero]
  rw [(hasDerivAt_share (c := (![1, 0] : Fin 2 → ℝ) 1) (q := 1) (x := 1) (by simp)).deriv]
  simp

namespace Example

/-- Two members whose output is the sum of efforts. -/
def additiveTeam : TeamProduction (Fin 2) where
  effort := ![1, 2]
  output e := e 0 + e 1

/-- With the efforts `(1, 2)` and the output `3`, effort-proportional sharing pays `1` and `2`. -/
example : proportionalShare 0 additiveTeam.effort (additiveTeam.output additiveTeam.effort) = 1 ∧
    proportionalShare 1 additiveTeam.effort (additiveTeam.output additiveTeam.effort) = 2 := by
  norm_num [proportionalShare, additiveTeam]

end Example

end RCAS
