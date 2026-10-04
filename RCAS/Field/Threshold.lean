import RCAS.Basic

/-!
# Threshold model: the second penguin (§5.4)

The adopters form a finite set `A : Finset ι`. Weights `w i j ≥ 0` (influence of `j` on `i`)
and thresholds `θ i`. Irreversible update: an agent adopts once the total weight of adopters it
sees reaches its threshold,

`step A = A ∪ { i | θ i ≤ ∑ j ∈ A, w i j }`.

The reversible version (agents may drop out) breaks monotonicity and is not treated.

## Main results

* `RCAS.subset_step`, `RCAS.monotone_iterate_step` (T1)
* `RCAS.step_mono`, `RCAS.iterate_step_mono` (T2, monotone in the seed)
* `RCAS.iterate_step_mono_weight` (T3, monotone in the coupling)
* `RCAS.step_singleton_of_isolated`, `RCAS.iterate_step_singleton_of_isolated` (T4)
* `RCAS.step_finalAdopters` (T5, a fixed point within `Fintype.card ι` steps)
-/

namespace RCAS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One round of irreversible adoption. -/
noncomputable def step (w : ι → ι → ℝ) (θ : ι → ℝ) (A : Finset ι) : Finset ι :=
  A ∪ Finset.univ.filter fun i => θ i ≤ ∑ j ∈ A, w i j

variable {w w' : ι → ι → ℝ} {θ : ι → ℝ}

theorem mem_step {A : Finset ι} {i : ι} :
    i ∈ step w θ A ↔ i ∈ A ∨ θ i ≤ ∑ j ∈ A, w i j := by
  simp [step]

/-- **T1**: adoption is never lost in one round. -/
theorem subset_step (A : Finset ι) : A ⊆ step w θ A :=
  Finset.subset_union_left

/-- **T1**: the adopter sets grow monotonically in time. -/
theorem monotone_iterate_step (A₀ : Finset ι) : Monotone fun t => (step w θ)^[t] A₀ := by
  refine monotone_nat_of_le_succ fun t => ?_
  rw [Function.iterate_succ_apply']
  exact subset_step _

/-- One round is monotone jointly in the seed and in the weights (weights `w'` nonnegative). -/
theorem step_mono₂ (hw' : ∀ i j, 0 ≤ w' i j) (hww' : ∀ i j, w i j ≤ w' i j) {S S' : Finset ι}
    (hSS' : S ⊆ S') : step w θ S ⊆ step w' θ S' := by
  intro i hi
  rw [mem_step] at hi ⊢
  rcases hi with hi | hi
  · exact Or.inl (hSS' hi)
  · refine Or.inr (hi.trans ?_)
    calc ∑ j ∈ S, w i j ≤ ∑ j ∈ S, w' i j := Finset.sum_le_sum fun j _ => hww' i j
      _ ≤ ∑ j ∈ S', w' i j := Finset.sum_le_sum_of_subset_of_nonneg hSS' fun j _ _ => hw' i j

theorem iterate_step_mono₂ (hw' : ∀ i j, 0 ≤ w' i j) (hww' : ∀ i j, w i j ≤ w' i j)
    {S S' : Finset ι} (hSS' : S ⊆ S') (t : ℕ) : (step w θ)^[t] S ⊆ (step w' θ)^[t] S' := by
  induction t with
  | zero => exact hSS'
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact step_mono₂ hw' hww' ih

/-- **T2** (monotone in the seed): a larger seed gives a larger next adopter set. -/
theorem step_mono (hw : ∀ i j, 0 ≤ w i j) {A A' : Finset ι} (hAA' : A ⊆ A') :
    step w θ A ⊆ step w θ A' :=
  step_mono₂ hw (fun _ _ => le_rfl) hAA'

/-- **T2** at every time. -/
theorem iterate_step_mono (hw : ∀ i j, 0 ≤ w i j) {A A' : Finset ι} (hAA' : A ⊆ A') (t : ℕ) :
    (step w θ)^[t] A ⊆ (step w θ)^[t] A' :=
  iterate_step_mono₂ hw (fun _ _ => le_rfl) hAA' t

/-- **T3** (monotone in the coupling): if the weights are larger entrywise, then from the same
seed the adopter set is larger at every time. Whether the cascade crosses a threshold is decided
by the coupling structure, not by the quality of the seed alone. -/
theorem iterate_step_mono_weight (hw : ∀ i j, 0 ≤ w i j) (hww' : ∀ i j, w i j ≤ w' i j)
    (A₀ : Finset ι) (t : ℕ) : (step w θ)^[t] A₀ ⊆ (step w' θ)^[t] A₀ :=
  iterate_step_mono₂ (fun i j => (hw i j).trans (hww' i j)) hww' subset_rfl t

/-- **T4** (the isolated first penguin): from the seed `{i₀}`, if nobody else is moved by `i₀`
alone (`w i i₀ < θ i` for `i ≠ i₀`), nothing happens. -/
theorem step_singleton_of_isolated {i₀ : ι} (hiso : ∀ i, i ≠ i₀ → w i i₀ < θ i) :
    step w θ {i₀} = {i₀} := by
  refine Finset.Subset.antisymm (fun i hi => ?_) (subset_step _)
  rw [mem_step, Finset.sum_singleton] at hi
  rcases hi with hi | hi
  · exact hi
  · by_contra hne
    exact absurd hi (not_le.mpr (hiso i (Finset.notMem_singleton.mp hne)))

/-- **T4** at every time. -/
theorem iterate_step_singleton_of_isolated {i₀ : ι} (hiso : ∀ i, i ≠ i₀ → w i i₀ < θ i)
    (t : ℕ) : (step w θ)^[t] {i₀} = {i₀} :=
  Function.iterate_fixed (step_singleton_of_isolated hiso) t

/-! ### T5: a fixed point within `Fintype.card ι` rounds -/

/-- The adopter set after `Fintype.card ι` rounds. -/
noncomputable def finalAdopters (w : ι → ι → ℝ) (θ : ι → ℝ) (A₀ : Finset ι) : Finset ι :=
  (step w θ)^[Fintype.card ι] A₀

/-- Once a round changes nothing, nothing changes afterwards. -/
theorem iterate_step_eq_of_fixed {A₀ : Finset ι} {s : ℕ}
    (hs : step w θ ((step w θ)^[s] A₀) = (step w θ)^[s] A₀) {t : ℕ} (hst : s ≤ t) :
    (step w θ)^[t] A₀ = (step w θ)^[s] A₀ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [add_comm, Function.iterate_add_apply, Function.iterate_fixed hs]

/-- If the first `t` rounds each add someone, at least `t` agents have adopted. -/
theorem le_card_iterate_step {A₀ : Finset ι} :
    ∀ t, (∀ s < t, step w θ ((step w θ)^[s] A₀) ≠ (step w θ)^[s] A₀) →
      t ≤ ((step w θ)^[t] A₀).card
  | 0, _ => Nat.zero_le _
  | t + 1, h => by
    have ih := le_card_iterate_step t fun s hs => h s (Nat.lt_succ_of_lt hs)
    rw [Function.iterate_succ_apply']
    have hlt := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨subset_step _, (h t (Nat.lt_succ_self t)).symm⟩)
    omega

/-- **T5**: since `ι` is finite, the sequence reaches a fixed point of `step` within
`Fintype.card ι` rounds. -/
theorem step_finalAdopters (A₀ : Finset ι) :
    step w θ (finalAdopters w θ A₀) = finalAdopters w θ A₀ := by
  set n := Fintype.card ι
  have : ∃ s ≤ n, step w θ ((step w θ)^[s] A₀) = (step w θ)^[s] A₀ := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have := le_card_iterate_step (w := w) (θ := θ) (A₀ := A₀) (n + 1)
      fun s hs => hcon s (Nat.lt_succ_iff.mp hs)
    have := Finset.card_le_univ ((step w θ)^[n + 1] A₀)
    omega
  obtain ⟨s, hsn, hs⟩ := this
  unfold finalAdopters
  rw [iterate_step_eq_of_fixed hs hsn]
  exact hs

/-- Every adopter set along the way is contained in the final one. -/
theorem iterate_step_subset_finalAdopters (A₀ : Finset ι) (t : ℕ) :
    (step w θ)^[t] A₀ ⊆ finalAdopters w θ A₀ := by
  rcases le_total t (Fintype.card ι) with h | h
  · exact monotone_iterate_step A₀ h
  · rw [iterate_step_eq_of_fixed (step_finalAdopters A₀) h]
    rfl

namespace Example

/-- A line `0 → 1 → 2`: agent `1` watches `0`, agent `2` watches `1`. -/
def wLine : Fin 3 → Fin 3 → ℝ := fun i j => if i.val = j.val + 1 then 1 else 0

/-- The first penguin alone, with the line coupling, sets off a full cascade in two rounds. -/
example : (step wLine (fun _ => 1))^[2] {0} = Finset.univ := by
  have h1 : step wLine (fun _ => 1) {0} = {0, 1} := by
    ext i
    simp only [mem_step, Finset.sum_singleton]
    fin_cases i <;> simp [wLine]
  have h2 : step wLine (fun _ => 1) {0, 1} = Finset.univ := by
    ext i
    simp only [mem_step, Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide), Finset.mem_univ,
      iff_true]
    fin_cases i <;> simp [wLine]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, h1, h2]

/-- Without coupling the first penguin stays alone (T4). -/
example : (step (fun (_ _ : Fin 3) => (0 : ℝ)) (fun _ => 1))^[5] {0} = {0} :=
  iterate_step_singleton_of_isolated (fun _ _ => by norm_num) 5

end Example

end RCAS
