import RCAS.Basic

/-!
# Rule update and rule deletion (§4.4)

Rule sets evolve in discrete time, `R : ℕ → 𝓡`. A rule set is evaluated by
`J : 𝓡 → ℝ` (outcome − load − friction). The update maximizes `J` over a finite neighbourhood
`N R` that contains the status quo.

The monotonicity result P8 is a property of the *designed* update operator. It is not a claim
that real organizations improve.

## Main results

* `RCAS.RuleDynamics.J_iterate_succ_ge`, `RCAS.RuleDynamics.monotone_J_iterate` (P8)
* `RCAS.stay_needed` (P8 fails without `stay`)
* `RCAS.RuleDynamics.tendsto_J_iterate` (P8', convergence when `J` is bounded above)
* `RCAS.RuleDynamics.J_update_gt_of_erase` (P9)
* `RCAS.Example.card_not_monotone` (P9, the number of rules can decrease)
-/

namespace RCAS

/-- A rule-update operator that maximizes the evaluation `J` over a finite neighbourhood `N R`
which contains the current rule set. -/
structure RuleDynamics (𝓡 : Type*) where
  /-- Evaluation of a rule set: outcome − load − friction. -/
  J : 𝓡 → ℝ
  /-- Candidate rule sets reachable in one step. -/
  N : 𝓡 → Finset 𝓡
  /-- The update. -/
  update : 𝓡 → 𝓡
  /-- Premise: keeping the current rule set is always a candidate. -/
  stay : ∀ R, R ∈ N R
  /-- Premise: the update picks a candidate. -/
  mem : ∀ R, update R ∈ N R
  /-- Premise: the update picks a best candidate. -/
  best : ∀ R, ∀ R' ∈ N R, J R' ≤ J (update R)

namespace RuleDynamics

variable {𝓡 : Type*} (D : RuleDynamics 𝓡)

/-- One update never lowers the evaluation. -/
theorem J_le_J_update (R : 𝓡) : D.J R ≤ D.J (D.update R) :=
  D.best R R (D.stay R)

/-- **P8** (one step). This is a property of the update operator as designed, not a claim that
real organizations improve. -/
theorem J_iterate_succ_ge (R₀ : 𝓡) (t : ℕ) :
    D.J (D.update^[t + 1] R₀) ≥ D.J (D.update^[t] R₀) := by
  rw [Function.iterate_succ_apply']
  exact D.J_le_J_update _

/-- **P8**: along the iterates of the update, the evaluation is monotone in time. This is a
property of the update operator as designed, not a claim that real organizations improve. -/
theorem monotone_J_iterate (R₀ : 𝓡) : Monotone (fun t => D.J (D.update^[t] R₀)) :=
  monotone_nat_of_le_succ (D.J_iterate_succ_ge R₀)

/-- **P8'**: if `J` is bounded above along the iterates, the evaluation converges (to its
supremum). -/
theorem tendsto_J_iterate (R₀ : 𝓡) (hbdd : BddAbove (Set.range fun t => D.J (D.update^[t] R₀))) :
    Filter.Tendsto (fun t => D.J (D.update^[t] R₀)) Filter.atTop
      (nhds (⨆ t, D.J (D.update^[t] R₀))) :=
  tendsto_atTop_ciSup (D.monotone_J_iterate R₀) hbdd

/-- **P9** (learning includes deletion): if deleting rule `r` is a candidate and strictly
improves the evaluation, the update strictly improves the evaluation and changes the rule set. -/
theorem J_update_gt_of_erase {β : Type*} [DecidableEq β] (D : RuleDynamics (Finset β))
    {R : Finset β} {r : β} (hN : R.erase r ∈ D.N R) (hJ : D.J (R.erase r) > D.J R) :
    D.J (D.update R) > D.J R ∧ D.update R ≠ R := by
  have hgt : D.J (D.update R) > D.J R := lt_of_lt_of_le hJ (D.best R _ hN)
  exact ⟨hgt, fun h => (ne_of_gt hgt) (congrArg D.J h)⟩

end RuleDynamics

/-- Without the premise `stay`, P8 fails: a best-candidate update over a neighbourhood that
excludes the status quo can lower the evaluation. -/
theorem stay_needed :
    ∃ (J : Bool → ℝ) (N : Bool → Finset Bool) (update : Bool → Bool),
      (∀ R, update R ∈ N R) ∧ (∀ R, ∀ R' ∈ N R, J R' ≤ J (update R)) ∧
      ¬ Monotone (fun t => J (update^[t] true)) := by
  refine ⟨fun R => if R then 1 else 0, fun _ => {false}, fun _ => false, fun _ => by simp,
    fun _ R' hR' => by simp_all, fun h => ?_⟩
  have := h (Nat.zero_le 1)
  norm_num at this

namespace Example

/-- Rules over a single possible atom; the evaluation penalizes each rule. -/
def D : RuleDynamics (Finset Unit) where
  J R := -(R.card : ℝ)
  N R := {R, ∅}
  update _ := ∅
  stay R := Finset.mem_insert_self _ _
  mem _ := by simp
  best R R' hR' := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR'
    rcases hR' with rfl | rfl <;> simp

/-- **P9** (concrete): the number of rules is not monotone increasing in time; the update
deletes the only rule. -/
theorem card_not_monotone : ¬ Monotone (fun t => (D.update^[t] {()}).card) := by
  intro h
  have := h (Nat.zero_le 1)
  simp [D] at this

/-- **P9** applied in the example: deleting the rule is a candidate and strictly better. -/
example : D.J (D.update {()}) > D.J {()} ∧ D.update {()} ≠ {()} :=
  RuleDynamics.J_update_gt_of_erase D (r := ()) (by simp [D]) (by simp [D])

end Example

end RCAS
