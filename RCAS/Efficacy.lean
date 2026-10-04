import RCAS.Basic

/-!
# Self-efficacy dynamics (§4.5)

`s (t+1) = s t + a * 1[success t ∧ selfChosen t]`.

That `a > 0` — a success on a self-chosen course raises self-efficacy — is a **premise** of the
model and appears as a hypothesis. E4 is the in-model consequence of that premise.

## Main results

* `RCAS.efficacy_monotone` (E1)
* `RCAS.efficacy_eq` (E2, closed form)
* `RCAS.efficacy_eq_init_of_not_selfChosen` (E3)
* `RCAS.efficacy_lt_of_selfChosen_success` (E4)
-/

namespace RCAS

/-- Self-efficacy: it rises by `a` exactly at the times of a success on a self-chosen course. -/
def efficacy (a s₀ : ℝ) (success selfChosen : ℕ → Prop) [DecidablePred success]
    [DecidablePred selfChosen] : ℕ → ℝ
  | 0 => s₀
  | t + 1 => efficacy a s₀ success selfChosen t + (if success t ∧ selfChosen t then a else 0)

variable {a s₀ : ℝ} {success selfChosen : ℕ → Prop} [DecidablePred success]
  [DecidablePred selfChosen]

/-- Number of times before `t` with a success on a self-chosen course. -/
def chosenSuccessCount (success selfChosen : ℕ → Prop) [DecidablePred success]
    [DecidablePred selfChosen] (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun τ => success τ ∧ selfChosen τ)).card

/-- **E1**: with `0 ≤ a`, self-efficacy is non-decreasing in time. -/
theorem efficacy_monotone (ha : 0 ≤ a) : Monotone (efficacy a s₀ success selfChosen) := by
  refine monotone_nat_of_le_succ fun t => ?_
  simp only [efficacy]
  split_ifs <;> linarith

/-- **E2** (closed form): `efficacy t = s₀ + a * #{τ < t | success τ ∧ selfChosen τ}`. -/
theorem efficacy_eq (t : ℕ) :
    efficacy a s₀ success selfChosen t = s₀ + a * chosenSuccessCount success selfChosen t := by
  induction t with
  | zero => simp [efficacy, chosenSuccessCount]
  | succ t ih =>
    simp only [efficacy, ih, chosenSuccessCount, Finset.card_filter, Finset.sum_range_succ]
    push_cast
    split_ifs <;> ring

/-- **E3** (instruction alone does not raise it): if no course is self-chosen, self-efficacy
stays at its initial value. -/
theorem efficacy_eq_init_of_not_selfChosen (h : ∀ t, ¬ selfChosen t) (t : ℕ) :
    efficacy a s₀ success selfChosen t = s₀ := by
  induction t with
  | zero => rfl
  | succ t ih => simp [efficacy, ih, h t]

/-- **E4** (comparison): same initial value and same successes; one course is never
self-chosen, the other has a self-chosen success at some `τ < T`. With `a > 0` (premise), the
second has strictly higher self-efficacy at time `T`. -/
theorem efficacy_lt_of_selfChosen_success {selfChosen' : ℕ → Prop} [DecidablePred selfChosen']
    (ha : 0 < a) {T τ : ℕ} (hτ : τ < T) (hsucc : success τ) (hchosen : selfChosen' τ) :
    efficacy a s₀ success (fun _ => False) T < efficacy a s₀ success selfChosen' T := by
  rw [efficacy_eq_init_of_not_selfChosen (fun _ h => h), efficacy_eq]
  have hcount : 1 ≤ chosenSuccessCount success selfChosen' T :=
    Finset.card_pos.mpr ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hτ, hsucc, hchosen⟩⟩
  have : (1 : ℝ) ≤ chosenSuccessCount success selfChosen' T := by exact_mod_cast hcount
  nlinarith

namespace Example

/-- Every attempt succeeds; the course is self-chosen at even times only. -/
example : efficacy 1 0 (fun _ => True) (fun t => t % 2 = 0) 3 = 2 := by
  norm_num [efficacy]

/-- The same successes, never self-chosen: no change (E3). -/
example : efficacy 1 0 (fun _ => True) (fun _ => False) 3 = 0 := by
  norm_num [efficacy]

end Example

end RCAS
