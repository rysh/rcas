import RCAS.Basic

/-!
# Widening the visible futures (§4.9)

The manager does not rewrite the person's preference `U`. The manager widens the finite set
`F` of futures the person can see.

`U` is held **fixed** (it does not depend on the information set). The original formulation
compared `U(f | I')` with `U(f | I)`, with the information set updated together with `F`; when
`U` depends on information, the inequality does not hold in general
(`RCAS.information_dependent_counterexample`). See `docs/DEVIATIONS.md`.

## Main results

* `RCAS.sup'_le_sup'_of_subset` (FC1)
* `RCAS.sup'_le_sup'_insert` (FC2, the option is not taken: the maximum does not drop)
* `RCAS.IsChoice.sup'_le` (FC2, whatever is chosen from the widened set)
* `RCAS.sup'_le_of_choose_new` (FC2, the new option is chosen)
-/

namespace RCAS

variable {φ : Type*}

/-- **FC1**: with `U` fixed, widening the visible futures does not lower the best value. -/
theorem sup'_le_sup'_of_subset (U : φ → ℝ) {F F' : Finset φ} (hFF' : F ⊆ F')
    (hF : F.Nonempty) (hF' : F'.Nonempty) : F.sup' hF U ≤ F'.sup' hF' U :=
  Finset.sup'_mono U hFF' hF

/-- **FC2** (a reference point has value even when not adopted): after adding a future `f`,
the best value does not drop, whether or not `f` is taken. Corollary of FC1. -/
theorem sup'_le_sup'_insert [DecidableEq φ] (U : φ → ℝ) {F : Finset φ} (hF : F.Nonempty)
    (f : φ) : F.sup' hF U ≤ (insert f F).sup' (Finset.insert_nonempty f F) U :=
  sup'_le_sup'_of_subset U (Finset.subset_insert f F) hF _

/-- `x` is a choice from `F` under `U`: a best element of `F`. -/
def IsChoice (F : Finset φ) (U : φ → ℝ) (x : φ) : Prop :=
  x ∈ F ∧ ∀ y ∈ F, U y ≤ U x

/-- **FC2**: whatever is chosen from the widened set is worth at least the old best value. -/
theorem IsChoice.sup'_le [DecidableEq φ] {U : φ → ℝ} {F : Finset φ} (hF : F.Nonempty)
    {f x : φ} (hx : IsChoice (insert f F) U x) : F.sup' hF U ≤ U x :=
  Finset.sup'_le hF U fun y hy => hx.2 y (Finset.mem_insert_of_mem hy)

/-- **FC2** (the new option is chosen): `U f` is at least the old best value. -/
theorem sup'_le_of_choose_new [DecidableEq φ] {U : φ → ℝ} {F : Finset φ} (hF : F.Nonempty)
    {f : φ} (hf : IsChoice (insert f F) U f) : F.sup' hF U ≤ U f :=
  hf.sup'_le hF

/-- If the valuation changes with the information set, widening can lower the best value:
FC1 needs `U` fixed. -/
theorem information_dependent_counterexample :
    ∃ (F F' : Finset Unit) (hF : F.Nonempty) (hF' : F'.Nonempty) (U U' : Unit → ℝ),
      F ⊆ F' ∧ ¬ F.sup' hF U ≤ F'.sup' hF' U' :=
  ⟨{()}, {()}, Finset.singleton_nonempty _, Finset.singleton_nonempty _, fun _ => 1,
    fun _ => 0, subset_rfl, by simp⟩

namespace Example

/-- Futures a person can see: stay in the current role, or (newly shown) lead a project. -/
inductive Future
  | stay
  | lead
  deriving DecidableEq

open Future

/-- The person's own valuation; the manager does not change it. -/
def U : Future → ℝ
  | stay => 2
  | lead => 3

example : ({stay} : Finset Future).sup' (Finset.singleton_nonempty _) U ≤
    ({lead, stay} : Finset Future).sup' (Finset.insert_nonempty _ _) U :=
  sup'_le_sup'_insert U _ lead

/-- The person chooses the new future, and it is worth more than the old best. -/
example : IsChoice {lead, stay} U lead ∧
    ({stay} : Finset Future).sup' (Finset.singleton_nonempty _) U < U lead := by
  refine ⟨⟨by simp, fun y hy => ?_⟩, by norm_num [U]⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl <;> norm_num [U]

end Example

end RCAS
