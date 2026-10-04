import RCAS.Basic

/-!
# Minimal sufficient constraints (§4.2)

A constraint is a finite set `B : Finset β` of atomic constraints. It has a load
`cost : Finset β → ℝ`, and it may or may not be *admissible* (`Adm B`: outcome, law, safety
and direction are all secured). The aim is not zero constraint but the least load among the
admissible constraints.

Candidates are drawn from a finite family `C : Finset (Finset β)`. When `β` is finite,
`C = Finset.univ` (every constraint is a candidate) is allowed.

## Main results

* `RCAS.exists_minSufficient` (C1)
* `RCAS.prefers_of_cost_lt` (C2, immediate from the definition)
* `RCAS.not_minSufficient_of_erase` (C3)
* `RCAS.MinSufficient.not_admissible_erase` (C3, contrapositive: every atom is needed)
-/

namespace RCAS

variable {β : Type*}

/-- `B` is a minimal sufficient constraint among the candidates `C`: it is a candidate, it is
admissible, and no admissible candidate has strictly smaller load. -/
def MinSufficient (cost : Finset β → ℝ) (Adm : Finset β → Prop) (C : Finset (Finset β))
    (B : Finset β) : Prop :=
  B ∈ C ∧ Adm B ∧ ∀ B' ∈ C, Adm B' → cost B ≤ cost B'

/-- Preference between constraints: `B` is preferred to `B'` when `B` is admissible and has
strictly smaller load. -/
def Prefers (cost : Finset β → ℝ) (Adm : Finset β → Prop) (B B' : Finset β) : Prop :=
  Adm B ∧ cost B < cost B'

/-- **C1** (existence of a minimum): if some candidate is admissible, a minimal sufficient
constraint exists. -/
theorem exists_minSufficient (cost : Finset β → ℝ) (Adm : Finset β → Prop)
    (C : Finset (Finset β)) (h : ∃ B ∈ C, Adm B) : ∃ B, MinSufficient cost Adm C B := by
  classical
  obtain ⟨B₀, hB₀C, hB₀⟩ := h
  have hne : (C.filter Adm).Nonempty := ⟨B₀, Finset.mem_filter.mpr ⟨hB₀C, hB₀⟩⟩
  obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image (C.filter Adm) cost hne
  rw [Finset.mem_filter] at hB
  exact ⟨B, hB.1, hB.2, fun B' hB'C hB' => hmin B' (Finset.mem_filter.mpr ⟨hB'C, hB'⟩)⟩

/-- **C1** with every constraint as a candidate (finitely many atoms). -/
theorem exists_minSufficient_univ [Fintype β] (cost : Finset β → ℝ) (Adm : Finset β → Prop)
    (h : ∃ B, Adm B) : ∃ B, MinSufficient cost Adm Finset.univ B := by
  obtain ⟨B₀, hB₀⟩ := h
  exact exists_minSufficient cost Adm _ ⟨B₀, Finset.mem_univ _, hB₀⟩

/-- **C2** (dominance): of two admissible constraints, the one with strictly smaller load is
preferred. Immediate from the definition of `Prefers`. -/
theorem prefers_of_cost_lt {cost : Finset β → ℝ} {Adm : Finset β → Prop} {B B' : Finset β}
    (hB : Adm B) (_hB' : Adm B') (hlt : cost B < cost B') : Prefers cost Adm B B' :=
  ⟨hB, hlt⟩

/-- A candidate that is beaten by an admissible candidate is not minimal sufficient. -/
theorem not_minSufficient_of_prefers {cost : Finset β → ℝ} {Adm : Finset β → Prop}
    {C : Finset (Finset β)} {B B' : Finset β} (hBC : B ∈ C) (hpref : Prefers cost Adm B B') :
    ¬ MinSufficient cost Adm C B' := by
  rintro ⟨-, -, hmin⟩
  exact absurd (hmin B hBC hpref.1) (not_le.mpr hpref.2)

variable [DecidableEq β]

/-- **C3** (the burden of proof lies with the constraint): if the load is strictly monotone
under inclusion, and removing an atom `r ∈ B` keeps the constraint admissible, then `B` is not
minimal sufficient.

The hypothesis `r ∈ B` makes explicit what "removing `r` from `B`" presupposes; see
`docs/DEVIATIONS.md`. -/
theorem not_minSufficient_of_erase {cost : Finset β → ℝ} {Adm : Finset β → Prop}
    {C : Finset (Finset β)} {B : Finset β} {r : β} (hcost : StrictMono cost) (hr : r ∈ B)
    (hC : B.erase r ∈ C) (hAdm : Adm (B.erase r)) : ¬ MinSufficient cost Adm C B :=
  not_minSufficient_of_prefers hC ⟨hAdm, hcost (Finset.erase_ssubset hr)⟩

/-- **C3** (contrapositive): in a minimal sufficient constraint, every atom is necessary —
removing any one of them breaks admissibility. -/
theorem MinSufficient.not_admissible_erase {cost : Finset β → ℝ} {Adm : Finset β → Prop}
    {C : Finset (Finset β)} {B : Finset β} (hB : MinSufficient cost Adm C B)
    (hcost : StrictMono cost) {r : β} (hr : r ∈ B) (hC : B.erase r ∈ C) :
    ¬ Adm (B.erase r) :=
  fun hAdm => not_minSufficient_of_erase hcost hr hC hAdm hB

/-- Without `r ∈ B` the conclusion of C3 fails: erasing an absent atom changes nothing. -/
theorem not_minSufficient_of_erase_needs_mem :
    ∃ (cost : Finset Bool → ℝ) (Adm : Finset Bool → Prop) (B : Finset Bool) (r : Bool),
      StrictMono cost ∧ Adm (B.erase r) ∧ MinSufficient cost Adm Finset.univ B := by
  refine ⟨fun B => (B.card : ℝ), fun _ => True, ∅, true, ?_, trivial, ?_⟩
  · intro B B' h
    exact Nat.cast_lt.mpr (Finset.card_lt_card h)
  · exact ⟨Finset.mem_univ _, trivial, fun B' _ _ => by simp⟩

/-! ### Example: a safety rule is the only necessary atom -/

namespace Example

/-- Atomic constraints. -/
inductive Atom
  | safety
  | dressCode
  | dailyReport
  deriving DecidableEq

open Atom

/- Written by hand: `deriving Fintype` fails in the pinned Mathlib (see README). -/
instance : Fintype Atom :=
  ⟨{safety, dressCode, dailyReport}, fun a => by cases a <;> simp⟩

/-- Load: number of atoms. -/
def cost (B : Finset Atom) : ℝ := B.card

/-- Admissible: the safety rule is in force. -/
def Adm (B : Finset Atom) : Prop := safety ∈ B

theorem cost_strictMono : StrictMono cost :=
  fun _ _ h => Nat.cast_lt.mpr (Finset.card_lt_card h)

theorem minSufficient_safety : MinSufficient cost Adm Finset.univ {safety} := by
  refine ⟨Finset.mem_univ _, Finset.mem_singleton_self _, fun B' _ hB' => ?_⟩
  simp only [cost, Finset.card_singleton, Nat.cast_one, Nat.one_le_cast]
  exact Finset.card_pos.mpr ⟨_, hB'⟩

/-- The full rule book is admissible but not minimal: `dressCode` can be removed. -/
theorem not_minSufficient_full : ¬ MinSufficient cost Adm Finset.univ Finset.univ :=
  not_minSufficient_of_erase cost_strictMono (Finset.mem_univ dressCode) (Finset.mem_univ _)
    (by simp [Adm])

end Example

end RCAS
