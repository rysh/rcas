import RCAS.Basic

/-!
# Reference points and choice (§4.1)

A reference point `ρ` does not name an action. It fixes which *outcomes* are acceptable
(`ρ.acceptable`, written `Y(ρ)`) and which *actions* are within bounds (`ρ.boundary`, written
`B`: law, safety, direction). Under an outcome map `F : α → Y` the feasible actions are

`A(ρ) = { a | a ∈ B ∧ F a ∈ Y(ρ) }`.

There is *genuine choice* when `A(ρ)` contains two distinct elements. Three regimes are
distinguished:

* prescription — exactly one feasible action;
* laissez-faire — no restriction at all (`Y(ρ) = univ`, `B = univ`);
* reference–choice — some restriction, and genuine choice remains.

## Main results

* `RCAS.IsReferenceChoice.not_prescription_and_not_laissezFaire` (P1)
* `RCAS.GenuineChoice.exists_distinct_acceptable` (P2)
* `RCAS.Example.regimes_nonempty_and_distinct` (P2, concrete example)
* `RCAS.GenuineChoice.outcome_standardized_and_method_diverse` (P3, general form)
* `RCAS.Example.standardization_with_autonomy` (P3, existence)
-/

namespace RCAS

/-- A reference point: acceptable outcomes and admissible actions. It does not name an action. -/
structure Reference (Y α : Type*) where
  /-- `Y(ρ)`: outcomes meeting the purpose and the criterion. -/
  acceptable : Set Y
  /-- `B`: actions allowed by law, safety and direction. -/
  boundary : Set α

variable {α Y : Type*}

/-- `A(ρ)`: actions inside the boundary whose outcome is acceptable. -/
def feasible (F : α → Y) (ρ : Reference Y α) : Set α :=
  {a | a ∈ ρ.boundary ∧ F a ∈ ρ.acceptable}

/-- Genuine choice: at least two distinct feasible actions. -/
def GenuineChoice (F : α → Y) (ρ : Reference Y α) : Prop :=
  (feasible F ρ).Nontrivial

/-- Prescription: exactly one feasible action. -/
def IsPrescription (F : α → Y) (ρ : Reference Y α) : Prop :=
  ∃ a, feasible F ρ = {a}

/-- Laissez-faire: no restriction on outcomes and none on actions. -/
def IsLaissezFaire (ρ : Reference Y α) : Prop :=
  ρ.acceptable = Set.univ ∧ ρ.boundary = Set.univ

/-- Reference–choice: not laissez-faire, and genuine choice remains. -/
def IsReferenceChoice (F : α → Y) (ρ : Reference Y α) : Prop :=
  ¬ IsLaissezFaire ρ ∧ GenuineChoice F ρ

theorem mem_feasible {F : α → Y} {ρ : Reference Y α} {a : α} :
    a ∈ feasible F ρ ↔ a ∈ ρ.boundary ∧ F a ∈ ρ.acceptable :=
  Iff.rfl

/-- Genuine choice excludes prescription. -/
theorem GenuineChoice.not_prescription {F : α → Y} {ρ : Reference Y α}
    (h : GenuineChoice F ρ) : ¬ IsPrescription F ρ := by
  rintro ⟨a, ha⟩
  exact h.ne_singleton ha

/-- **P1** (neither prescription nor laissez-faire). Immediate from the definitions. -/
theorem IsReferenceChoice.not_prescription_and_not_laissezFaire {F : α → Y}
    {ρ : Reference Y α} (h : IsReferenceChoice F ρ) :
    ¬ IsPrescription F ρ ∧ ¬ IsLaissezFaire ρ :=
  ⟨h.2.not_prescription, h.1⟩

/-- **P2** (convergence of outcomes does not require convergence of methods): under genuine
choice there are two distinct actions both of whose outcomes are acceptable. -/
theorem GenuineChoice.exists_distinct_acceptable {F : α → Y} {ρ : Reference Y α}
    (h : GenuineChoice F ρ) :
    ∃ a a', a ≠ a' ∧ F a ∈ ρ.acceptable ∧ F a' ∈ ρ.acceptable := by
  obtain ⟨a, ha, a', ha', hne⟩ := h
  exact ⟨a, a', hne, ha.2, ha'.2⟩

/-! ### Standardization of outcomes versus standardization of methods (P3) -/

section Standardization

variable {ι : Type*}

/-- Standardization as *outcome* standardization: every agent's outcome is acceptable. -/
def OutcomeStandardized (F : α → Y) (ρ : Reference Y α) (choice : ι → α) : Prop :=
  ∀ i, F (choice i) ∈ ρ.acceptable

/-- Standardization as *method* standardization: all agents use the same action. -/
def MethodStandardized (choice : ι → α) : Prop :=
  ∀ i j, choice i = choice j

/-- Agents who each pick a feasible action are outcome-standardized. Immediate from the
definitions. -/
theorem outcomeStandardized_of_forall_feasible {F : α → Y} {ρ : Reference Y α}
    {choice : ι → α} (h : ∀ i, choice i ∈ feasible F ρ) : OutcomeStandardized F ρ choice :=
  fun i => (h i).2

/-- **P3** (general form): whenever there is genuine choice, two agents can each choose a
feasible action so that outcomes are standardized while methods are not. -/
theorem GenuineChoice.outcome_standardized_and_method_diverse {F : α → Y}
    {ρ : Reference Y α} (h : GenuineChoice F ρ) :
    ∃ choice : Fin 2 → α, (∀ i, choice i ∈ feasible F ρ) ∧
      OutcomeStandardized F ρ choice ∧ ¬ MethodStandardized choice := by
  obtain ⟨a, ha, a', ha', hne⟩ := h
  refine ⟨![a, a'], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ha
    · exact ha'
  · intro i
    fin_cases i
    · exact ha.2
    · exact ha'.2
  · intro hsame
    exact hne (hsame 0 1)

end Standardization

/-! ### Concrete example: three methods, one acceptable outcome -/

namespace Example

/-- Three methods for the same task (e.g. speeding up a slow query). -/
inductive Method
  | index
  | cache
  | queryRewrite
  deriving DecidableEq

/-- Outcomes: the target is met or not. -/
inductive Outcome
  | met
  | missed
  deriving DecidableEq

open Method Outcome

/-- Every method reaches the target. -/
def F : Method → Outcome := fun _ => met

/-- Reference–choice: the target must be met; any method is allowed. -/
def ρRC : Reference Outcome Method := ⟨{met}, Set.univ⟩

/-- Prescription: the target must be met, and only `index` is allowed. -/
def ρPres : Reference Outcome Method := ⟨{met}, {index}⟩

/-- Laissez-faire: no restriction. -/
def ρLF : Reference Outcome Method := ⟨Set.univ, Set.univ⟩

theorem feasible_ρRC : feasible F ρRC = Set.univ := by
  ext a
  simp [feasible, F, ρRC]

theorem feasible_ρPres : feasible F ρPres = {index} := by
  ext a
  simp [feasible, F, ρPres]

theorem feasible_ρLF : feasible F ρLF = Set.univ := by
  ext a
  simp [feasible, ρLF]

theorem genuineChoice_univ {G : Method → Outcome} {ρ : Reference Outcome Method}
    (h : feasible G ρ = Set.univ) : GenuineChoice G ρ := by
  rw [GenuineChoice, h]
  exact ⟨index, trivial, cache, trivial, by decide⟩

theorem not_laissezFaire_of_acceptable_eq {ρ : Reference Outcome Method}
    (h : ρ.acceptable = {met}) : ¬ IsLaissezFaire ρ := by
  rintro ⟨hacc, -⟩
  have : missed ∈ ρ.acceptable := by rw [hacc]; trivial
  rw [h] at this
  exact absurd this (by decide)

theorem rc_isReferenceChoice : IsReferenceChoice F ρRC :=
  ⟨not_laissezFaire_of_acceptable_eq rfl, genuineChoice_univ feasible_ρRC⟩

theorem pres_isPrescription : IsPrescription F ρPres :=
  ⟨index, feasible_ρPres⟩

theorem pres_not_genuineChoice : ¬ GenuineChoice F ρPres := by
  rw [GenuineChoice, feasible_ρPres]
  exact Set.not_nontrivial_singleton

theorem lf_isLaissezFaire : IsLaissezFaire ρLF :=
  ⟨rfl, rfl⟩

/-- The three regimes are each inhabited, and the three witnesses are pairwise separated:
each witness lies in its own regime and in neither of the other two. -/
theorem regimes_nonempty_and_distinct :
    (IsReferenceChoice F ρRC ∧ ¬ IsPrescription F ρRC ∧ ¬ IsLaissezFaire ρRC) ∧
    (IsPrescription F ρPres ∧ ¬ IsReferenceChoice F ρPres ∧ ¬ IsLaissezFaire ρPres) ∧
    (IsLaissezFaire ρLF ∧ ¬ IsReferenceChoice F ρLF ∧ ¬ IsPrescription F ρLF) := by
  refine ⟨⟨rc_isReferenceChoice, rc_isReferenceChoice.not_prescription_and_not_laissezFaire⟩,
    ⟨pres_isPrescription, fun h => pres_not_genuineChoice h.2,
      not_laissezFaire_of_acceptable_eq rfl⟩,
    ⟨lf_isLaissezFaire, fun h => h.1 lf_isLaissezFaire,
      (genuineChoice_univ feasible_ρLF).not_prescription⟩⟩

/-- **P2** (concrete): two different methods (`index`, `cache`) both reach the acceptable
outcome. -/
example : index ≠ cache ∧ F index ∈ ρRC.acceptable ∧ F cache ∈ ρRC.acceptable :=
  ⟨by decide, rfl, rfl⟩

/-- Three agents, each using a different method. -/
def assignment : Fin 3 → Method := ![index, cache, queryRewrite]

/-- **P3** (existence): a model in which genuine choice holds, every agent's outcome is
acceptable, and the agents' methods differ. -/
theorem standardization_with_autonomy :
    GenuineChoice F ρRC ∧ OutcomeStandardized F ρRC assignment ∧
      ¬ MethodStandardized assignment := by
  refine ⟨rc_isReferenceChoice.2, fun _ => rfl, fun h => ?_⟩
  exact absurd (h 0 1) (by decide)

end Example

end RCAS
