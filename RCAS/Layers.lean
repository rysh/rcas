import RCAS.Basic

/-!
# Three nested layers (§4.3)

The organization sets a boundary `orgAllowed` on actions. Inside it the team chooses a rule
`R ∈ teamRules`. Under a rule `R` the individual chooses an action in `actionsOf R`.

The nesting condition `sound` — every action allowed under an admissible team rule is inside the
organizational boundary — is a **premise** of the model (a structure field), not a conclusion.
`RCAS.sound_not_automatic` shows that it does not follow from the rest of the data.

## Main results

* `RCAS.ThreeLayer.mem_orgAllowed` (P12)
-/

namespace RCAS

/-- Organization boundary, team rules inside it, individual actions inside the rules. -/
structure ThreeLayer (α ρ : Type*) where
  /-- Actions the organizational boundary allows. -/
  orgAllowed : Set α
  /-- Team rules admissible within the boundary. -/
  teamRules : Set ρ
  /-- Actions an individual may choose under a rule. -/
  actionsOf : ρ → Set α
  /-- Premise: admissible team rules only allow actions inside the organizational boundary. -/
  sound : ∀ R ∈ teamRules, actionsOf R ⊆ orgAllowed

variable {α ρ : Type*}

/-- **P12**: an action an individual chooses under an admissible team rule lies inside the
organizational boundary. Immediate from the premise `sound`. -/
theorem ThreeLayer.mem_orgAllowed (L : ThreeLayer α ρ) {R : ρ} {a : α} (hR : R ∈ L.teamRules)
    (ha : a ∈ L.actionsOf R) : a ∈ L.orgAllowed :=
  L.sound R hR ha

/-- The nesting premise is independent of the other data: there are boundary, rules and
action sets for which it fails. -/
theorem sound_not_automatic :
    ∃ (orgAllowed : Set Bool) (teamRules : Set Unit) (actionsOf : Unit → Set Bool),
      ¬ ∀ R ∈ teamRules, actionsOf R ⊆ orgAllowed :=
  ⟨∅, Set.univ, fun _ => Set.univ, fun h => h () trivial (Set.mem_univ true)⟩

namespace Example

/-- A three-layer system with real choice at every layer: the organization forbids one action
out of three, two team rules are admissible, and each rule leaves two actions. -/
def L : ThreeLayer (Fin 3) Bool where
  orgAllowed := {0, 1}
  teamRules := Set.univ
  actionsOf _ := {0, 1}
  sound _ _ := subset_rfl

example : (2 : Fin 3) ∉ L.orgAllowed := by simp [L]
example : (L.actionsOf true).Nontrivial := ⟨0, by simp [L], 1, by simp [L], by decide⟩

end Example

end RCAS
