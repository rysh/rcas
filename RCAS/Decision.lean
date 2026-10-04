import RCAS.Basic

/-!
# Decisions with recorded premises (§4.8)

A decision is produced from premises, evidence and the alternatives considered. When one of its
premises no longer holds in the current environment, the decision becomes a candidate for
reconsideration (it is *reopenable*).

This section is mainly definitional; its mathematical content is thin.

The type variable for premises is written `P` (the specification wrote `Π`, which Mathlib
reserves as binder notation).

## Main results

* `RCAS.Decision.instDecidableReopenable` (P10a)
* `RCAS.Decision.not_reopenable_of_premises_eq_empty` (P10b)
* `RCAS.Decision.Reopenable.mono` (recording more premises detects at least as much)
-/

namespace RCAS

/-- A decision: the premises it rests on, the choice made, and when a premise holds in an
environment. -/
structure Decision (P E δ : Type*) where
  /-- Recorded premises. -/
  premises : Finset P
  /-- The choice that was made. -/
  choice : δ
  /-- `holds e π`: premise `π` holds in environment `e`. -/
  holds : E → P → Prop

namespace Decision

variable {P E δ : Type*}

/-- A decision is reopenable in environment `e` when some recorded premise fails there. -/
def Reopenable (d : Decision P E δ) (e : E) : Prop :=
  ∃ π ∈ d.premises, ¬ d.holds e π

/-- **P10a**: if whether a premise holds is decidable, whether a decision is reopenable is
decidable. Recording premises makes staleness mechanically checkable. -/
instance instDecidableReopenable (d : Decision P E δ) (e : E) [DecidablePred (d.holds e)] :
    Decidable (d.Reopenable e) :=
  inferInstanceAs (Decidable (∃ π ∈ d.premises, ¬ d.holds e π))

/-- **P10b**: a decision that records no premises is never reopenable. Immediate from the
definition. -/
theorem not_reopenable_of_premises_eq_empty {d : Decision P E δ} (h : d.premises = ∅) (e : E) :
    ¬ d.Reopenable e := by
  simp [Reopenable, h]

/-- Recording more premises (with the same meaning) detects staleness at least as often. -/
theorem Reopenable.mono {d d' : Decision P E δ} (hprem : d.premises ⊆ d'.premises)
    (hholds : d.holds = d'.holds) {e : E} (h : d.Reopenable e) : d'.Reopenable e := by
  obtain ⟨π, hπ, hfail⟩ := h
  exact ⟨π, hprem hπ, hholds ▸ hfail⟩

end Decision

namespace Example

/-- Environment: daily traffic and team size. -/
structure Env where
  /-- Daily traffic. -/
  traffic : ℕ
  /-- Team size. -/
  teamSize : ℕ

/-- Two premises: `true` — traffic at most 1000; `false` — at least three people. -/
def check (e : Env) : Bool → Bool
  | true => decide (e.traffic ≤ 1000)
  | false => decide (3 ≤ e.teamSize)

/-- "Use a single database server", resting on both premises. -/
def d : Decision Bool Env String where
  premises := {true, false}
  choice := "single database server"
  holds e π := check e π = true

instance (e : Env) : DecidablePred (d.holds e) :=
  fun π => inferInstanceAs (Decidable (check e π = true))

/-- P10a in action: reopenability is computed by `decide`. -/
example : ¬ d.Reopenable ⟨500, 4⟩ := by decide

example : d.Reopenable ⟨5000, 4⟩ := by decide

/-- The same choice without recorded premises can never be reopened. -/
example : ¬ ({ d with premises := ∅ } : Decision Bool Env String).Reopenable ⟨5000, 4⟩ :=
  Decision.not_reopenable_of_premises_eq_empty rfl _

end Example

end RCAS
