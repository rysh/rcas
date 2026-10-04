import Mathlib

/-!
# RCAS: basic conventions

This file fixes the conventions of the Reference–Choice Adaptive System (RCAS) formalization.
"RCAS" is a provisional name; everything lives in the namespace `RCAS`.

Type-variable conventions used throughout (each file declares only what it needs):

* `ι` — agents, with `[Fintype ι] [DecidableEq ι]`;
* `α` — actions / methods;
* `Y` — outcomes;
* `κ` — capabilities (requirements);
* time is discrete, `ℕ`; values are real, `ℝ`.

The global state `S_t = (N, E_t, R_t, K_t, S_t, H_t)` is deliberately *not* bundled into a
single structure. Each file takes only the components it needs as arguments; `SelfManaging.lean`
bundles exactly the components used there.

Modelling discipline:

* assumptions of the model appear only as structure fields or explicit theorem hypotheses
  (the keyword `axiom` is never used);
* conclusions appear as `theorem`s;
* empirical claims are not stated in Lean at all (see `docs/EMPIRICAL.md`).

This file provides the one notion shared by several files: a time-indexed predicate that holds
from some time on.
-/

namespace RCAS

/-- `EventuallyAlways P` : there is a time `T` from which `P t` holds at every `t ≥ T`. -/
def EventuallyAlways (P : ℕ → Prop) : Prop :=
  ∃ T, ∀ t ≥ T, P t

theorem eventuallyAlways_iff {P : ℕ → Prop} :
    EventuallyAlways P ↔ ∀ᶠ t in Filter.atTop, P t := by
  rw [Filter.eventually_atTop]
  rfl

theorem EventuallyAlways.mono {P Q : ℕ → Prop} (h : EventuallyAlways P) (hPQ : ∀ t, P t → Q t) :
    EventuallyAlways Q := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun t ht => hPQ t (hT t ht)⟩

theorem EventuallyAlways.and {P Q : ℕ → Prop} (hP : EventuallyAlways P)
    (hQ : EventuallyAlways Q) : EventuallyAlways (fun t => P t ∧ Q t) := by
  obtain ⟨T₁, h₁⟩ := hP
  obtain ⟨T₂, h₂⟩ := hQ
  exact ⟨max T₁ T₂, fun t ht => ⟨h₁ t (max_le_iff.mp ht).1, h₂ t (max_le_iff.mp ht).2⟩⟩

/-- A predicate that holds at some time and is preserved by one step holds from then on. -/
theorem eventuallyAlways_of_invariant {P : ℕ → Prop} {T : ℕ} (hT : P T)
    (hstep : ∀ t ≥ T, P t → P (t + 1)) : EventuallyAlways P := by
  refine ⟨T, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact hT
  | succ n hn ih => exact hstep n hn ih

end RCAS
