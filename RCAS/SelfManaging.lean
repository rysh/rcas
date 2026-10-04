import RCAS.Capability
import RCAS.Dependence
import RCAS.RuleUpdate

/-!
# The self-managing state (§4.10)

Four conditions at time `t`:

1. collective cover, `CollectiveCover (k t) θ` (§4.6);
2. low dependence on the manager, `D t ≤ δ` (§4.7);
3. adequate performance, `qMin ≤ q t`;
4. rule-update capability: the rule set is updated by the team's own update operator,
   `R (t + 1) = RD.update (R t)` (§4.4).

This is the Phase 1 definition. The stronger definition after the Field extension (§5.1) —
"can run the fast dynamics autonomously and update the slow parameters autonomously" — belongs
to Phase 2 and will be stated there without changing this file.

## Where "follows" ends and "needs external verification" begins

In `RCAS.eventually_selfManaging` (SM1), conditions 1 and 2 are *derived* from the dynamics of
§4.6 and §4.7. Condition 3 cannot be derived from the Phase 1 model and is a *hypothesis*;
whether it holds is an empirical question (see `docs/EMPIRICAL.md`). Condition 4 is a premise
about who runs the update.

## Main results

* `RCAS.eventually_selfManaging` (SM1)
* `RCAS.performance_not_derivable` (condition ③ does not follow from the other hypotheses)
* `RCAS.SelfManaging.J_le_succ` (under condition 4, the rule evaluation does not drop)
-/

namespace RCAS

variable {ι κ 𝓡 : Type*}

/-- The four conditions of the self-managing state at time `t` (Phase 1 definition). -/
structure SelfManaging (k : ℕ → ι → κ → ℝ) (θ : κ → ℝ) (D : ℕ → ℝ) (δ : ℝ) (q : ℕ → ℝ)
    (qMin : ℝ) (RD : RuleDynamics 𝓡) (R : ℕ → 𝓡) (t : ℕ) : Prop where
  /-- ① Collective cover. -/
  cover : CollectiveCover (k t) θ
  /-- ② Low dependence on the manager. -/
  lowDependence : D t ≤ δ
  /-- ③ Adequate performance. -/
  performance : qMin ≤ q t
  /-- ④ The rule set is updated by the team's own update operator. -/
  teamUpdatesRules : R (t + 1) = RD.update (R t)

/-- Under condition ④ the evaluation of the rule set does not drop over the next step (P8). -/
theorem SelfManaging.J_le_succ {k : ℕ → ι → κ → ℝ} {θ : κ → ℝ} {D : ℕ → ℝ} {δ : ℝ}
    {q : ℕ → ℝ} {qMin : ℝ} {RD : RuleDynamics 𝓡} {R : ℕ → 𝓡} {t : ℕ}
    (h : SelfManaging k θ D δ q qMin RD R t) : RD.J (R t) ≤ RD.J (R (t + 1)) := by
  rw [h.teamUpdatesRules]
  exact RD.J_le_J_update _

/-- **SM1**: suppose

* capability diffuses as in §4.6 (K1) and collective cover holds at some time `T₁`;
* dependence decays as in §4.7 with `0 < p ≤ 1`, and the threshold is `δ > 0`;
* the team runs the rule update from some time on;
* **performance is adequate from some time on — a hypothesis, not a consequence:** the Phase 1
  model does not determine performance, so this is exactly where formal consequence stops and
  external (empirical) verification is required.

Then from some time on the team is in the self-managing state. -/
theorem eventually_selfManaging {k : ℕ → ι → κ → ℝ} {η : ℝ} {L : ℕ → ι → κ → ℝ}
    {θ : κ → ℝ} {D : ℕ → ℝ} {p δ : ℝ} {q : ℕ → ℝ} {qMin : ℝ} {RD : RuleDynamics 𝓡}
    {R : ℕ → 𝓡}
    -- §4.6: diffusion of capability, and cover at some time
    (hk : ∀ t i j, k (t + 1) i j = min 1 (k t i j + η * L t i j)) (hη : 0 ≤ η)
    (hL : ∀ t i j, 0 ≤ L t i j) (hk0 : ∀ i j, k 0 i j ≤ 1) {T₁ : ℕ}
    (hcov : CollectiveCover (k T₁) θ)
    -- §4.7: decay of dependence
    (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ)
    -- ③ performance: assumed, not derived
    (hq : ∃ T₃, ∀ t ≥ T₃, qMin ≤ q t)
    -- ④ the team runs the rule update
    (hR : ∃ T₄, ∀ t ≥ T₄, R (t + 1) = RD.update (R t)) :
    ∃ T, ∀ t ≥ T, SelfManaging k θ D δ q qMin RD R t := by
  have h₁ : EventuallyAlways fun t => CollectiveCover (k t) θ :=
    ⟨T₁, fun _ ht => diffusion_cover_preserved hk hη hL hk0 hcov ht⟩
  have h₂ : EventuallyAlways fun t => D t ≤ δ := dependence_eventually_le hD hp hp1 hδ
  obtain ⟨T, hT⟩ := (h₁.and h₂).and ((show EventuallyAlways _ from hq).and hR)
  exact ⟨T, fun t ht => ⟨(hT t ht).1.1, (hT t ht).1.2, (hT t ht).2.1, (hT t ht).2.2⟩⟩

namespace Example

/-- The one-rule-set team: the update keeps it. -/
def trivialRD : RuleDynamics Unit where
  J _ := 0
  N _ := {()}
  update _ := ()
  stay _ := Finset.mem_singleton_self _
  mem _ := Finset.mem_singleton_self _
  best _ _ _ := le_rfl

/-- The definition is not vacuous: a one-person, one-requirement team with full capability,
no dependence and adequate performance is self-managing at every time. -/
example : ∀ t, SelfManaging (fun _ (_ : Unit) _ => (1 : ℝ)) (fun _ : Unit => 1) (fun _ => 0) 1
    (fun _ => 1) 0 trivialRD (fun _ => ()) t :=
  fun _ => ⟨fun _ => ⟨(), le_rfl⟩, zero_le_one, zero_le_one, rfl⟩

end Example

/-- Condition ③ is not a consequence of the rest: every hypothesis of SM1 other than the
performance hypothesis holds, and yet the team is never in the self-managing state. -/
theorem performance_not_derivable :
    ∃ (k L : ℕ → Unit → Unit → ℝ) (η : ℝ) (θ : Unit → ℝ) (D : ℕ → ℝ) (p δ : ℝ) (q : ℕ → ℝ)
      (qMin : ℝ) (RD : RuleDynamics Unit) (R : ℕ → Unit),
      (∀ t i j, k (t + 1) i j = min 1 (k t i j + η * L t i j)) ∧ 0 ≤ η ∧
      (∀ t i j, 0 ≤ L t i j) ∧ (∀ i j, k 0 i j ≤ 1) ∧ CollectiveCover (k 0) θ ∧
      (∀ t, D (t + 1) = (1 - p) * D t) ∧ 0 < p ∧ p ≤ 1 ∧ 0 < δ ∧
      (∀ t, R (t + 1) = RD.update (R t)) ∧
      ¬ ∃ T, ∀ t ≥ T, SelfManaging k θ D δ q qMin RD R t := by
  refine ⟨fun _ _ _ => 1, fun _ _ _ => 0, 0, fun _ => 1, fun _ => 0, 1, 1, fun _ => 0, 1,
    Example.trivialRD, fun _ => (), fun _ _ _ => by simp, le_rfl, fun _ _ _ => le_rfl,
    fun _ _ => le_rfl, fun _ => ⟨(), le_rfl⟩, fun _ => by simp, one_pos, le_rfl, one_pos,
    fun _ => rfl, ?_⟩
  rintro ⟨T, hT⟩
  have := (hT T le_rfl).performance
  norm_num at this

end RCAS
