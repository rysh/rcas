import RCAS.SelfManaging
import RCAS.Field.Forcing

/-!
# The strong self-managing state (§4.10 after the Field extension §5.1)

The Phase 1 definition `RCAS.SelfManaging` is strengthened with the two operations of §5.1:
the team "can run the fast dynamics autonomously and update the slow parameters autonomously".

* fast dynamics run autonomously: no directive forcing, `u t = 0`. Here `u` is a push on the
  state from outside the team's own dynamics `f θ` — the manager's (or the wider
  organization's) directives. Interaction among team members is part of `f θ`, and changes in
  the environment and in requirements act on the parameters `θ`, not on `u`;
* slow parameters are updated by the team's own operator,
  `θ (t+1) = paramUpdate (θ t) (x t) (ω t)`, where `ω t` is the outside influence at time `t`
  (environment, requirements, private life, health, …) to which the team's update responds.

Parameters are **not** assumed to settle at a constant. They may change at every step. What is
assumed is that they stay at a stable level, i.e. inside a stable band
(`RCAS.StableBand`); the conclusion is that the state stays within a band, not that it
converges to a point.

`RCAS.SelfManaging.lean` is not modified (Phase 2 does not rewrite Phase 1); the strong state is
built on top of it here.

## Main results

* `RCAS.SelfManagingStrong.toSelfManaging` (the strong state is a self-managing state)
* `RCAS.eventually_selfManagingStrong` (SM1 for the strong state)
* `RCAS.SelfManagingStrong.mem_stableBand` (if the team's update keeps the band whatever the
  outside influence, the parameters stay in the band)
* `RCAS.SelfManagingStrong.eventually_near` (in the strong state with parameters in the band,
  the state eventually stays near the reference level)
* `RCAS.SelfManagingStrong.tendsto_of_fixed_level` (band of width `0`)
-/

namespace RCAS

open Filter Topology

variable {ι κ 𝓡 X Θ Ω : Type*} [NormedAddCommGroup X]

/-- The strong self-managing state at time `t`: the four Phase 1 conditions, no directive
forcing on the fast dynamics, and the slow parameters updated by the team's own operator in
response to the outside influence `ω t`. -/
structure SelfManagingStrong (k : ℕ → ι → κ → ℝ) (θcap : κ → ℝ) (D : ℕ → ℝ) (δ : ℝ)
    (q : ℕ → ℝ) (qMin : ℝ) (RD : RuleDynamics 𝓡) (R : ℕ → 𝓡) (u x : ℕ → X) (θ : ℕ → Θ)
    (ω : ℕ → Ω) (paramUpdate : Θ → X → Ω → Θ) (t : ℕ) : Prop where
  /-- The four conditions of the Phase 1 definition. -/
  base : SelfManaging k θcap D δ q qMin RD R t
  /-- The fast dynamics run without directive forcing. -/
  autonomousFast : u t = 0
  /-- The slow parameters are updated by the team's own operator. -/
  autonomousSlow : θ (t + 1) = paramUpdate (θ t) (x t) (ω t)

variable {k : ℕ → ι → κ → ℝ} {θcap : κ → ℝ} {D : ℕ → ℝ} {δ : ℝ} {q : ℕ → ℝ} {qMin : ℝ}
  {RD : RuleDynamics 𝓡} {R : ℕ → 𝓡} {u x : ℕ → X} {θ : ℕ → Θ} {ω : ℕ → Ω}
  {paramUpdate : Θ → X → Ω → Θ}

/-- The strong state is in particular a (Phase 1) self-managing state. Immediate from the
definition. -/
theorem SelfManagingStrong.toSelfManaging {t : ℕ}
    (h : SelfManagingStrong k θcap D δ q qMin RD R u x θ ω paramUpdate t) :
    SelfManaging k θcap D δ q qMin RD R t :=
  h.base

/-- **SM1** for the strong state: under the hypotheses of SM1, if moreover the directives stop
from some time on and the team updates the parameters from some time on, the team is
eventually in the strong self-managing state. As in SM1, performance (③) is a hypothesis; so
are the end of directives and the team's taking over the parameter update. -/
theorem eventually_selfManagingStrong {η : ℝ} {L : ℕ → ι → κ → ℝ} {p : ℝ}
    (hk : ∀ t i j, k (t + 1) i j = min 1 (k t i j + η * L t i j)) (hη : 0 ≤ η)
    (hL : ∀ t i j, 0 ≤ L t i j) (hk0 : ∀ i j, k 0 i j ≤ 1) {T₁ : ℕ}
    (hcov : CollectiveCover (k T₁) θcap)
    (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ)
    (hq : ∃ T₃, ∀ t ≥ T₃, qMin ≤ q t)
    (hR : ∃ T₄, ∀ t ≥ T₄, R (t + 1) = RD.update (R t))
    (hu : ∃ T₅, ∀ t ≥ T₅, u t = 0)
    (hθ : ∃ T₆, ∀ t ≥ T₆, θ (t + 1) = paramUpdate (θ t) (x t) (ω t)) :
    ∃ T, ∀ t ≥ T, SelfManagingStrong k θcap D δ q qMin RD R u x θ ω paramUpdate t := by
  have hbase := eventually_selfManaging hk hη hL hk0 hcov hD hp hp1 hδ hq hR
  obtain ⟨T, hT⟩ := (show EventuallyAlways _ from hbase).and
    ((show EventuallyAlways _ from hu).and hθ)
  exact ⟨T, fun t ht => ⟨(hT t ht).1, (hT t ht).2.1, (hT t ht).2.2⟩⟩

/-- If the team's update keeps parameters in a set `S` whatever the state and whatever the
outside influence, and the parameters are in `S` when the strong state begins, they stay in `S`
from then on. -/
theorem SelfManagingStrong.mem_stableBand {S : Set Θ} {T : ℕ}
    (hSM : ∀ t ≥ T, SelfManagingStrong k θcap D δ q qMin RD R u x θ ω paramUpdate t)
    (hθT : θ T ∈ S) (hinv : ∀ θ' ∈ S, ∀ x' ω', paramUpdate θ' x' ω' ∈ S) :
    ∀ t ≥ T, θ t ∈ S := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hθT
  | succ n hn ih =>
    rw [(hSM n hn).autonomousSlow]
    exact hinv _ ih _ _

/-- In the strong state, the outcome is held at the level the parameters keep, not by
directives. Suppose the strong state holds from time `T` on, the fast dynamics are
`x (t+1) = f (θ t) (x t) + u t`, and from `T` on the parameters — which may keep changing — stay in
the stable band around `xBar`. Then for every `η > 0` the state eventually stays within
`(1 + K) ρ / (1 - K) + η` of `xBar`, whatever directives were given before `T`. That the
parameters stay in the band is a hypothesis. -/
theorem SelfManagingStrong.eventually_near (f : Θ → X → X)
    (hx : ∀ t, x (t + 1) = f (θ t) (x t) + u t) {T : ℕ}
    (hSM : ∀ t ≥ T, SelfManagingStrong k θcap D δ q qMin RD R u x θ ω paramUpdate t)
    {K : NNReal} {xBar : X} {ρ : ℝ} (hband : ∀ t ≥ T, θ t ∈ StableBand f K xBar ρ)
    {η : ℝ} (hη : 0 < η) :
    ∃ T', ∀ t ≥ T', dist (x t) xBar ≤ (1 + K) * ρ / (1 - K) + η :=
  eventually_near_of_stableBand f hx (fun t ht => (hSM t ht).autonomousFast) hband hη

/-- The same, with the band hypothesis derived from the team's update: if the team's update
keeps the parameters in the stable band whatever the outside influence, and they are in the band
when the strong state begins, the state eventually stays near the reference level. -/
theorem SelfManagingStrong.eventually_near_of_invariant (f : Θ → X → X)
    (hx : ∀ t, x (t + 1) = f (θ t) (x t) + u t) {T : ℕ}
    (hSM : ∀ t ≥ T, SelfManagingStrong k θcap D δ q qMin RD R u x θ ω paramUpdate t)
    {K : NNReal} {xBar : X} {ρ : ℝ} (hθT : θ T ∈ StableBand f K xBar ρ)
    (hinv : ∀ θ' ∈ StableBand f K xBar ρ, ∀ x' ω', paramUpdate θ' x' ω' ∈ StableBand f K xBar ρ)
    {η : ℝ} (hη : 0 < η) :
    ∃ T', ∀ t ≥ T', dist (x t) xBar ≤ (1 + K) * ρ / (1 - K) + η :=
  SelfManagingStrong.eventually_near f hx hSM (SelfManagingStrong.mem_stableBand hSM hθT hinv) hη

/-- Band of width `0`: if every parameter the team uses has its fixed point at `xBar`, the state
converges to `xBar`, although the parameters themselves keep changing. -/
theorem SelfManagingStrong.tendsto_of_fixed_level (f : Θ → X → X)
    (hx : ∀ t, x (t + 1) = f (θ t) (x t) + u t) {T : ℕ}
    (hSM : ∀ t ≥ T, SelfManagingStrong k θcap D δ q qMin RD R u x θ ω paramUpdate t)
    {K : NNReal} {xBar : X} (hband : ∀ t ≥ T, θ t ∈ StableBand f K xBar 0) :
    Tendsto x atTop (𝓝 xBar) :=
  tendsto_of_stableBand_zero f hx (fun t ht => (hSM t ht).autonomousFast) hband

end RCAS
