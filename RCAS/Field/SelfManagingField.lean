import RCAS.SelfManaging
import RCAS.Field.Forcing

/-!
# The strong self-managing state (§4.10 after the Field extension §5.1)

The Phase 1 definition `RCAS.SelfManaging` is strengthened with the two operations of §5.1:
the team "can run the fast dynamics autonomously and update the slow parameters autonomously".

* fast dynamics run autonomously: no directive forcing, `u t = 0`;
* slow parameters are updated by the team's own operator, `θ (t+1) = paramUpdate (θ t) (x t)`.

`RCAS.SelfManaging.lean` is not modified (Phase 2 does not rewrite Phase 1); the strong state is
built on top of it here.

## Main results

* `RCAS.SelfManagingStrong.toSelfManaging` (the strong state is a self-managing state)
* `RCAS.eventually_selfManagingStrong` (SM1 for the strong state)
* `RCAS.SelfManagingStrong.tendsto` (in the strong state, the limit is set by the team's
  parameter, not by past directives)
-/

namespace RCAS

open Filter Topology

variable {ι κ 𝓡 X Θ : Type*} [NormedAddCommGroup X]

/-- The strong self-managing state at time `t`: the four Phase 1 conditions, no directive
forcing on the fast dynamics, and the slow parameters updated by the team's own operator. -/
structure SelfManagingStrong (k : ℕ → ι → κ → ℝ) (θcap : κ → ℝ) (D : ℕ → ℝ) (δ : ℝ)
    (q : ℕ → ℝ) (qMin : ℝ) (RD : RuleDynamics 𝓡) (R : ℕ → 𝓡) (u x : ℕ → X) (θ : ℕ → Θ)
    (paramUpdate : Θ → X → Θ) (t : ℕ) : Prop where
  /-- The four conditions of the Phase 1 definition. -/
  base : SelfManaging k θcap D δ q qMin RD R t
  /-- The fast dynamics run without directive forcing. -/
  autonomousFast : u t = 0
  /-- The slow parameters are updated by the team's own operator. -/
  autonomousSlow : θ (t + 1) = paramUpdate (θ t) (x t)

variable {k : ℕ → ι → κ → ℝ} {θcap : κ → ℝ} {D : ℕ → ℝ} {δ : ℝ} {q : ℕ → ℝ} {qMin : ℝ}
  {RD : RuleDynamics 𝓡} {R : ℕ → 𝓡} {u x : ℕ → X} {θ : ℕ → Θ} {paramUpdate : Θ → X → Θ}

/-- The strong state is in particular a (Phase 1) self-managing state. Immediate from the
definition. -/
theorem SelfManagingStrong.toSelfManaging {t : ℕ}
    (h : SelfManagingStrong k θcap D δ q qMin RD R u x θ paramUpdate t) :
    SelfManaging k θcap D δ q qMin RD R t :=
  h.base

/-- **SM1** for the strong state: under the hypotheses of SM1, if moreover directives stop from
some time on and the team updates the parameters from some time on, the team is eventually in
the strong self-managing state. As in SM1, performance (③) is a hypothesis; so are the end of
directives and the team's taking over the parameter update. -/
theorem eventually_selfManagingStrong {η : ℝ} {L : ℕ → ι → κ → ℝ} {p : ℝ}
    (hk : ∀ t i j, k (t + 1) i j = min 1 (k t i j + η * L t i j)) (hη : 0 ≤ η)
    (hL : ∀ t i j, 0 ≤ L t i j) (hk0 : ∀ i j, k 0 i j ≤ 1) {T₁ : ℕ}
    (hcov : CollectiveCover (k T₁) θcap)
    (hD : ∀ t, D (t + 1) = (1 - p) * D t) (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ)
    (hq : ∃ T₃, ∀ t ≥ T₃, qMin ≤ q t)
    (hR : ∃ T₄, ∀ t ≥ T₄, R (t + 1) = RD.update (R t))
    (hu : ∃ T₅, ∀ t ≥ T₅, u t = 0)
    (hθ : ∃ T₆, ∀ t ≥ T₆, θ (t + 1) = paramUpdate (θ t) (x t)) :
    ∃ T, ∀ t ≥ T, SelfManagingStrong k θcap D δ q qMin RD R u x θ paramUpdate t := by
  have hbase := eventually_selfManaging hk hη hL hk0 hcov hD hp hp1 hδ hq hR
  obtain ⟨T, hT⟩ := (show EventuallyAlways _ from hbase).and
    ((show EventuallyAlways _ from hu).and hθ)
  exact ⟨T, fun t ht => ⟨(hT t ht).1, (hT t ht).2.1, (hT t ht).2.2⟩⟩

/-- In the strong state the outcome is set by the team's parameter, not by past directives:
if the strong state holds from some time on, the fast dynamics are
`x (t+1) = f (θ t) (x t) + u t`, and the team's parameter settles at `θStar` with `f θStar` a
contraction with fixed point `xStar`, then `x` converges to `xStar` — whatever directives were
given before. That the team's parameter settles is a hypothesis. -/
theorem SelfManagingStrong.tendsto (f : Θ → X → X) (hx : ∀ t, x (t + 1) = f (θ t) (x t) + u t)
    (hSM : ∃ T, ∀ t ≥ T, SelfManagingStrong k θcap D δ q qMin RD R u x θ paramUpdate t)
    {θStar : Θ} (hsettle : ∃ T', ∀ t ≥ T', θ t = θStar) {K : NNReal}
    (hf : ContractingWith K (f θStar)) {xStar : X} (hfix : f θStar xStar = xStar) :
    Tendsto x atTop (𝓝 xStar) := by
  obtain ⟨T, hT⟩ := hSM
  obtain ⟨T', hT'⟩ := hsettle
  refine tendsto_of_eventually_contracting hf hfix (T := max T T') fun t ht => ?_
  rw [hx, (hT t (le_of_max_le_left ht)).autonomousFast, add_zero,
    hT' t (le_of_max_le_right ht)]

end RCAS
