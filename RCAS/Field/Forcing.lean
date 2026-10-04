import RCAS.Basic

/-!
# Directive versus constraint (§5.1)

Fast dynamics `x (t+1) = f θ (x t) + u t`:

* `u` is a forcing applied to the state — a **directive**;
* `θ` is a parameter that shapes the landscape `f θ` — a **constraint**.

F1: when `f θ` is a contraction with fixed point `x*` and the forcing stops at some time, the
state converges to `x*` whatever the forcing was before: a directive does not persist.

F2 (scalar linear case `x (t+1) = c * x t + b`, `|c| < 1`): the limit is `b / (1 - c)`. It is
moved by the parameter `b` and not by any past forcing. Together with F1, this is the formal
content of "a directive and a constraint are different operations, not different degrees of the
same operation".

## Main results

* `RCAS.tendsto_of_eventually_contracting` (generic lemma)
* `RCAS.forcing_does_not_persist` (F1)
* `RCAS.forcing_history_irrelevant` (F1, two histories, one limit)
* `RCAS.scalar_tendsto` (F2, the limit is `b / (1 - c)`)
* `RCAS.directive_vs_constraint` (F2, limits coincide iff the parameters coincide)
-/

namespace RCAS

open Filter Topology

section Metric

variable {X : Type*} [MetricSpace X]

/-- If from time `T` on the state evolves by a contraction `g` with fixed point `xStar`, the
state converges to `xStar`, whatever happened before `T`. -/
theorem tendsto_of_eventually_contracting {g : X → X} {K : NNReal} (hg : ContractingWith K g)
    {xStar : X} (hfix : g xStar = xStar) {x : ℕ → X} {T : ℕ}
    (hx : ∀ t ≥ T, x (t + 1) = g (x t)) : Tendsto x atTop (𝓝 xStar) := by
  have hiter : ∀ n, x (n + T) = g^[n] (x T) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ← ih, show n + 1 + T = n + T + 1 by omega]
      exact hx _ (Nat.le_add_left T n)
  have hdist : ∀ n, dist (x (n + T)) xStar ≤ (K : ℝ) ^ n * dist (x T) xStar := by
    intro n
    calc dist (x (n + T)) xStar = dist (g^[n] (x T)) (g^[n] xStar) := by
          rw [hiter, Function.iterate_fixed hfix]
      _ ≤ ((K ^ n : NNReal) : ℝ) * dist (x T) xStar :=
          (hg.toLipschitzWith.iterate n).dist_le_mul _ _
      _ = (K : ℝ) ^ n * dist (x T) xStar := by push_cast; ring
  have hK : (K : ℝ) < 1 := by exact_mod_cast hg.1
  have hlim : Tendsto (fun n => (K : ℝ) ^ n * dist (x T) xStar) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one K.coe_nonneg hK).mul_const (dist (x T) xStar)
    rwa [zero_mul] at this
  have hshift : Tendsto (fun n => x (n + T)) atTop (𝓝 xStar) :=
    tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) hdist hlim)
  exact (tendsto_add_atTop_iff_nat T).mp hshift

end Metric

section Forcing

variable {X Θ : Type*} [NormedAddCommGroup X]

/-- **F1** (a directive does not persist): if `f θ` is a contraction with fixed point `xStar`
and the forcing `u` vanishes from time `T` on, then the state converges to `xStar`, whatever the
forcing was before `T` and whatever the initial state. -/
theorem forcing_does_not_persist (f : Θ → X → X) (θ : Θ) {K : NNReal}
    (hf : ContractingWith K (f θ)) {xStar : X} (hfix : f θ xStar = xStar) {u x : ℕ → X}
    (hx : ∀ t, x (t + 1) = f θ (x t) + u t) {T : ℕ} (hu : ∀ t ≥ T, u t = 0) :
    Tendsto x atTop (𝓝 xStar) :=
  tendsto_of_eventually_contracting hf hfix fun t ht => by rw [hx, hu t ht, add_zero]

/-- **F1** (two histories, one limit): two trajectories under the same parameter, with
different initial states and different forcing histories that both stop eventually, have the
same limit. -/
theorem forcing_history_irrelevant (f : Θ → X → X) (θ : Θ) {K : NNReal}
    (hf : ContractingWith K (f θ)) {xStar : X} (hfix : f θ xStar = xStar) {u u' x x' : ℕ → X}
    (hx : ∀ t, x (t + 1) = f θ (x t) + u t) (hx' : ∀ t, x' (t + 1) = f θ (x' t) + u' t)
    {T T' : ℕ} (hu : ∀ t ≥ T, u t = 0) (hu' : ∀ t ≥ T', u' t = 0) :
    ∃ L, Tendsto x atTop (𝓝 L) ∧ Tendsto x' atTop (𝓝 L) :=
  ⟨xStar, forcing_does_not_persist f θ hf hfix hx hu,
    forcing_does_not_persist f θ hf hfix hx' hu'⟩

end Forcing

/-! ### The scalar linear case (F2) -/

section Scalar

variable {c b : ℝ}

/-- The map `x ↦ c * x + b` is a contraction with constant `|c|` when `|c| < 1`. -/
theorem contractingWith_affine (hc : |c| < 1) :
    ContractingWith (Real.nnabs c) (fun x : ℝ => c * x + b) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_nnabs, NNReal.coe_one]
    exact hc
  · rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, show c * x + b - (c * y + b) = c * (x - y) by
      ring, abs_mul]

/-- `b / (1 - c)` is the fixed point of `x ↦ c * x + b`. -/
theorem affine_fixed (hc : |c| < 1) : c * (b / (1 - c)) + b = b / (1 - c) := by
  have h : 1 - c ≠ 0 := by
    intro h
    have : c = 1 := by linarith
    rw [this, abs_one] at hc
    exact lt_irrefl _ hc
  field_simp
  ring

/-- **F2** (the limit is set by the parameter): `x (t+1) = c * x t + b + u t` with `|c| < 1` and a
forcing that stops eventually converges to `b / (1 - c)`. -/
theorem scalar_tendsto (hc : |c| < 1) {x u : ℕ → ℝ} (hx : ∀ t, x (t + 1) = c * x t + b + u t)
    {T : ℕ} (hu : ∀ t ≥ T, u t = 0) : Tendsto x atTop (𝓝 (b / (1 - c))) :=
  tendsto_of_eventually_contracting (contractingWith_affine hc) (affine_fixed hc)
    fun t ht => by rw [hx, hu t ht, add_zero]

/-- The fixed point `b / (1 - c)` is injective in the parameter `b`. -/
theorem affine_fixed_injective (hc : |c| < 1) {b b' : ℝ} :
    b / (1 - c) = b' / (1 - c) ↔ b = b' := by
  have h : 1 - c ≠ 0 := by
    intro h
    have : c = 1 := by linarith
    rw [this, abs_one] at hc
    exact lt_irrefl _ hc
  exact div_left_inj' h

/-- **F2** (directive versus constraint): take two trajectories with the same `c` (`|c| < 1`),
parameters `b` and `b'`, arbitrary initial states and arbitrary forcing histories that stop
eventually. Both converge, and their limits coincide **if and only if** `b = b'`. Changing the
parameter moves the limit; no past forcing does. -/
theorem directive_vs_constraint (hc : |c| < 1) {b b' : ℝ} {x x' u u' : ℕ → ℝ}
    (hx : ∀ t, x (t + 1) = c * x t + b + u t) (hx' : ∀ t, x' (t + 1) = c * x' t + b' + u' t)
    {T T' : ℕ} (hu : ∀ t ≥ T, u t = 0) (hu' : ∀ t ≥ T', u' t = 0) :
    ∃ L L', Tendsto x atTop (𝓝 L) ∧ Tendsto x' atTop (𝓝 L') ∧ (L = L' ↔ b = b') :=
  ⟨_, _, scalar_tendsto hc hx hu, scalar_tendsto hc hx' hu', affine_fixed_injective hc⟩

end Scalar

namespace Example

/-- A strong directive (`u 0 = 100`) followed by none: the state still converges to the fixed
point `2 / (1 - 1/2) = 4` set by the parameter `b = 2`. -/
example {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) = 1 / 2 * x t + 2 + (if t = 0 then 100 else 0)) :
    Tendsto x atTop (𝓝 4) := by
  have := scalar_tendsto (c := 1 / 2) (b := 2) (by norm_num [abs_of_pos]) hx (T := 1)
    (fun t ht => by simp [show t ≠ 0 by omega])
  norm_num at this
  exact this

end Example

end RCAS
