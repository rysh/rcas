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
* `RCAS.eventually_near_of_stableBand` (F1 with parameters that keep changing inside a stable
  band: the state ends up within a band)
* `RCAS.tendsto_of_stableBand_zero` (band of width `0`: convergence although the parameters
  keep changing)
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

/-! ### Parameters that keep changing inside a stable band

Parameters need not settle. The environment and the requirements change, and an individual's
parameters change even in an unchanged workplace (motivation, health, plateaus). What is assumed
instead is that the parameters stay at a stable *level*: inside a band where `f θ` restores
with rate at least `1 - K` toward a fixed point within distance `ρ` of a reference level
`xBar`. -/

/-- If `a (t+1) ≤ K * a t + c` from time `T` on, with `0 ≤ K < 1`, then for every `η > 0`
eventually `a t ≤ c / (1 - K) + η`. -/
theorem eventually_le_of_affine_bound {a : ℕ → ℝ} {K c : ℝ} (hK0 : 0 ≤ K) (hK1 : K < 1)
    {T : ℕ} (ha : ∀ t ≥ T, a (t + 1) ≤ K * a t + c) {η : ℝ} (hη : 0 < η) :
    ∃ T', ∀ t ≥ T', a t ≤ c / (1 - K) + η := by
  set L := c / (1 - K) with hLdef
  have hK' : 1 - K ≠ 0 := ne_of_gt (by linarith)
  have hL : K * L + c = L := by
    rw [hLdef]
    field_simp
    ring
  have hb : ∀ n, a (n + T) - L ≤ K ^ n * max (a T - L) 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show n + 1 + T = n + T + 1 by omega]
      calc a (n + T + 1) - L ≤ K * a (n + T) + c - L := by
            linarith [ha (n + T) (Nat.le_add_left T n)]
        _ = K * (a (n + T) - L) := by linear_combination hL
        _ ≤ K * (K ^ n * max (a T - L) 0) := mul_le_mul_of_nonneg_left ih hK0
        _ = K ^ (n + 1) * max (a T - L) 0 := by ring
  have hlim : Tendsto (fun n => K ^ n * max (a T - L) 0) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const (max (a T - L) 0)
    rwa [zero_mul] at this
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (Iic_mem_nhds hη))
  refine ⟨N + T, fun t ht => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, t = n + T := ⟨t - T, by omega⟩
  have h1 := hb n
  have h2 : K ^ n * max (a T - L) 0 ≤ η := hN n (by omega)
  linarith

section Band

variable {X Θ : Type*} [NormedAddCommGroup X]

/-- The stable band: parameters `θ` for which `f θ` is a `K`-contraction whose fixed point lies
within distance `ρ` of the reference level `xBar`. -/
def StableBand (f : Θ → X → X) (K : NNReal) (xBar : X) (ρ : ℝ) : Set Θ :=
  {θ | ContractingWith K (f θ) ∧ ∃ xs, f θ xs = xs ∧ dist xs xBar ≤ ρ}

/-- **F1 with changing parameters**: suppose the directives stop from time `T` on, and from
then on the parameters keep changing in any way (for any reason) but stay in the stable band.
Then for every `η > 0` the state eventually stays within `(1 + K) ρ / (1 - K) + η` of the
reference level. The state settles at a level, not at a point. -/
theorem eventually_near_of_stableBand (f : Θ → X → X) {θ : ℕ → Θ} {u x : ℕ → X}
    (hx : ∀ t, x (t + 1) = f (θ t) (x t) + u t) {T : ℕ} (hu : ∀ t ≥ T, u t = 0)
    {K : NNReal} {xBar : X} {ρ : ℝ} (hband : ∀ t ≥ T, θ t ∈ StableBand f K xBar ρ)
    {η : ℝ} (hη : 0 < η) :
    ∃ T', ∀ t ≥ T', dist (x t) xBar ≤ (1 + K) * ρ / (1 - K) + η := by
  have hK1 : (K : ℝ) < 1 := by exact_mod_cast (hband T le_rfl).1.1
  refine eventually_le_of_affine_bound (a := fun t => dist (x t) xBar) (c := (1 + K) * ρ)
    (T := T) K.coe_nonneg hK1 (fun t ht => ?_) hη
  show dist (x (t + 1)) xBar ≤ K * dist (x t) xBar + (1 + K) * ρ
  obtain ⟨hc, xs, hxs, hd⟩ := hband t ht
  rw [hx, hu t ht, add_zero]
  calc dist (f (θ t) (x t)) xBar ≤ dist (f (θ t) (x t)) xs + dist xs xBar := dist_triangle _ _ _
    _ = dist (f (θ t) (x t)) (f (θ t) xs) + dist xs xBar := by rw [hxs]
    _ ≤ K * dist (x t) xs + ρ := add_le_add (hc.toLipschitzWith.dist_le_mul _ _) hd
    _ ≤ K * (dist (x t) xBar + dist xBar xs) + ρ := by
        gcongr
        exact dist_triangle _ _ _
    _ ≤ K * (dist (x t) xBar + ρ) + ρ := by
        gcongr
        rw [dist_comm]
        exact hd
    _ = K * dist (x t) xBar + (1 + K) * ρ := by ring

/-- Band of width `0`: if every parameter in use has its fixed point at `xBar`, the state
converges to `xBar` even though the parameters keep changing. -/
theorem tendsto_of_stableBand_zero (f : Θ → X → X) {θ : ℕ → Θ} {u x : ℕ → X}
    (hx : ∀ t, x (t + 1) = f (θ t) (x t) + u t) {T : ℕ} (hu : ∀ t ≥ T, u t = 0)
    {K : NNReal} {xBar : X} (hband : ∀ t ≥ T, θ t ∈ StableBand f K xBar 0) :
    Tendsto x atTop (𝓝 xBar) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T', hT'⟩ := eventually_near_of_stableBand f hx hu hband (half_pos hε)
  refine ⟨T', fun t ht => ?_⟩
  have := hT' t ht
  rw [mul_zero, zero_div, zero_add] at this
  linarith

end Band

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

/-- A stable band in which the parameter can move: `f θ x = x / 2 + θ / 2` has fixed point `θ`,
and every `θ ∈ [1, 3]` lies in the band of width `1` around the level `2`. -/
example {θ : ℝ} (hθ : θ ∈ Set.Icc (1 : ℝ) 3) :
    θ ∈ StableBand (fun θ x : ℝ => 1 / 2 * x + θ / 2) (Real.nnabs (1 / 2)) 2 1 := by
  refine ⟨contractingWith_affine (by norm_num [abs_of_pos]), θ, by ring, ?_⟩
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hθ.1, hθ.2]

end Example

end RCAS
