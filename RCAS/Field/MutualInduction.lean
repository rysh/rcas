import RCAS.Basic

/-!
# Mutual induction (§5.6)

The preprint leaves the formalization of mutual induction open. Only the smallest solvable
case is treated: two parties with linear mutual coupling,

`x' = x + c * (y - x)`, `y' = y + c * (x - y)`, `0 < c < 1`.

For the general nonlinear many-body case only the definition is given (a coupling map that
contains the leader as one of the dynamical elements); no theorem is stated about it.

## Main results

* `RCAS.mutual_sum_eq` (M1)
* `RCAS.mutual_diff_succ`, `RCAS.mutual_diff_eq` (M2)
* `RCAS.mutual_tendsto` (M3)
* `RCAS.mutual_limit_ne` (M4)
-/

namespace RCAS

open Filter Topology

variable {c : ℝ} {x y : ℕ → ℝ}

/-- **M1**: the sum `x + y` is conserved. -/
theorem mutual_sum_eq (hx : ∀ t, x (t + 1) = x t + c * (y t - x t))
    (hy : ∀ t, y (t + 1) = y t + c * (x t - y t)) (t : ℕ) : x t + y t = x 0 + y 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [hx, hy, ← ih]; ring

/-- **M2**: the difference `x - y` is multiplied by `1 - 2c` at every step. -/
theorem mutual_diff_succ (hx : ∀ t, x (t + 1) = x t + c * (y t - x t))
    (hy : ∀ t, y (t + 1) = y t + c * (x t - y t)) (t : ℕ) :
    x (t + 1) - y (t + 1) = (1 - 2 * c) * (x t - y t) := by
  rw [hx, hy]
  ring

/-- **M2** (closed form). -/
theorem mutual_diff_eq (hx : ∀ t, x (t + 1) = x t + c * (y t - x t))
    (hy : ∀ t, y (t + 1) = y t + c * (x t - y t)) (t : ℕ) :
    x t - y t = (1 - 2 * c) ^ t * (x 0 - y 0) := by
  induction t with
  | zero => simp
  | succ t ih => rw [mutual_diff_succ hx hy, ih, pow_succ]; ring

/-- **M3**: with `0 < c < 1` (so `|1 - 2c| < 1`), both parties converge to the mean of the initial
states. -/
theorem mutual_tendsto (hx : ∀ t, x (t + 1) = x t + c * (y t - x t))
    (hy : ∀ t, y (t + 1) = y t + c * (x t - y t)) (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto x atTop (𝓝 ((x 0 + y 0) / 2)) ∧ Tendsto y atTop (𝓝 ((x 0 + y 0) / 2)) := by
  have hr : |1 - 2 * c| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hd : Tendsto (fun t => (1 - 2 * c) ^ t * (x 0 - y 0)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).mul_const (x 0 - y 0)
    rwa [zero_mul] at this
  have hxe : ∀ t, x t = (x 0 + y 0) / 2 + (1 - 2 * c) ^ t * (x 0 - y 0) / 2 := fun t => by
    have h1 := mutual_sum_eq hx hy t
    have h2 := mutual_diff_eq hx hy t
    linarith
  have hye : ∀ t, y t = (x 0 + y 0) / 2 - (1 - 2 * c) ^ t * (x 0 - y 0) / 2 := fun t => by
    have h1 := mutual_sum_eq hx hy t
    have h2 := mutual_diff_eq hx hy t
    linarith
  constructor
  · have := (hd.div_const 2).const_add ((x 0 + y 0) / 2)
    rw [zero_div, add_zero] at this
    exact this.congr fun t => (hxe t).symm
  · have := (hd.div_const 2).const_sub ((x 0 + y 0) / 2)
    rw [zero_div, sub_zero] at this
    exact this.congr fun t => (hye t).symm

/-- **M4**: if the initial states differ, the common limit differs from both of them. In this
minimal model, the two parties converge to a configuration neither of them held. -/
theorem mutual_limit_ne {x₀ y₀ : ℝ} (h : x₀ ≠ y₀) : (x₀ + y₀) / 2 ≠ x₀ ∧ (x₀ + y₀) / 2 ≠ y₀ := by
  constructor
  · intro h'
    exact h (by linarith)
  · intro h'
    exact h (by linarith)

/-! ### The general case: definition only -/

/-- A coupling map on a population in which the leader is one of the dynamical elements: the
leader's next state is produced by the same coupling map as everyone else's, not imposed from
outside. No theorem is stated about this general (nonlinear, many-body) case. -/
structure LeaderInclusiveCoupling (ι X : Type*) where
  /-- The leader, an ordinary element of the population. -/
  leader : ι
  /-- Next state of each element, given the whole current configuration. -/
  next : (ι → X) → ι → X

namespace Example

/-- The two-party linear case as a leader-inclusive coupling (`true` is the leader). -/
def twoParty (c : ℝ) : LeaderInclusiveCoupling Bool ℝ where
  leader := true
  next z i := z i + c * (z (!i) - z i)

example (c : ℝ) (z : Bool → ℝ) :
    (twoParty c).next z true = z true + c * (z false - z true) := rfl

end Example

end RCAS
