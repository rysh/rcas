import RCAS.Basic

/-!
# Coupling and propagation (§5.3)

Coupling matrix `W : Matrix ι ι ℝ`; `W j i` is the direct influence of agent `i` on agent `j`.
Linear propagation: `x (t+1) = W.mulVec (x t)`.

Comparing candidate transmissivities `τ(G)` (density, spectral radius, algebraic connectivity)
and convergence to consensus are outside the scope of this formalization.

## Main results

* `RCAS.propagate_eq` (`x t = (W ^ t).mulVec (x 0)`)
* `RCAS.influence_eq` (CP1)
* `RCAS.influence_eq_zero_of_uncoupled` (CP2)
* `RCAS.pow_apply_eq_zero_of_not_walk`, `RCAS.influence_eq_zero_of_no_walk` (CP3)
-/

namespace RCAS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Linear propagation reduces to matrix powers: `x t = (W ^ t).mulVec (x 0)`. -/
theorem propagate_eq (W : Matrix ι ι ℝ) {x : ℕ → ι → ℝ} (hx : ∀ t, x (t + 1) = W.mulVec (x t))
    (t : ℕ) : x t = (W ^ t).mulVec (x 0) := by
  induction t with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ t ih => rw [hx, ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- **CP1**: the influence of a unit perturbation of agent `i` on agent `j` after `t` steps is
`(W ^ t) j i`. -/
theorem influence_eq (W : Matrix ι ι ℝ) {x : ℕ → ι → ℝ} (hx : ∀ t, x (t + 1) = W.mulVec (x t))
    {i : ι} (hx0 : x 0 = Pi.single i 1) (t : ℕ) (j : ι) : x t j = (W ^ t) j i := by
  rw [propagate_eq W hx, hx0, Matrix.mulVec_single_one]
  rfl

/-- **CP2** (no medium, no propagation): without coupling (`W = 1`) a unit perturbation of `i`
never reaches `j ≠ i`. -/
theorem influence_eq_zero_of_uncoupled {x : ℕ → ι → ℝ}
    (hx : ∀ t, x (t + 1) = (1 : Matrix ι ι ℝ).mulVec (x t)) {i j : ι} (hij : i ≠ j)
    (hx0 : x 0 = Pi.single i 1) (t : ℕ) : x t j = 0 := by
  rw [influence_eq 1 hx hx0, one_pow, Matrix.one_apply_ne hij.symm]

/-- `HasWalk W t i j`: there is a walk of length `t` from `i` to `j` along nonzero couplings
(an edge `k → j` when `W j k ≠ 0`). -/
inductive HasWalk (W : Matrix ι ι ℝ) : ℕ → ι → ι → Prop
  | refl (i : ι) : HasWalk W 0 i i
  | step {t : ℕ} {i k j : ι} : HasWalk W t i k → W j k ≠ 0 → HasWalk W (t + 1) i j

/-- **CP3** (matrix form): without a walk of length `t` from `i` to `j`, the entry
`(W ^ t) j i` vanishes. -/
theorem pow_apply_eq_zero_of_not_walk (W : Matrix ι ι ℝ) {t : ℕ} {i j : ι}
    (h : ¬ HasWalk W t i j) : (W ^ t) j i = 0 := by
  induction t generalizing j with
  | zero =>
    have hji : j ≠ i := by
      rintro rfl
      exact h (HasWalk.refl j)
    rw [pow_zero, Matrix.one_apply_ne hji]
  | succ t ih =>
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hW : W j k = 0
    · rw [hW, zero_mul]
    · rw [ih fun hk => h (HasWalk.step hk hW), mul_zero]

/-- **CP3**: if there is no walk from `i` to `j` of any length, a unit perturbation of `i`
never reaches `j`. -/
theorem influence_eq_zero_of_no_walk (W : Matrix ι ι ℝ) {x : ℕ → ι → ℝ}
    (hx : ∀ t, x (t + 1) = W.mulVec (x t)) {i j : ι} (hx0 : x 0 = Pi.single i 1)
    (hno : ∀ t, ¬ HasWalk W t i j) (t : ℕ) : x t j = 0 := by
  rw [influence_eq W hx hx0]
  exact pow_apply_eq_zero_of_not_walk W (hno t)

namespace Example

/-- A chain `0 → 1 → 2`. -/
def chain : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 1, 0, 0; 0, 1, 0]

/-- The perturbation of `0` has not reached `2` after one step, and has after two. -/
example : (chain ^ 1) 2 0 = 0 ∧ (chain ^ 2) 2 0 = 1 := by
  constructor
  · simp [chain]
  · simp [chain, sq, Matrix.mul_apply, Fin.sum_univ_three]

end Example

end RCAS
