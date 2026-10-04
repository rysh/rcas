import RCAS.Basic

/-!
# Stuart–Landau amplitude: equilibria and linear restoring rate (§5.2)

Only **static** properties of the right-hand side of the amplitude equation

`g μ r = μ * r - r ^ 3`, `r ≥ 0`,

are formalized: its zeros and its derivative at the zeros. The flow of the ODE, the Hopf
bifurcation and the centre manifold are outside the scope of this formalization (see
`docs/CORRESPONDENCE.md`). In particular, the sign of `deriv (g μ)` at an equilibrium is stated
as a property of `g`, not as a theorem about the stability of solutions.

## Main results

* `RCAS.slRhs_eq_zero_iff_of_nonpos` (SL1)
* `RCAS.slRhs_eq_zero_iff_of_pos` (SL2)
* `RCAS.deriv_slRhs_zero`, `RCAS.deriv_slRhs_sqrt` (SL3; the second with `0 ≤ μ`, see
  `RCAS.deriv_slRhs_sqrt_needs_nonneg`)
* `RCAS.deriv_slRhs_zero_at_criticality` (the restoring rate vanishes at `μ = 0`)
-/

namespace RCAS

/-- Right-hand side of the Stuart–Landau amplitude equation. -/
def slRhs (μ r : ℝ) : ℝ :=
  μ * r - r ^ 3

variable {μ r : ℝ}

theorem slRhs_eq_mul (μ r : ℝ) : slRhs μ r = r * (μ - r ^ 2) := by
  unfold slRhs
  ring

/-- **SL1**: for `μ ≤ 0`, the only zero with `r ≥ 0` is `r = 0`. -/
theorem slRhs_eq_zero_iff_of_nonpos (hμ : μ ≤ 0) (hr : 0 ≤ r) : slRhs μ r = 0 ↔ r = 0 := by
  constructor
  · intro h
    rw [slRhs_eq_mul] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact le_antisymm (by nlinarith) hr
  · rintro rfl
    simp [slRhs]

/-- **SL2**: for `μ > 0`, the zeros with `r ≥ 0` are `r = 0` and `r = √μ`. -/
theorem slRhs_eq_zero_iff_of_pos (hμ : 0 < μ) (hr : 0 ≤ r) :
    slRhs μ r = 0 ↔ r = 0 ∨ r = Real.sqrt μ := by
  constructor
  · intro h
    rw [slRhs_eq_mul] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · right
      rw [show μ = r ^ 2 by linarith, Real.sqrt_sq hr]
  · rintro (rfl | rfl)
    · simp [slRhs]
    · rw [slRhs_eq_mul, Real.sq_sqrt hμ.le, sub_self, mul_zero]

/-- The derivative of `g μ` at `r` is `μ - 3 r²`. -/
theorem hasDerivAt_slRhs (μ r : ℝ) : HasDerivAt (slRhs μ) (μ - 3 * r ^ 2) r := by
  have := ((hasDerivAt_id r).const_mul μ).sub (hasDerivAt_pow 3 r)
  convert this using 1
  · ext x
    simp [slRhs]
  · norm_num

theorem deriv_slRhs (μ r : ℝ) : deriv (slRhs μ) r = μ - 3 * r ^ 2 :=
  (hasDerivAt_slRhs μ r).deriv

/-- **SL3** (at the origin): `deriv (g μ) 0 = μ`. -/
theorem deriv_slRhs_zero (μ : ℝ) : deriv (slRhs μ) 0 = μ := by
  simp [deriv_slRhs]

/-- **SL3** (on the branch): for `μ ≥ 0`, `deriv (g μ) (√μ) = -2 * μ`. The restoring rate is
proportional to `μ`. -/
theorem deriv_slRhs_sqrt (hμ : 0 ≤ μ) : deriv (slRhs μ) (Real.sqrt μ) = -2 * μ := by
  rw [deriv_slRhs, Real.sq_sqrt hμ]
  ring

/-- The hypothesis `0 ≤ μ` in SL3 (branch) is needed: for `μ < 0`, `√μ = 0` in Mathlib, and the
derivative there is `μ`, not `-2 * μ`. -/
theorem deriv_slRhs_sqrt_needs_nonneg : deriv (slRhs (-1)) (Real.sqrt (-1)) ≠ -2 * (-1) := by
  rw [Real.sqrt_eq_zero_of_nonpos (by norm_num), deriv_slRhs_zero]
  norm_num

/-- At criticality `μ = 0` the restoring rate vanishes. -/
theorem deriv_slRhs_zero_at_criticality : deriv (slRhs 0) 0 = 0 :=
  deriv_slRhs_zero 0

/-- Sign of the linear rate: for `μ < 0` the origin is restoring (negative rate); for `μ > 0`
the origin is repelling and the branch `√μ` is restoring. -/
theorem deriv_slRhs_signs :
    (μ < 0 → deriv (slRhs μ) 0 < 0) ∧
    (0 < μ → 0 < deriv (slRhs μ) 0 ∧ deriv (slRhs μ) (Real.sqrt μ) < 0) := by
  refine ⟨fun h => by rwa [deriv_slRhs_zero], fun h => ⟨by rwa [deriv_slRhs_zero], ?_⟩⟩
  rw [deriv_slRhs_sqrt h.le]
  linarith

end RCAS
