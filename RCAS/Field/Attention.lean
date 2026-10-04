import RCAS.Field.Threshold

/-!
# Multi-layer attention (§5.5)

Each agent attends at a layer `ℓ i : Λ`. Alignment between layers is `al : Λ → Λ → ℝ`, with
`0 ≤ al ≤ 1` and `al l l = 1` (premises, as structure fields). The effective weight is

`wEff i j = w i j * al (ℓ i) (ℓ j)`.

## Main results

* `RCAS.effWeight_le` (A1)
* `RCAS.effWeight_eq_of_aligned` (A2)
* `RCAS.iterate_step_effWeight_subset_aligned`, `RCAS.finalAdopters_effWeight_subset_aligned`
  (A3, with T3)
-/

namespace RCAS

/-- Alignment between attention layers. -/
structure Alignment (Λ : Type*) where
  /-- Degree of alignment between two layers. -/
  al : Λ → Λ → ℝ
  /-- Premise: alignment is nonnegative. -/
  nonneg : ∀ l m, 0 ≤ al l m
  /-- Premise: alignment is at most `1`. -/
  le_one : ∀ l m, al l m ≤ 1
  /-- Premise: a layer is fully aligned with itself. -/
  self : ∀ l, al l l = 1

variable {ι Λ : Type*}

/-- Effective weight: the coupling attenuated by the alignment of the two agents' layers. -/
def effWeight (w : ι → ι → ℝ) (A : Alignment Λ) (ℓ : ι → Λ) : ι → ι → ℝ :=
  fun i j => w i j * A.al (ℓ i) (ℓ j)

variable {w : ι → ι → ℝ} (A : Alignment Λ)

theorem effWeight_nonneg (hw : ∀ i j, 0 ≤ w i j) (ℓ : ι → Λ) (i j : ι) :
    0 ≤ effWeight w A ℓ i j :=
  mul_nonneg (hw i j) (A.nonneg _ _)

/-- **A1**: with nonnegative weights, the effective weight never exceeds the weight. -/
theorem effWeight_le (hw : ∀ i j, 0 ≤ w i j) (ℓ : ι → Λ) (i j : ι) :
    effWeight w A ℓ i j ≤ w i j :=
  mul_le_of_le_one_right (hw i j) (A.le_one _ _)

/-- **A2**: if everyone attends at the same layer, the effective weight is the weight. -/
theorem effWeight_eq_of_aligned {ℓ : ι → Λ} (hℓ : ∀ i j, ℓ i = ℓ j) : effWeight w A ℓ = w := by
  funext i j
  rw [effWeight, hℓ i j, A.self, mul_one]

variable [Fintype ι] [DecidableEq ι] {θ : ι → ℝ}

/-- **A3** (alignment does not reduce propagation), at every time: the adopter set with everyone
at layer `l` contains the adopter set under any layer assignment `ℓ`. Composition of A1, A2 and
T3. -/
theorem iterate_step_effWeight_subset_aligned (hw : ∀ i j, 0 ≤ w i j) (ℓ : ι → Λ) (l : Λ)
    (A₀ : Finset ι) (t : ℕ) :
    (step (effWeight w A ℓ) θ)^[t] A₀ ⊆ (step (effWeight w A fun _ => l) θ)^[t] A₀ := by
  rw [effWeight_eq_of_aligned A (ℓ := fun _ => l) fun _ _ => rfl]
  exact iterate_step_mono_weight (effWeight_nonneg A hw ℓ) (effWeight_le A hw ℓ) A₀ t

/-- **A3** for the final adopter sets. -/
theorem finalAdopters_effWeight_subset_aligned (hw : ∀ i j, 0 ≤ w i j) (ℓ : ι → Λ) (l : Λ)
    (A₀ : Finset ι) :
    finalAdopters (effWeight w A ℓ) θ A₀ ⊆ finalAdopters (effWeight w A fun _ => l) θ A₀ :=
  iterate_step_effWeight_subset_aligned A hw ℓ l A₀ _

namespace Example

/-- Two layers that do not hear each other at all. -/
def disjointLayers : Alignment Bool where
  al l m := if l = m then 1 else 0
  nonneg l m := by split_ifs <;> norm_num
  le_one l m := by split_ifs <;> norm_num
  self l := by simp

/-- Misaligned layers cut a unit coupling to zero. -/
example :
    effWeight (fun _ _ : Fin 2 => (1 : ℝ)) disjointLayers (fun i => decide (i = 0)) 1 0 = 0 := by
  simp [effWeight, disjointLayers]

end Example

end RCAS
