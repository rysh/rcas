import RCAS.Performance

/-!
# Operating modes: diffusion and specialization phases (survey addition §3)

A team may switch on its own between a phase that spreads knowledge (diffusion, `η > 0`) and a
phase in which each member deepens their own expertise (specialization, `η = 0`). The rate `η`
is then a choice of the team over time, `modeSchedule`.

**Model A** feeds `modeSchedule` into `RCAS.KnowledgeSharing` (used as is). There, `η = 0` keeps
every member other than the top member unchanged, so the only learning a specialization phase
can contain is the top member's.

**Model B** (`RCAS.ModeDynamics`) represents the specification's independent learning
`k i (t+1) = k i t + δ i t` (`δ ≥ 0`) for *every* member in specialization phases. Diffusion
phases pull everyone toward the current ceiling (whoever holds it).

## Main results

* Model A: `RCAS.KnowledgeSharing.schedule_specialization_eq` (OM1),
  `RCAS.schedule_monotone` (OM2), `RCAS.KnowledgeSharing.schedule_volume_lt_succ` (OM2, strict at
  diffusion steps), `RCAS.KnowledgeSharing.schedule_specialization_ceiling_lt_iff` (OM3 within
  Model A)
* Step lemmas: `RCAS.ceiling_catchUp` (diffusion keeps the ceiling),
  `RCAS.ceiling_lt_ceiling_add_iff` (learning raises the ceiling iff someone passes it)
* Model B: `RCAS.ModeDynamics.volume_monotone`, `card_carriers_monotone`, `frontier_monotone`
  (OM2), `RCAS.ModeDynamics.ceiling_diffusion` (diffusion keeps the ceiling),
  `RCAS.ModeDynamics.ceiling_lt_iff_of_specialization` (OM3),
  `RCAS.ModeDynamics.specialization_of_ceiling_lt` (the ceiling rises only in specialization),
  `RCAS.ModeDynamics.eq_of_specialization_of_no_learning` (OM1)
* `RCAS.Example.specialization_raises_ceiling`
-/

noncomputable section

namespace RCAS

open Filter Topology

/-- Operating modes. -/
inductive OperatingMode where
  /-- Knowledge diffusion phase (`η > 0`). -/
  | diffusion
  /-- Specialization phase (`η = 0`; each member deepens their own expertise). -/
  | specialization
  deriving DecidableEq

/-- The transfer rate chosen by the team over time. -/
def modeSchedule (mode : ℕ → OperatingMode) (η_base : ℝ) : ℕ → ℝ :=
  fun t => match mode t with
  | .diffusion => η_base
  | .specialization => 0

section Schedule

variable {mode : ℕ → OperatingMode} {ηb : ℝ} {t : ℕ}

theorem modeSchedule_of_diffusion (h : mode t = .diffusion) : modeSchedule mode ηb t = ηb := by
  simp [modeSchedule, h]

theorem modeSchedule_of_specialization (h : mode t = .specialization) :
    modeSchedule mode ηb t = 0 := by
  simp [modeSchedule, h]

theorem modeSchedule_nonneg (h0 : 0 ≤ ηb) (t : ℕ) : 0 ≤ modeSchedule mode ηb t := by
  cases hm : mode t
  · rw [modeSchedule_of_diffusion hm]; exact h0
  · rw [modeSchedule_of_specialization hm]

theorem modeSchedule_le_one (h1 : ηb ≤ 1) (t : ℕ) : modeSchedule mode ηb t ≤ 1 := by
  cases hm : mode t
  · rw [modeSchedule_of_diffusion hm]; exact h1
  · rw [modeSchedule_of_specialization hm]; exact zero_le_one

end Schedule

/-! ### Model A: the schedule fed into `KnowledgeSharing` -/

section ModelA

variable {ι : Type*} {k : ℕ → ι → ℝ} {h : ι} {mode : ℕ → OperatingMode} {ηb : ℝ}

/-- Catch-up at the scheduled rate, with `0 ≤ η_base ≤ 1`, is knowledge sharing. -/
theorem knowledgeSharing_of_schedule
    (hk : ∀ t i, i ≠ h → k (t + 1) i = k t i + modeSchedule mode ηb t * (k t h - k t i))
    (h0 : 0 ≤ ηb) (h1 : ηb ≤ 1) (htop : ∀ t, k t h ≤ k (t + 1) h) (hinit : ∀ i, k 0 i ≤ k 0 h) :
    KnowledgeSharing k h (fun t _ => modeSchedule mode ηb t) :=
  ⟨hk, fun t _ => modeSchedule_nonneg h0 t, fun t _ => modeSchedule_le_one h1 t, htop, hinit⟩

namespace KnowledgeSharing

variable (hS : KnowledgeSharing k h (fun t _ => modeSchedule mode ηb t))
include hS

/-- In a specialization step, every member other than the top member is unchanged. -/
theorem schedule_specialization_other {t : ℕ} (ht : mode t = .specialization) {i : ι}
    (hi : i ≠ h) : k (t + 1) i = k t i := by
  rw [hS.catchUp t i hi, modeSchedule_of_specialization ht, zero_mul, add_zero]

/-- **OM1** (Model A): in a specialization step in which the top member does not change either,
nobody changes. -/
theorem schedule_specialization_eq {t : ℕ} (ht : mode t = .specialization)
    (htop : k (t + 1) h = k t h) : k (t + 1) = k t := by
  funext i
  by_cases hi : i = h
  · rw [hi]; exact htop
  · exact hS.schedule_specialization_other ht hi

/-- **OM1** (Model A): hence volume and the set of members who can carry the domain are
preserved in such a step. -/
theorem schedule_specialization_preserves [Fintype ι] {t : ℕ} (ht : mode t = .specialization)
    (htop : k (t + 1) h = k t h) (φ : ℝ → ℝ) (θ : ℝ) (e : ι → ℝ) :
    volume φ (k (t + 1)) e = volume φ (k t) e ∧ carriers θ (k (t + 1)) e = carriers θ (k t) e := by
  rw [hS.schedule_specialization_eq ht htop]
  exact ⟨rfl, rfl⟩

/-- **OM2** (strict growth at diffusion steps): at a diffusion step with `η_base > 0`, if an
engaged member is behind the top member and `φ` is strictly monotone, volume strictly increases.
-/
theorem schedule_volume_lt_succ [Fintype ι] {φ : ℝ → ℝ} (hφ : StrictMono φ) {e : ι → ℝ}
    (he0 : ∀ i, 0 ≤ e i) {t : ℕ} (ht : mode t = .diffusion) (hηb : 0 < ηb) {i : ι} (hi : i ≠ h)
    (hgap : k t i < k t h) (hei : 0 < e i) : volume φ (k t) e < volume φ (k (t + 1)) e :=
  hS.volume_lt_succ hφ he0 hi (by rw [modeSchedule_of_diffusion ht]; exact hηb) hgap hei

/-- **OM3** (Model A): in a specialization step the ceiling rises exactly when the top member
learns; the other members cannot raise it, since they do not change. -/
theorem schedule_specialization_ceiling_lt_iff [Fintype ι] [Nonempty ι] (t : ℕ) :
    ceiling (k t) < ceiling (k (t + 1)) ↔ k t h < k (t + 1) h :=
  hS.ceiling_lt_iff t

end KnowledgeSharing

/-- **OM2** (Model A): whatever the schedule of diffusion and specialization phases, volume and
the number of members who can carry the domain are non-decreasing. -/
theorem schedule_monotone [Fintype ι]
    (hk : ∀ t i, i ≠ h → k (t + 1) i = k t i + modeSchedule mode ηb t * (k t h - k t i))
    (h0 : 0 ≤ ηb) (h1 : ηb ≤ 1) (htop : ∀ t, k t h ≤ k (t + 1) h) (hinit : ∀ i, k 0 i ≤ k 0 h)
    {φ : ℝ → ℝ} (hφ : Monotone φ) {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) (θ : ℝ) :
    Monotone (fun t => volume φ (k t) e) ∧ Monotone (fun t => (carriers θ (k t) e).card) :=
  let hS := knowledgeSharing_of_schedule hk h0 h1 htop hinit
  ⟨hS.volume_monotone hφ he0, hS.card_carriers_monotone he0⟩

end ModelA

/-! ### Step lemmas for the ceiling -/

section Steps

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A catch-up step toward the current ceiling at a rate at most `1` keeps the ceiling (the
member at the ceiling stays there; nobody overshoots). -/
theorem ceiling_catchUp (k : ι → ℝ) {η : ℝ} (h1 : η ≤ 1) :
    ceiling (fun i => k i + η * (ceiling k - k i)) = ceiling k := by
  refine le_antisymm (Finset.sup'_le _ _ fun i _ => ?_) ?_
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (le_ceiling k i))]
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty k
    calc ceiling k = k i + η * (ceiling k - k i) := by
          rw [show ceiling k = k i from hi]; ring
      _ ≤ ceiling (fun i => k i + η * (ceiling k - k i)) :=
          le_ceiling (fun i => k i + η * (ceiling k - k i)) i

/-- Learning `δ` raises the ceiling exactly when someone passes the current ceiling. -/
theorem ceiling_lt_ceiling_add_iff (k δ : ι → ℝ) :
    ceiling k < ceiling (fun i => k i + δ i) ↔ ∃ i, ceiling k < k i + δ i := by
  unfold ceiling
  rw [Finset.lt_sup'_iff]
  simp

end Steps

/-! ### Model B: independent learning in specialization phases -/

/-- Mode dynamics: in a diffusion step everyone catches up toward the current ceiling at rate
`η_base`; in a specialization step each member learns independently, `δ ≥ 0`. -/
structure ModeDynamics {ι : Type*} [Fintype ι] [Nonempty ι] (k : ℕ → ι → ℝ)
    (mode : ℕ → OperatingMode) (ηb : ℝ) (δ : ℕ → ι → ℝ) : Prop where
  /-- Diffusion: catch-up toward the current ceiling. -/
  diffuse : ∀ t, mode t = .diffusion → ∀ i, k (t + 1) i = k t i + ηb * (ceiling (k t) - k t i)
  /-- Specialization: independent learning. -/
  specialize : ∀ t, mode t = .specialization → ∀ i, k (t + 1) i = k t i + δ t i
  /-- The transfer rate is nonnegative. -/
  rate_nonneg : 0 ≤ ηb
  /-- The transfer rate is at most `1`. -/
  rate_le_one : ηb ≤ 1
  /-- Independent learning does not lower capability. -/
  learn_nonneg : ∀ t i, 0 ≤ δ t i

namespace ModeDynamics

variable {ι : Type*} [Fintype ι] [Nonempty ι] {k : ℕ → ι → ℝ} {mode : ℕ → OperatingMode}
  {ηb : ℝ} {δ : ℕ → ι → ℝ} (hM : ModeDynamics k mode ηb δ)
include hM

/-- Nobody's capability decreases, in either mode. -/
theorem le_succ (t : ℕ) (i : ι) : k t i ≤ k (t + 1) i := by
  cases hm : mode t
  · rw [hM.diffuse t hm i]
    exact le_add_of_nonneg_right (mul_nonneg hM.rate_nonneg (sub_nonneg.mpr (le_ceiling _ i)))
  · rw [hM.specialize t hm i]
    exact le_add_of_nonneg_right (hM.learn_nonneg t i)

theorem monotone_member (i : ι) : Monotone fun t => k t i :=
  monotone_nat_of_le_succ fun t => hM.le_succ t i

/-- **OM2** (Model B): volume is non-decreasing across any alternation of phases. -/
theorem volume_monotone {φ : ℝ → ℝ} (hφ : Monotone φ) {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) :
    Monotone fun t => volume φ (k t) e :=
  monotone_nat_of_le_succ fun t =>
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hφ (hM.le_succ t i)) (he0 i)

/-- **OM2** (Model B): the number of members who can carry the domain is non-decreasing. -/
theorem card_carriers_monotone {θ : ℝ} {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) :
    Monotone fun t => (carriers θ (k t) e).card := fun _ _ htt' =>
  Finset.card_le_card fun i hi => mem_carriers.mpr ((mem_carriers.mp hi).trans
    (mul_le_mul_of_nonneg_right (hM.monotone_member i htt') (he0 i)))

/-- **OM2** (Model B): the frontier is non-decreasing. -/
theorem frontier_monotone {e : ι → ℝ} (he0 : ∀ i, 0 ≤ e i) :
    Monotone fun t => frontier (k t) e :=
  monotone_nat_of_le_succ fun t => Finset.sup'_le _ _ fun i _ =>
    (mul_le_mul_of_nonneg_right (hM.le_succ t i) (he0 i)).trans (mul_le_frontier _ e i)

/-- A diffusion step keeps the ceiling. -/
theorem ceiling_diffusion {t : ℕ} (hm : mode t = .diffusion) :
    ceiling (k (t + 1)) = ceiling (k t) := by
  rw [show k (t + 1) = fun i => k t i + ηb * (ceiling (k t) - k t i) from
    funext (hM.diffuse t hm)]
  exact ceiling_catchUp _ hM.rate_le_one

/-- **OM3** (Model B): in a specialization step the ceiling rises exactly when some member's
independent learning takes them past the current ceiling. -/
theorem ceiling_lt_iff_of_specialization {t : ℕ} (hm : mode t = .specialization) :
    ceiling (k t) < ceiling (k (t + 1)) ↔ ∃ i, ceiling (k t) < k t i + δ t i := by
  rw [show k (t + 1) = fun i => k t i + δ t i from funext (hM.specialize t hm)]
  exact ceiling_lt_ceiling_add_iff _ _

/-- The ceiling rises only in specialization steps: specialization is the mechanism of frontier
expansion in this model. -/
theorem specialization_of_ceiling_lt {t : ℕ} (h : ceiling (k t) < ceiling (k (t + 1))) :
    mode t = .specialization := by
  cases hm : mode t
  · rw [hM.ceiling_diffusion hm] at h
    exact absurd h (lt_irrefl _)
  · rfl

/-- **OM1** (Model B): a specialization step without learning changes nothing. -/
theorem eq_of_specialization_of_no_learning {t : ℕ} (hm : mode t = .specialization)
    (hδ : ∀ i, δ t i = 0) : k (t + 1) = k t :=
  funext fun i => by rw [hM.specialize t hm i, hδ i, add_zero]

end ModeDynamics

namespace Example

/-- **OM3** in a two-member example: the expert is at `1`, the other at `1/2`. A specialization
step in which only the other member learns (`δ = (0, 1)`) raises the ceiling from `1` to `3/2`;
a following diffusion step at rate `1/2` keeps it at `3/2`. -/
theorem specialization_raises_ceiling :
    ceiling (![1, 1 / 2] : Fin 2 → ℝ) <
      ceiling (fun i => (![1, 1 / 2] : Fin 2 → ℝ) i + ![0, 1] i) ∧
    ceiling (fun i => (![1, 3 / 2] : Fin 2 → ℝ) i +
        1 / 2 * (ceiling (![1, 3 / 2] : Fin 2 → ℝ) - (![1, 3 / 2] : Fin 2 → ℝ) i)) =
      ceiling (![1, 3 / 2] : Fin 2 → ℝ) := by
  refine ⟨(ceiling_lt_ceiling_add_iff _ _).mpr ⟨1, ?_⟩,
    ceiling_catchUp _ (by norm_num)⟩
  have : ceiling (![1, 1 / 2] : Fin 2 → ℝ) = 1 :=
    ceiling_eq_of_top (h := 0) fun i => by fin_cases i <;> norm_num
  rw [this]
  norm_num

end Example

end RCAS
