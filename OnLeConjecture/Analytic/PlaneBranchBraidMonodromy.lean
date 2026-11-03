/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidChambers
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Cyclic relabelling of analytic branch sheets

Increasing the base angle by `2 * pi` sends the source sheet labelled `k`
to the sheet labelled `finRotate a k`. This is an equality of the actual
parametrizations. It implies periodicity of projected coincidence events.
Finiteness on one period supplies a base angle for which both endpoints
of the resulting period avoid all projected coincidences.
-/

@[expose] public noncomputable section

open Set Metric

namespace OnLeConjecture.Analytic

theorem planeBranchBraidRoot_finRotate {a : ℕ} (ha : 0 < a) (k : Fin a) :
    planeBranchBraidRoot a (finRotate a k) =
      Complex.exp (2 * Real.pi * Complex.I / (a : ℂ)) * planeBranchBraidRoot a k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  by_cases hk : k = Fin.last n
  · subst k
    simp only [finRotate_last, planeBranchBraidRoot, Fin.val_zero, Fin.val_last, pow_zero]
    rw [mul_comm, ← pow_succ, (Complex.isPrimitiveRoot_exp (n + 1) (by omega)).pow_eq_one]
  · unfold planeBranchBraidRoot
    rw [coe_finRotate_of_ne_last hk, pow_succ, mul_comm]

theorem planeBranchAngularParameter_add_two_pi (a : ℕ) (r θ : ℝ) :
    planeBranchAngularParameter a r (θ + 2 * Real.pi) =
      Complex.exp (2 * Real.pi * Complex.I / (a : ℂ)) *
        planeBranchAngularParameter a r θ := by
  unfold planeBranchAngularParameter
  rw [mul_left_comm _ (r : ℂ), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- One positive base turn advances the source label by one cyclic step. -/
theorem planeBranchBraidParameter_add_two_pi {a : ℕ} (ha : 0 < a)
    (r θ : ℝ) (k : Fin a) :
    planeBranchBraidParameter a r k (θ + 2 * Real.pi) =
      planeBranchBraidParameter a r (finRotate a k) θ := by
  rw [planeBranchBraidParameter_eq_root_mul, planeBranchAngularParameter_add_two_pi,
    planeBranchBraidParameter_eq_root_mul, planeBranchBraidRoot_finRotate ha]
  ring

theorem planeBranchBraidSheet_add_two_pi (F : ℂ → Source 2) (i : Fin 2)
    {a : ℕ} (ha : 0 < a) (r θ : ℝ) (k : Fin a) :
    planeBranchBraidSheet F i a r k (θ + 2 * Real.pi) =
      planeBranchBraidSheet F i a r (finRotate a k) θ := by
  unfold planeBranchBraidSheet
  rw [planeBranchBraidParameter_add_two_pi ha]

theorem planeBranchBraidProjection_add_two_pi (F : ℂ → Source 2) (i : Fin 2)
    {a : ℕ} (ha : 0 < a) (r : ℝ) (c : ℂ) (θ : ℝ) (k : Fin a) :
    planeBranchBraidProjection F i a r c (θ + 2 * Real.pi) k =
      planeBranchBraidProjection F i a r c θ (finRotate a k) := by
  unfold planeBranchBraidProjection
  rw [planeBranchBraidSheet_add_two_pi F i ha]

/-- Every label belongs to the same orbit, including the one-strand case. -/
theorem planeBranchBraidLabel_sameCycle {a : ℕ} (ha : 0 < a) (k l : Fin a) :
    (finRotate a).SameCycle k l := by
  by_cases ha2 : 2 ≤ a
  · apply (isCycle_finRotate_of_le ha2).sameCycle
    · apply Equiv.Perm.mem_support.mp
      rw [support_finRotate_of_le ha2]
      exact Finset.mem_univ _
    · apply Equiv.Perm.mem_support.mp
      rw [support_finRotate_of_le ha2]
      exact Finset.mem_univ _
  · have he : a = 1 := by omega
    subst a
    exact (Subsingleton.elim k l).sameCycle _

/-- A projected coincidence, without restricting the angle to an interval. -/
def planeBranchProjectedCoincidence (F : ℂ → Source 2) (i : Fin 2) (a : ℕ)
    (r : ℝ) (c : ℂ) (θ : ℝ) : Prop :=
  ∃ k l : Fin a, k ≠ l ∧
    planeBranchBraidProjection F i a r c θ k = planeBranchBraidProjection F i a r c θ l

theorem mem_planeBranchProjectedCrossingTimes_iff_coincidence
    (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) (c : ℂ) (u v θ : ℝ) :
    θ ∈ planeBranchProjectedCrossingTimes F i a r c u v ↔
      θ ∈ Icc u v ∧ planeBranchProjectedCoincidence F i a r c θ :=
  mem_planeBranchProjectedCrossingTimes_iff F i a r c u v θ

theorem planeBranchProjectedCoincidence_add_two_pi_iff
    (F : ℂ → Source 2) (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (r : ℝ) (c : ℂ) (θ : ℝ) :
    planeBranchProjectedCoincidence F i a r c (θ + 2 * Real.pi) ↔
      planeBranchProjectedCoincidence F i a r c θ := by
  constructor
  · rintro ⟨k, l, hkl, heq⟩
    refine ⟨finRotate a k, finRotate a l, fun h => hkl ((finRotate a).injective h), ?_⟩
    simpa only [planeBranchBraidProjection_add_two_pi F i ha] using heq
  · rintro ⟨k, l, hkl, heq⟩
    refine ⟨(finRotate a).symm k, (finRotate a).symm l,
      fun h => hkl ((finRotate a).symm.injective h), ?_⟩
    simpa only [planeBranchBraidProjection_add_two_pi F i ha, Equiv.apply_symm_apply] using heq

theorem planeBranchProjectedCoincidence_periodic
    (F : ℂ → Source 2) (i : Fin 2) {a : ℕ} (ha : 0 < a) (r : ℝ) (c : ℂ) :
    Function.Periodic (planeBranchProjectedCoincidence F i a r c) (2 * Real.pi) :=
  fun θ => propext (planeBranchProjectedCoincidence_add_two_pi_iff F i ha r c θ)

/-- The finite event sets on translated periods agree by translation. -/
theorem mem_planeBranchProjectedCrossingTimes_add_two_pi_iff
    (F : ℂ → Source 2) (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (r : ℝ) (c : ℂ) (u v θ : ℝ) :
    θ + 2 * Real.pi ∈ planeBranchProjectedCrossingTimes F i a r c
      (u + 2 * Real.pi) (v + 2 * Real.pi) ↔
      θ ∈ planeBranchProjectedCrossingTimes F i a r c u v := by
  rw [mem_planeBranchProjectedCrossingTimes_iff_coincidence,
    mem_planeBranchProjectedCrossingTimes_iff_coincidence,
    planeBranchProjectedCoincidence_add_two_pi_iff F i ha]
  simp only [mem_Icc, add_le_add_iff_right]

theorem planeBranchBraidProjection_injective_iff_no_coincidence
    (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) (c : ℂ) (θ : ℝ) :
    Function.Injective (planeBranchBraidProjection F i a r c θ) ↔
      ¬ planeBranchProjectedCoincidence F i a r c θ := by
  constructor
  · rintro hinj ⟨k, l, hkl, heq⟩
    exact hkl (hinj heq)
  · intro h k l heq
    by_contra hkl
    exact h ⟨k, l, hkl, heq⟩

/-- Endpoint sorting agrees with the proved cyclic relabelling of sheets. -/
theorem planeBranchBraid_endpoint_sortingPerm
    (F : ℂ → Source 2) (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (r : ℝ) (c : ℂ) (θ : ℝ)
    (hinj : Function.Injective (planeBranchBraidProjection F i a r c θ))
    {σ₀ σ₁ : Equiv.Perm (Fin a)}
    (h₀ : StrictMono (fun j => planeBranchBraidProjection F i a r c θ (σ₀ j)))
    (h₁ : StrictMono (fun j =>
      planeBranchBraidProjection F i a r c (θ + 2 * Real.pi) (σ₁ j))) :
    σ₁.trans (finRotate a) = σ₀ := by
  apply sortingPerm_unique hinj _ h₀
  intro j k hjk
  simpa only [planeBranchBraidProjection_add_two_pi F i ha, Equiv.trans_apply] using h₁ hjk

/-- Finiteness of the actual projected coincidences on two standard
periods suffices to choose a full period with two regular endpoints. -/
theorem exists_planeBranch_regular_period_of_finite
    (F : ℂ → Source 2) (i : Fin 2) {a : ℕ} (ha : 0 < a) (r : ℝ) (c : ℂ)
    (hfin : (planeBranchProjectedCrossingTimes F i a r c 0 (4 * Real.pi)).Finite) :
    ∃ θ ∈ Ioo (0 : ℝ) (2 * Real.pi), ∃ E : Finset ℝ,
      (∀ t, t ∈ E ↔ t ∈ planeBranchProjectedCrossingTimes F i a r c
        θ (θ + 2 * Real.pi)) ∧
      θ ∉ E ∧ θ + 2 * Real.pi ∉ E ∧
      Function.Injective (planeBranchBraidProjection F i a r c θ) ∧
      Function.Injective (planeBranchBraidProjection F i a r c (θ + 2 * Real.pi)) := by
  obtain ⟨θ, hθ, hθnot⟩ := ((Ioo_infinite Real.two_pi_pos).sdiff hfin).nonempty
  have hreg : ¬ planeBranchProjectedCoincidence F i a r c θ := by
    intro h
    exact hθnot ((mem_planeBranchProjectedCrossingTimes_iff_coincidence
      F i a r c 0 (4 * Real.pi) θ).mpr ⟨⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩, h⟩)
  have hreg' : ¬ planeBranchProjectedCoincidence F i a r c (θ + 2 * Real.pi) :=
    fun h => hreg ((planeBranchProjectedCoincidence_add_two_pi_iff F i ha r c θ).mp h)
  have hfin' : (planeBranchProjectedCrossingTimes F i a r c θ (θ + 2 * Real.pi)).Finite := by
    apply hfin.subset
    intro t ht
    obtain ⟨ht, hco⟩ := (mem_planeBranchProjectedCrossingTimes_iff_coincidence
      F i a r c θ (θ + 2 * Real.pi) t).mp ht
    exact (mem_planeBranchProjectedCrossingTimes_iff_coincidence
      F i a r c 0 (4 * Real.pi) t).mpr
      ⟨⟨by linarith [hθ.1, ht.1], by linarith [hθ.2, ht.2]⟩, hco⟩
  refine ⟨θ, hθ, hfin'.toFinset, fun _ => hfin'.mem_toFinset, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hreg ((mem_planeBranchProjectedCrossingTimes_iff_coincidence
      F i a r c θ (θ + 2 * Real.pi) θ).mp (hfin'.mem_toFinset.mp h)).2
  · intro h
    exact hreg' ((mem_planeBranchProjectedCrossingTimes_iff_coincidence
      F i a r c θ (θ + 2 * Real.pi) (θ + 2 * Real.pi)).mp
      (hfin'.mem_toFinset.mp h)).2
  · exact (planeBranchBraidProjection_injective_iff_no_coincidence F i a r c θ).mpr hreg
  · exact (planeBranchBraidProjection_injective_iff_no_coincidence
      F i a r c (θ + 2 * Real.pi)).mpr hreg'

/-- The base point can be chosen so that both endpoints of one full period
are regular for the actual branch projection. The finite event set covers
that entire closed period. -/
theorem exists_radius_planeBranch_regular_period
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ r : ℝ, 0 < r → r < ρ → ∀ c : ℂ, c ≠ 0 →
        ∃ θ ∈ Ioo (0 : ℝ) (2 * Real.pi), ∃ E : Finset ℝ,
          (∀ t, t ∈ E ↔ t ∈ planeBranchProjectedCrossingTimes F i a r c
            θ (θ + 2 * Real.pi)) ∧
          θ ∉ E ∧ θ + 2 * Real.pi ∉ E ∧
          Function.Injective (planeBranchBraidProjection F i a r c θ) ∧
          Function.Injective (planeBranchBraidProjection F i a r c (θ + 2 * Real.pi)) := by
  obtain ⟨ρ, hρ, hρR, hfinite⟩ :=
    exists_radius_planeBranchProjectedCrossingTimes_finite ha hR hF hi hp
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro r hr hrρ c hc
  exact exists_planeBranch_regular_period_of_finite F i ha r c
    (hfinite r hr hrρ c hc 0 (4 * Real.pi)).1

end OnLeConjecture.Analytic
