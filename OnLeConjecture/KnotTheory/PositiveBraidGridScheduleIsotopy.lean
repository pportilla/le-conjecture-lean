/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridEventSchedule
public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordIsotopy

/-! # Ambient transport between two literal generator schedules

The endpoints of every generator interval move by the same smooth convex
parameter. Positivity and order hold throughout. The resulting finite-sum height
family is smooth, has no collisions, and retains uniform endpoint collars.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

local instance scheduleRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance scheduleRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- Smooth motion of an individual interval endpoint. -/
def positiveScheduleBlend (a b s : ℝ) : ℝ :=
  (1 - Real.smoothTransition s) * a + Real.smoothTransition s * b

@[simp] theorem positiveScheduleBlend_zero (a b : ℝ) : positiveScheduleBlend a b 0 = a := by
  simp [positiveScheduleBlend]

@[simp] theorem positiveScheduleBlend_one (a b : ℝ) : positiveScheduleBlend a b 1 = b := by
  simp [positiveScheduleBlend]

@[simp] theorem positiveScheduleBlend_self (a s : ℝ) : positiveScheduleBlend a a s = a := by
  unfold positiveScheduleBlend
  ring

theorem positiveScheduleBlend_contDiff (a b : ℝ) : ContDiff ℝ ∞ (positiveScheduleBlend a b) :=
  ((contDiff_const.sub Real.smoothTransition.contDiff).mul contDiff_const).add
    (Real.smoothTransition.contDiff.mul contDiff_const)

theorem positiveScheduleBlend_le {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (s : ℝ) :
    positiveScheduleBlend a c s ≤ positiveScheduleBlend b d s := by
  exact add_le_add
    (mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr (Real.smoothTransition.le_one s)))
    (mul_le_mul_of_nonneg_left hcd (Real.smoothTransition.nonneg s))

theorem positiveScheduleBlend_lt {a b c d : ℝ} (hab : a < b) (hcd : c < d) (s : ℝ) :
    positiveScheduleBlend a c s < positiveScheduleBlend b d s := by
  by_cases hs : Real.smoothTransition s = 0
  · simpa only [positiveScheduleBlend, hs, sub_zero, one_mul, zero_mul, add_zero] using hab
  · exact add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left hab.le (sub_nonneg.mpr (Real.smoothTransition.le_one s)))
      (mul_lt_mul_of_pos_left hcd (lt_of_le_of_ne (Real.smoothTransition.nonneg s) (Ne.symm hs)))

/-- The same word, with its literal generator intervals smoothly moved. -/
def positiveGridScheduleFamily {m : ℕ} (w : PositiveAdjacentWord m)
    (L₀ R₀ L₁ R₁ : Fin w.length → ℝ) (k : Fin m) (p : ℝ × ℝ) : ℂ :=
  positiveGridScheduledWord w
    (fun j => positiveScheduleBlend (L₀ j) (L₁ j) p.1)
    (fun j => positiveScheduleBlend (R₀ j) (R₁ j) p.1) k p.2

theorem positiveGridScheduleFamily_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    (L₀ R₀ L₁ R₁ : Fin w.length → ℝ)
    (h₀ : ∀ j, L₀ j < R₀ j) (h₁ : ∀ j, L₁ j < R₁ j) (k : Fin m) :
    ContDiff ℝ ∞ (positiveGridScheduleFamily w L₀ R₀ L₁ R₁ k) :=
  positiveGridScheduledWord_contDiff w _ _
    (fun _ => positiveScheduleBlend_contDiff _ _) (fun _ => positiveScheduleBlend_contDiff _ _)
    (fun j s => positiveScheduleBlend_lt (h₀ j) (h₁ j) s) k

/-- Uniform collars follow from the common outer bounds of both schedules. -/
theorem positiveGridScheduleFamily_left_collar {m : ℕ} (w : PositiveAdjacentWord m)
    (L₀ R₀ L₁ R₁ : Fin w.length → ℝ)
    (h₀ : ∀ j, L₀ j < R₀ j) (h₁ : ∀ j, L₁ j < R₁ j) (b : ℝ)
    (hb₀ : ∀ j, b < L₀ j) (hb₁ : ∀ j, b < L₁ j) (k : Fin m) :
    ∀ᶠ θ in 𝓝 b, ∀ s, positiveGridScheduleFamily w L₀ R₀ L₁ R₁ k (s, θ) = k.val := by
  have hh : ∀ᶠ θ in 𝓝 b, ∀ j, θ < L₀ j ∧ θ < L₁ j :=
    Filter.eventually_all.mpr fun j => (eventually_lt_nhds (hb₀ j)).and
      (eventually_lt_nhds (hb₁ j))
  filter_upwards [hh] with θ hθ
  intro s
  apply positiveGridScheduledWord_initial w _ _
    (fun j => positiveScheduleBlend_lt (h₀ j) (h₁ j) s) k
  intro j
  simpa only [positiveScheduleBlend_self] using
    (positiveScheduleBlend_lt (hθ j).1 (hθ j).2 s).le

theorem positiveGridScheduleFamily_right_collar {m : ℕ} (w : PositiveAdjacentWord m)
    (L₀ R₀ L₁ R₁ : Fin w.length → ℝ)
    (h₀ : ∀ j, L₀ j < R₀ j) (h₁ : ∀ j, L₁ j < R₁ j) (d : ℝ)
    (hd₀ : ∀ j, R₀ j < d) (hd₁ : ∀ j, R₁ j < d) (k : Fin m) :
    ∀ᶠ θ in 𝓝 d, ∀ s, positiveGridScheduleFamily w L₀ R₀ L₁ R₁ k (s, θ) =
      (w.permutation.symm k).val := by
  have hh : ∀ᶠ θ in 𝓝 d, ∀ j, R₀ j < θ ∧ R₁ j < θ :=
    Filter.eventually_all.mpr fun j => (eventually_gt_nhds (hd₀ j)).and
      (eventually_gt_nhds (hd₁ j))
  filter_upwards [hh] with θ hθ
  intro s
  apply positiveGridScheduledWord_final w _ _
    (fun j => positiveScheduleBlend_lt (h₀ j) (h₁ j) s) k
  intro j
  simpa only [positiveScheduleBlend_self] using
    (positiveScheduleBlend_lt (hθ j).1 (hθ j).2 s).le

/-- Literal ordered schedules have ambient-isotopic sphere closures. All native
smoothness, injection, immersion and seam conditions are constructed here. -/
theorem exists_positiveGridSchedule_diffeotopy {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    (i : Fin 2) (b : ℝ) (L₀ R₀ L₁ R₁ : Fin w.length → ℝ)
    (h₀ : ∀ j, L₀ j < R₀ j) (h₁ : ∀ j, L₁ j < R₁ j)
    (ho₀ : ∀ j q, j < q → R₀ j ≤ L₀ q) (ho₁ : ∀ j q, j < q → R₁ j ≤ L₁ q)
    (hb₀ : ∀ j, b < L₀ j) (hb₁ : ∀ j, b < L₁ j)
    (hd₀ : ∀ j, R₀ j < b + 2 * Real.pi) (hd₁ : ∀ j, R₁ j < b + 2 * Real.pi) :
    ∃ W : Circle × ℝ → ℂ, ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ W ∧
      (∀ k θ s, θ ∈ Icc b (b + 2 * Real.pi) → W (braidCircleSheet m k θ, s) =
        positiveGridScheduleFamily w L₀ R₀ L₁ R₁ (before.symm k) (s, θ)) ∧
      ∃ (A B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
        (∀ v, (A v : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (v ^ m, W (v, 0))) ∧
        (∀ v, (B v : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (v ^ m, W (v, 1))) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ v, Φ.final (A v) = B v := by
  obtain ⟨W, hW, hsheet⟩ := exists_circle_height_family_of_period_collars hm
    (fun k => positiveGridScheduleFamily w L₀ R₀ L₁ R₁ (before.symm k)) b
    (fun k => ((before.symm k).val : ℂ))
    (fun k => ((w.permutation.symm (before.symm k)).val : ℂ))
    (fun k => positiveGridScheduleFamily_contDiff w L₀ R₀ L₁ R₁ h₀ h₁ _)
    (fun k => positiveGridScheduleFamily_left_collar w L₀ R₀ L₁ R₁ h₀ h₁ b hb₀ hb₁ _)
    (fun k => positiveGridScheduleFamily_right_collar w L₀ R₀ L₁ R₁ h₀ h₁ _ hd₀ hd₁ _)
    (fun k => congrArg (fun v : Fin m => (v.val : ℂ))
      (positiveWord_inverse_sorting_rotation w before after hw hc k).symm)
  change ∀ k θ s, θ ∈ Icc b (b + 2 * Real.pi) → W (braidCircleSheet m k θ, s) =
    positiveGridScheduleFamily w L₀ R₀ L₁ R₁ (before.symm k) (s, θ) at hsheet
  let K : Circle × ℝ → EuclideanSpace ℂ (Fin 2) := fun p =>
    planeSolidTorusMap i (p.1 ^ m, W p)
  have hK : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ K :=
    (planeSolidTorusMap_isSmoothEmbedding i).contMDiff.comp
      ((contMDiff_fst.pow m).prodMk hW)
  have hphase (p : Circle × ℝ) : ‖K p i‖⁻¹ • K p i = (p.1 : ℂ) ^ m := by
    simpa only [K, Circle.coe_pow] using congrArg Prod.fst
      (planeSolidTorusMap_recovery i (p.1 ^ m, W p))
  have hinj (s : ℝ) : Function.Injective (fun v : Circle => K (v, s)) := by
    intro v q heq
    by_contra hne
    have hh := (planeSolidTorusMap_isSmoothEmbedding i).isEmbedding.injective heq
    have hpow : v ^ m = q ^ m := congrArg Prod.fst hh
    have hheight : W (v, s) = W (q, s) := congrArg Prod.snd hh
    obtain ⟨θ, hθ, k, l, hkl, rfl, rfl⟩ := exists_common_braidCircleSheet_labels hm b hne hpow
    rw [hsheet k θ s hθ, hsheet l θ s hθ] at hheight
    have hlabels := positiveGridScheduledWord_injective w _ _
      (fun j => positiveScheduleBlend_lt (h₀ j) (h₁ j) s)
      (fun j q hjq => positiveScheduleBlend_le (ho₀ j q hjq) (ho₁ j q hjq) s) θ hheight
    exact hkl (before.symm.injective hlabels)
  have hEmb (s : ℝ) : Topology.IsEmbedding (fun v : Circle => K (v, s)) :=
    ((hK.comp (contMDiff_id.prodMk contMDiff_const)).continuous.isClosedEmbedding
      (hinj s)).isEmbedding
  obtain ⟨A, B, hA, hB, Φ, hΦ⟩ := exists_plane_sphere_family_endpoint_diffeotopy K
    (fun _ _ => planeSolidTorusMap_norm i _) hK
    (planeSphereFamily_mfderiv_injective_of_power_phase K i hm hK hphase) hEmb
  exact ⟨W, hW, hsheet, A, B, hA, hB, Φ, hΦ⟩

end OnLeConjecture.KnotTheory
