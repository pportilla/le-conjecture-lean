/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordClosed
public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordCollars
public import OnLeConjecture.Analytic.PlaneBranchBraidPeriodFamilyGluing
public import OnLeConjecture.Analytic.PlaneBranchBraidCircleFibres

/-! # Native circle parametrization of the rounded word family

A labelling intertwining sheet rotation with the inverse word permutation closes
the same strand endpoints. The real horizontal correction and the complex height
are descended separately, retaining the exact cylinder formula.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic
attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.KnotTheory

/-- Rescale one circle period to the fixed word interval. -/
def positiveRoundedWordPeriodTime {m : ℕ} (w : PositiveAdjacentWord m) (θ : ℝ) : ℝ :=
  (2 * (w.length : ℝ) + 1) * θ / (2 * Real.pi)

@[simp] theorem positiveRoundedWordPeriodTime_zero {m : ℕ} (w : PositiveAdjacentWord m) :
    positiveRoundedWordPeriodTime w 0 = 0 := by simp [positiveRoundedWordPeriodTime]

@[simp] theorem positiveRoundedWordPeriodTime_end {m : ℕ} (w : PositiveAdjacentWord m) :
    positiveRoundedWordPeriodTime w (2 * Real.pi) = 2 * (w.length : ℝ) + 1 := by
  rw [positiveRoundedWordPeriodTime, mul_div_cancel_right₀ _ (ne_of_gt Real.two_pi_pos)]

theorem positiveRoundedWordPeriodTime_contDiff {m : ℕ} (w : PositiveAdjacentWord m) :
    ContDiff ℝ ∞ (positiveRoundedWordPeriodTime w) :=
  (contDiff_const.mul contDiff_id).div_const _

theorem positiveRoundedWordPeriodTime_mem {m : ℕ} (w : PositiveAdjacentWord m)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi)) :
    positiveRoundedWordPeriodTime w θ ∈ Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) := by
  constructor
  · exact div_nonneg (mul_nonneg (by positivity) hθ.1) Real.two_pi_pos.le
  · apply (div_le_iff₀ Real.two_pi_pos).mpr
    exact mul_le_mul_of_nonneg_left hθ.2 (by positivity)

/-- The complete rounded family descends jointly smoothly to a native circle.
Its formula is the same cylinder image as the already constructed closed quotient. -/
theorem exists_positiveRoundedWord_circle_family {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ k, σ (finRotate m k) = w.permutation.symm (σ k))
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j)) :
    ∃ F : Circle × ℝ → Circle × ℂ,
      ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ F ∧
      ∀ k θ s, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        F (braidCircleSheet m k θ, s) = positiveRectilinearCylinderPoint w
          (positiveRoundedWordDeformation w l u (σ k) s (positiveRoundedWordPeriodTime w θ)) := by
  let H := fun k (p : ℝ × ℝ) => positiveRoundedWordDeformation w l u (σ k) p.1
    (positiveRoundedWordPeriodTime w p.2)
  have hH (k) : ContDiff ℝ ∞ (H k) :=
    (positiveRoundedWordDeformation_contDiff w hls hus (σ k)).comp
      (contDiff_fst.prodMk ((positiveRoundedWordPeriodTime_contDiff w).comp contDiff_snd))
  have hleft : ∀ k, ∀ᶠ θ in 𝓝 (0 : ℝ), ∀ s,
      H k (s, θ) = (positiveRoundedWordPeriodTime w θ, ((σ k).val : ℂ)) := by
    intro k
    have ht : ∀ᶠ θ in 𝓝 (0 : ℝ), positiveRoundedWordPeriodTime w θ < 1 / 3 :=
      ((positiveRoundedWordPeriodTime_contDiff w).continuous.continuousAt).eventually
        (eventually_lt_nhds (by simp))
    filter_upwards [ht] with θ hθ
    intro s
    exact positiveRoundedWordDeformation_initial_open_collar w hl hu hU (σ k) s hθ.le
  have hright : ∀ k, ∀ᶠ θ in 𝓝 (2 * Real.pi), ∀ s,
      H k (s, θ) = (positiveRoundedWordPeriodTime w θ, ((σ (finRotate m k)).val : ℂ)) := by
    intro k
    have ht : ∀ᶠ θ in 𝓝 (2 * Real.pi),
        2 * (w.length : ℝ) + 2 / 3 < positiveRoundedWordPeriodTime w θ :=
      ((positiveRoundedWordPeriodTime_contDiff w).continuous.continuousAt).eventually
        (eventually_gt_nhds (by simp; linarith))
    filter_upwards [ht] with θ hθ
    intro s
    rw [hσ]
    exact positiveRoundedWordDeformation_final_open_collar w hl hu hU (σ k) s hθ.le
  let Z : Fin m → ℝ × ℝ → ℂ := fun k p => (H k p).2
  let X : Fin m → ℝ × ℝ → ℂ := fun k p => ((H k p).1 - positiveRoundedWordPeriodTime w p.2 : ℝ)
  obtain ⟨Wz, hWz, hez⟩ := exists_circle_height_family_of_period_collars hm Z 0
    (fun k => ((σ k).val : ℂ)) (fun k => ((σ (finRotate m k)).val : ℂ))
    (fun k => (hH k).snd)
    (fun k => (hleft k).mono fun θ hθ s => congrArg Prod.snd (hθ s))
    (fun k => by simpa only [zero_add] using
      ((hright k).mono fun θ hθ s => congrArg Prod.snd (hθ s)))
    (fun _ => rfl)
  obtain ⟨Wx, hWx, hex⟩ := exists_circle_height_family_of_period_collars hm X 0
    (fun _ => 0) (fun _ => 0)
    (fun k => Complex.ofRealCLM.contDiff.comp
      ((hH k).fst.sub ((positiveRoundedWordPeriodTime_contDiff w).comp contDiff_snd)))
    (fun k => (hleft k).mono fun θ hθ s => by simp only [X, hθ s, sub_self, Complex.ofReal_zero])
    (fun k => by
      simp only [zero_add]
      exact (hright k).mono fun θ hθ s => by simp only [X, hθ s, sub_self, Complex.ofReal_zero])
    (fun _ => rfl)
  let F : Circle × ℝ → Circle × ℂ := fun p =>
    (p.1 ^ m * Circle.exp (2 * Real.pi * (Wx p).re / (2 * (w.length : ℝ) + 1)), Wz p)
  have hF : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ F := by
    apply ContMDiff.prodMk _ hWz
    apply ContMDiff.mul (contMDiff_fst.pow m)
    apply contMDiff_circleExp.comp
    exact (contMDiff_const.mul (Complex.reCLM.contDiff.comp_contMDiff hWx)).div_const _
  refine ⟨F, hF, ?_⟩
  intro k θ s hθ
  have hz := hez k θ s (by simpa only [zero_add] using hθ)
  have hx := hex k θ s (by simpa only [zero_add] using hθ)
  change Wx (braidCircleSheet m k θ, s) = X k (s, θ) at hx
  change F (braidCircleSheet m k θ, s) = _
  apply Prod.ext
  · change braidCircleSheet m k θ ^ m * Circle.exp _ = Circle.exp _
    rw [braidCircleSheet_pow hm, hx]
    simp only [X, Complex.ofReal_re]
    rw [← Circle.exp_add]
    congr 1
    dsimp [H, positiveRoundedWordPeriodTime]
    field_simp
    ring
  · exact hz

/-- Every source-circle point has a representative in the half-open word period. -/
theorem exists_braidCircleSheet_half_open {m : ℕ} (hm : 0 < m) (v : Circle) :
    ∃ θ ∈ Ico (0 : ℝ) (2 * Real.pi), ∃ k : Fin m, braidCircleSheet m k θ = v := by
  obtain ⟨η, hη, hηv⟩ := exists_circle_angle_in_period 0 (v ^ m)
  let θ := toIcoMod Real.two_pi_pos 0 η
  have hθ : θ ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 η
  have he : Circle.exp θ = v ^ m := by
    apply Eq.trans _ hηv
    apply Circle.exp_eq_exp.mpr
    refine ⟨-toIcoDiv Real.two_pi_pos 0 η, ?_⟩
    simp only [θ, toIcoMod, zsmul_eq_mul, Int.cast_neg]
    ring
  obtain ⟨k, hk⟩ := exists_braidCircleSheet_eq hm θ he.symm
  exact ⟨θ, hθ, k, hk⟩

/-- The exact native circle family has no additional coincidences at the seam. -/
theorem positiveRoundedWord_circle_family_injective {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    {F : Circle × ℝ → Circle × ℂ}
    (he : ∀ k θ s, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      F (braidCircleSheet m k θ, s) = positiveRectilinearCylinderPoint w
        (positiveRoundedWordDeformation w l u (σ k) s (positiveRoundedWordPeriodTime w θ)))
    (s : ℝ) : Function.Injective (fun v : Circle => F (v, s)) := by
  intro v v' hv
  obtain ⟨θ, hθ, k, rfl⟩ := exists_braidCircleSheet_half_open hm v
  obtain ⟨η, hη, k', rfl⟩ := exists_braidCircleSheet_half_open hm v'
  have ht := positiveRoundedWordPeriodTime_mem w ⟨hθ.1, hθ.2.le⟩
  have ht' := positiveRoundedWordPeriodTime_mem w ⟨hη.1, hη.2.le⟩
  have htlt : positiveRoundedWordPeriodTime w θ < 2 * (w.length : ℝ) + 1 := by
    apply (div_lt_iff₀ Real.two_pi_pos).mpr
    exact mul_lt_mul_of_pos_left hθ.2 (by positivity)
  have htlt' : positiveRoundedWordPeriodTime w η < 2 * (w.length : ℝ) + 1 := by
    apply (div_lt_iff₀ Real.two_pi_pos).mpr
    exact mul_lt_mul_of_pos_left hη.2 (by positivity)
  change F (braidCircleSheet m k θ, s) = F (braidCircleSheet m k' η, s) at hv
  rw [he k θ s ⟨hθ.1, hθ.2.le⟩, he k' η s ⟨hη.1, hη.2.le⟩] at hv
  have hr := (positiveRoundedWordDeformation_cylinder_eq_iff w hU hl hu hla hua s
    (σ k, ⟨positiveRoundedWordPeriodTime w θ, ht⟩)
    (σ k', ⟨positiveRoundedWordPeriodTime w η, ht'⟩)).mp hv
  rcases hr with hr | hr | hr
  · have hk : k = k' := σ.injective (congrArg Prod.fst hr)
    have htime := congrArg (fun p : PositiveRectilinearWordTangleSource w => (p.2 : ℝ)) hr
    have hangle : θ = η := by
      change (2 * (w.length : ℝ) + 1) * θ / (2 * Real.pi) =
        (2 * (w.length : ℝ) + 1) * η / (2 * Real.pi) at htime
      have hh := (div_left_inj' (ne_of_gt Real.two_pi_pos)).mp htime
      exact (mul_left_cancel₀ (by positivity : (2 * (w.length : ℝ) + 1) ≠ 0)) hh
    rw [hk, hangle]
  · exact False.elim (htlt'.ne hr.2.1)
  · exact False.elim (htlt.ne hr.1)

/-- The descended slices are native-circle topological embeddings, with the exact
rounded cylinder formula at every labelled parameter. -/
theorem exists_positiveRoundedWord_circle_embeddings {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ k, σ (finRotate m k) = w.permutation.symm (σ k))
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j)) :
    ∃ F : Circle × ℝ → Circle × ℂ,
      ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ F ∧
      (∀ k θ s, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        F (braidCircleSheet m k θ, s) = positiveRectilinearCylinderPoint w
          (positiveRoundedWordDeformation w l u (σ k) s (positiveRoundedWordPeriodTime w θ))) ∧
      ∀ s, Topology.IsClosedEmbedding (fun v : Circle => F (v, s)) := by
  have hU' : U ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  obtain ⟨F, hF, he⟩ := exists_positiveRoundedWord_circle_family hm w σ hσ hl hu hU' hls hus
  refine ⟨F, hF, he, fun s => ?_⟩
  exact (hF.continuous.comp (continuous_id.prodMk continuous_const)).isClosedEmbedding
    (positiveRoundedWord_circle_family_injective hm w σ hU hl hu hla hua he s)

end OnLeConjecture.KnotTheory
