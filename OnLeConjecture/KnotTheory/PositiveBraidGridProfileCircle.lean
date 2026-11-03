/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridProfileInterpolation

/-! # Joint native circle descent of convex profile interpolation

The same period collars descend the profile interpolation without changing the
word, labels, or progress parameter. Each slice equals a slice of the released
native rounded-word family for that slice's admissible profiles.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic
attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.KnotTheory

/-- The actual convex profile word descends jointly smoothly to the same source circle. -/
theorem exists_positiveRoundedWordProfileInterpolation_circle_family {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ k, σ (finRotate m k) = w.permutation.symm (σ k))
    {l₀ u₀ l₁ u₁ : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hl₁ : ∀ j, EqOn (l₁ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₁ : ∀ j, EqOn (u₁ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hU : U ⊆ Ioo (0 : ℝ) 1)
    (hls₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hus₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    (hls₁ : ∀ j, ContDiff ℝ ∞ (l₁ j)) (hus₁ : ∀ j, ContDiff ℝ ∞ (u₁ j)) :
    ∃ F : Circle × ℝ → Circle × ℂ,
      ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ F ∧
      ∀ k θ s, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        F (braidCircleSheet m k θ, s) = positiveRectilinearCylinderPoint w
          (positiveRoundedWordProfileInterpolation w l₀ u₀ l₁ u₁ (σ k) s
            (positiveRoundedWordPeriodTime w θ)) := by
  let H := fun k (p : ℝ × ℝ) => positiveRoundedWordProfileInterpolation w l₀ u₀ l₁ u₁ (σ k) p.1
    (positiveRoundedWordPeriodTime w p.2)
  have hH (k) : ContDiff ℝ ∞ (H k) :=
    (positiveRoundedWordProfileInterpolation_contDiff w hls₀ hus₀ hls₁ hus₁ (σ k)).comp
      (contDiff_fst.prodMk ((positiveRoundedWordPeriodTime_contDiff w).comp contDiff_snd))
  have hleft : ∀ k, ∀ᶠ θ in 𝓝 (0 : ℝ), ∀ s,
      H k (s, θ) = (positiveRoundedWordPeriodTime w θ, ((σ k).val : ℂ)) := by
    intro k
    have ht : ∀ᶠ θ in 𝓝 (0 : ℝ), positiveRoundedWordPeriodTime w θ < 1 / 3 :=
      ((positiveRoundedWordPeriodTime_contDiff w).continuous.continuousAt).eventually
        (eventually_lt_nhds (by simp))
    filter_upwards [ht] with θ hθ
    intro s
    simpa only [positiveRoundedWordDeformation_one, H,
      positiveRoundedWordProfileInterpolation] using
      positiveRoundedWordDeformation_initial_open_collar w
        (fun j => positiveGridProfileInterpolation_eqOn (hl₀ j) (hl₁ j) s)
        (fun j => positiveGridProfileInterpolation_eqOn (hu₀ j) (hu₁ j) s) hU (σ k) 1 hθ.le
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
    simpa only [positiveRoundedWordDeformation_one, H,
      positiveRoundedWordProfileInterpolation] using
      positiveRoundedWordDeformation_final_open_collar w
        (fun j => positiveGridProfileInterpolation_eqOn (hl₀ j) (hl₁ j) s)
        (fun j => positiveGridProfileInterpolation_eqOn (hu₀ j) (hu₁ j) s) hU (σ k) 1 hθ.le
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

/-- Every interpolation circle slice is a closed embedding with injective native
differential, by equality with the released family for its interpolated profiles. -/
theorem positiveRoundedWordProfileInterpolation_circle_regular {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ k, σ (finRotate m k) = w.permutation.symm (σ k))
    {l₀ u₀ l₁ u₁ : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hl₁ : ∀ j, EqOn (l₁ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₁ : ∀ j, EqOn (u₁ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla₀ : ∀ j t, dist (l₀ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₀ : ∀ j t, dist (u₀ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hla₁ : ∀ j t, dist (l₁ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₁ : ∀ j t, dist (u₁ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hus₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    (hls₁ : ∀ j, ContDiff ℝ ∞ (l₁ j)) (hus₁ : ∀ j, ContDiff ℝ ∞ (u₁ j))
    {F : Circle × ℝ → Circle × ℂ}
    (he : ∀ k θ s, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      F (braidCircleSheet m k θ, s) = positiveRectilinearCylinderPoint w
        (positiveRoundedWordProfileInterpolation w l₀ u₀ l₁ u₁ (σ k) s
          (positiveRoundedWordPeriodTime w θ))) (s : ℝ) :
    Topology.IsClosedEmbedding (fun v : Circle => F (v, s)) ∧
      ∀ v, Function.Injective (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ))
        (fun v => F (v, s)) v) := by
  have hl (j) := positiveGridProfileInterpolation_eqOn (hl₀ j) (hl₁ j) s
  have hu (j) := positiveGridProfileInterpolation_eqOn (hu₀ j) (hu₁ j) s
  have hla (j t) := positiveGridProfileInterpolation_dist_lt (hla₀ j) (hla₁ j) s t
  have hua (j t) := positiveGridProfileInterpolation_dist_lt (hua₀ j) (hua₁ j) s t
  have hls (j) := (positiveGridProfileInterpolation_contDiff (hls₀ j) (hls₁ j)).comp
    (contDiff_const (c := s) |>.prodMk contDiff_id)
  have hus (j) := (positiveGridProfileInterpolation_contDiff (hus₀ j) (hus₁ j)).comp
    (contDiff_const (c := s) |>.prodMk contDiff_id)
  obtain ⟨G, hG, heG, hEmb⟩ := exists_positiveRoundedWord_circle_embeddings hm w σ hσ hU
    hl hu hla hua hls hus
  have hFG : (fun v : Circle => F (v, s)) = fun v => G (v, 1) := by
    funext v
    obtain ⟨θ, hθ, k, rfl⟩ := exists_braidCircleSheet_half_open hm v
    rw [he k θ s ⟨hθ.1, hθ.2.le⟩, heG k θ 1 ⟨hθ.1, hθ.2.le⟩,
      positiveRoundedWordDeformation_one]
    rfl
  rw [hFG]
  refine ⟨hEmb 1, ?_⟩
  have hU' : U ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  exact positiveRoundedWord_circle_family_mfderiv_injective hm w σ hl hu hU' hls hus hG heG 1

end OnLeConjecture.KnotTheory
