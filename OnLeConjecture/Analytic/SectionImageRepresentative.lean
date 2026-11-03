/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedSectionImage

/-!
# Representative coverage of the reduced section image

The product of the constructed image-branch equations describes the entire
nearby image of the coordinate section. The proof uses the previously
constructed proper hypersurface image and the divisibility identities of
the section equations. Equality of germ ideals is not used as a substitute
for pointwise image coverage.
-/

public noncomputable section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic.SectionImageFactorization

open OnLeConjecture.Analytic.Germ

variable {g : PointedMapGerm 2 3} (D : SectionImageFactorization g)

/-- The zero set of the constructed plane equation is exactly the nearby
image of the source coordinate section in an arbitrarily small closed ball. -/
theorem exists_closedBall_section_image_eq_zero_set
    (hi : g.HasInjectiveRepresentative)
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = PointedMapGerm.ofFunction G hG hG0)
    (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0)
    (hWeq : D.imageEquation = ofFunction W hW)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : Source 2) r ⊆ S ∧
      AnalyticOnNhd ℂ G (closedBall 0 r) ∧
      ∀ᶠ y in 𝓝 (0 : Source 2),
        W y = 0 ↔ ∃ x ∈ closedBall (0 : Source 2) r, G x = hyperplaneInclusion 2 y := by
  have hf := g.injective_isFiniteAtOrigin_two hi
  obtain ⟨f, _, _, hker⟩ := g.exists_irreducible_generator_of_finite hf
  obtain ⟨F, hF, hfF⟩ := exists_ofFunction f
  rw [hfF] at hker
  have hz : g.pullbackRingHom (ofFunction F hF) = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hWdiv := D.imageEquation_dvd_restriction_of_pullback_zero hi _ hz
  rw [hWeq, hyperplaneRestriction_ofFunction] at hWdiv
  have htarget := eventually_zero_imp_zero_of_dvd W (F ∘ hyperplaneInclusion 2)
    hW (hF.comp_of_eq ((hyperplaneInclusion 2).analyticAt 0) (map_zero _)) hWdiv
  have hV : AnalyticAt ℂ (fun x => G x 0) 0 :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt _).comp hG
  have hWG : AnalyticAt ℂ (fun x => W (hyperplaneTail 2 (G x))) 0 := by
    exact hW.comp_of_eq (((hyperplaneTail 2).analyticAt _).comp hG)
      (by rw [hG0, map_zero])
  have hsourceDiv := (D.imageEquation_dvd_iff hi D.imageEquation).mp dvd_rfl
  rw [hWeq, hg, hyperplaneExtension_ofFunction, PointedMapGerm.pullbackRingHom_apply,
    compPointed_ofFunction] at hsourceDiv
  have hsourceDiv' : ofFunction (fun x => G x 0) hV ∣
      ofFunction (fun x => W (hyperplaneTail 2 (G x))) hWG := by
    have hc : (PointedMapGerm.ofFunction G hG hG0).1.component 0 =
        ofFunction (fun x => G x 0) hV := by
      apply Subtype.ext
      exact MapGerm.component_ofFunction G hG 0
    rwa [hc] at hsourceDiv
  have hsource := eventually_zero_imp_zero_of_dvd (fun x => G x 0)
    (fun x => W (hyperplaneTail 2 (G x))) hV hWG hsourceDiv'
  obtain ⟨r, hr, hrS, hGr, _, _, himage⟩ :=
    g.exists_closedBall_image_eq_zero_set_of_finite hf G hG hG0 hg F hF hker
      (S ∩ {x | G x 0 = 0 → W (hyperplaneTail 2 (G x)) = 0}) (inter_mem hS hsource)
  have htargetImage :=
    ((hyperplaneInclusion 2).continuous.tendsto' _ _ (map_zero _)).eventually himage
  refine ⟨r, hr, fun x hx => (hrS hx).1, hGr, ?_⟩
  filter_upwards [htarget, htargetImage] with y hWy hFy
  constructor
  · intro hy
    exact hFy.mp (hWy hy)
  · rintro ⟨x, hx, hxy⟩
    have hhead : G x 0 = 0 := by rw [hxy, hyperplaneInclusion_apply_zero]
    have hzero := (hrS hx).2 hhead
    simpa only [hxy, hyperplaneTail_inclusion] using hzero

end OnLeConjecture.Analytic.SectionImageFactorization
