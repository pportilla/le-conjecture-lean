/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneSectionGeometry
public import OnLeConjecture.Analytic.SectionImageQuotient
public import OnLeConjecture.Analytic.SectionImageSquareSum
public import OnLeConjecture.Analytic.RawProjectiveWeakBlowupExistence
public import OnLeConjecture.Analytic.FiniteColength

/-!
# Generic target coordinates for plane sections

For a locally injective germ `g : (ℂ², 0) → (ℂ³, 0)` there is an invertible
linear change of target coordinates `M` such that the new first component
`λ₁ ∘ g` (with `λ₁` the first row of `M`) is reduced and meets the new third
component finitely. The reduced first component comes from an open set of
reduced members of the weak-blowup tree of `g`, and the third component is a
companion that meets it finitely.

The specialization theorem therefore holds for every locally injective germ
after this linear change of target coordinates.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open Filter Metric Set
open scoped Topology
open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- A locally injective plane germ in three-space admits an invertible linear
target change whose first new component is reduced and meets the third new
component finitely. -/
theorem PointedMapGerm.exists_generic_target_matrix (g : PointedMapGerm 2 3)
    (hi : g.HasInjectiveRepresentative) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℂ, M.det ≠ 0 ∧
      Squarefree (germLinearCombination g.1.component (M 0)) ∧
      HasFiniteIntersection (germLinearCombination g.1.component (M 0))
        (germLinearCombination g.1.component (M 2)) := by
  classical
  have hIdeal : g.1.coordinateIdeal = Ideal.span (Set.range g.1.component) := by
    apply le_antisymm
    · rw [MapGerm.coordinateIdeal_le]
      intro i
      exact Ideal.subset_span (Set.mem_range_self i)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact g.1.component_mem_coordinateIdeal i
  have hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range g.1.component)) := by
    rw [← hIdeal]
    exact g.coordinateQuotient_moduleFinite (g.injective_isFiniteAtOrigin_two hi)
  obtain ⟨T⟩ := RawProjectiveWeakBlowupTree.exists_of_finite_colength g.1.component
    (fun i => g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal i)) hfinite
  obtain ⟨V, -, ⟨q, hqV⟩, -, hV⟩ := T.exists_open_reduced_members Set.univ isOpen_univ
    ⟨0, Set.mem_univ _⟩
  have hq := fun p => (hV q hqV p).1
  have hsq : Squarefree (germLinearCombination g.1.component q) := by
    simpa only [T.generators_root] using (hV q hqV T.root).2
  obtain ⟨r, -, hfin, -⟩ := T.exists_companion_intersection_eq_squareSum_mem_open q hq
    Set.univ isOpen_univ ⟨0, Set.mem_univ _⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsq
    exact not_squarefree_zero hsq
  obtain ⟨s, hs⟩ := exists_row_completion_of_finite_intersection g q r hq0 hfin
  refine ⟨targetThreeRows q s r, ?_, hsq, hfin⟩
  intro hdet
  apply hs
  simp [Matrix.det_fin_three, targetThreeRows] at hdet ⊢
  linear_combination -hdet

theorem germLinearCombination_ofFunction_component (G : Source 2 → Source 3)
    (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0) (q : Fin 3 → ℂ) :
    germLinearCombination (PointedMapGerm.ofFunction G hG hG0).1.component q =
      ofFunction (fun x => ∑ k, q k * G x k)
        (Finset.analyticAt_fun_sum _ fun k _ =>
          analyticAt_const.mul ((analyticAt_pi_iff.mp hG) k)) := by
  have hF (k : Fin 3) : (PointedMapGerm.ofFunction G hG hG0).1.component k =
      ofFunction (fun x => G x k) ((analyticAt_pi_iff.mp hG) k) :=
    Subtype.ext (MapGerm.component_ofFunction G hG k)
  have hGk (k : Fin 3) : AnalyticAt ℂ (fun x => q k * G x k) 0 :=
    analyticAt_const.mul ((analyticAt_pi_iff.mp hG) k)
  have h1 : germLinearCombination (PointedMapGerm.ofFunction G hG hG0).1.component q =
      ofFunction (fun x => q 0 * G x 0 + q 1 * G x 1 + q 2 * G x 2)
        (((hGk 0).add (hGk 1)).add (hGk 2)) := by
    change ∑ k, q k • (PointedMapGerm.ofFunction G hG hG0).1.component k = _
    rw [Fin.sum_univ_three, hF 0, hF 1, hF 2]
    rfl
  rw [h1]
  apply ofFunction_eq_of_eventuallyEq
  filter_upwards with x
  simp [Fin.sum_univ_three]

/-- **Specialization of plane sections after a linear target change.** Let
`g` be a locally injective germ `(ℂ², 0) → (ℂ³, 0)` with analytic
representative `G`. There is an invertible matrix `M` such that all
conclusions of `plane_section_specialization` hold for the representative
`G' = M G`, whose first component is `λ₁ ∘ G` for the first row `λ₁` of `M`.
In particular `V₀ = {λ₁ ∘ G = 0}` is reduced, and for every sufficiently small
radius and every sufficiently small nonzero `s`,
`δ(W₀) = δ(V₀) + ∑_{x ∈ Z} δ(W_s, G'(x))`, where `Z` is the finite set of
critical points of `G'` on `{λ₁ ∘ G = s}`. Its cardinality `N` does not depend
on `s`, is positive when `dg = 0`, and is zero when `dg` is injective. The
quotient of the source ring by the image ring is finite and free over `ℂ{t}`
acting through `t ↦ λ₁ ∘ g`, and its rank is `δ(W₀) - δ(V₀)`. -/
theorem plane_section_specialization_generic
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = PointedMapGerm.ofFunction G hG hG0) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℂ, M.det ≠ 0 ∧
      ∃ (hG' : AnalyticAt ℂ (fun x => M.mulVec (G x)) 0)
        (hG'0 : M.mulVec (G 0) = 0),
        let g' := PointedMapGerm.ofFunction (fun x => M.mulVec (G x)) hG' hG'0
        g'.HasInjectiveRepresentative ∧
        Squarefree (g'.1.component 0) ∧
        ∃ D : SectionImageFactorization g',
          (letI : Algebra (Germ 1) (Germ 2) := g'.sectionParameterHom.toAlgebra
            ∃ A : Submodule (Germ 1) (Germ 2), (A : Set (Germ 2)) = g'.ImageRing ∧
              Module.Finite (Germ 1) (Germ 2 ⧸ A) ∧ Module.Free (Germ 1) (Germ 2 ⧸ A) ∧
              deltaInvariant D.imageEquation =
                deltaInvariant (g'.1.component 0) + Module.finrank (Germ 1) (Germ 2 ⧸ A)) ∧
          ∃ N : ℕ, (g.differential = 0 → 0 < N) ∧ (Function.Injective g.differential → N = 0) ∧
            ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 0 →
              ∃ Z : Finset (Source 2),
                (∀ x, x ∈ Z ↔ (x ∈ ball (0 : Source 2) r ∧ M.mulVec (G x) 0 = s ∧
                  ¬ Function.Injective (fderiv ℂ (fun y => M.mulVec (G y)) x))) ∧
                Z.card = N ∧
                InjOn (fun x => M.mulVec (G x)) (ball (0 : Source 2) r) ∧
                Topology.IsClosedEmbedding
                  ((closedBall (0 : Source 2) r ∩ (fun x => M.mulVec (G x) 0) ⁻¹' {s}).domRestrict
                    (fun x => M.mulVec (G x))) ∧
                (∀ x ∈ ball (0 : Source 2) r, M.mulVec (G x) 0 = s →
                  fderiv ℂ (fun y => M.mulVec (G y) 0) x ≠ 0 ∧
                  ∃ (hGx : AnalyticAt ℂ (fun y => M.mulVec (G y)) x)
                    (Dx : SectionImageFactorization
                      (PointedMapGerm.recenterOfFunction (fun y => M.mulVec (G y)) x hGx)),
                    Irreducible Dx.imageEquation ∧
                    (Dx.imageEquation ∈ maximalIdeal 2 ^ 2 ↔ x ∈ Z) ∧
                    localSectionDelta (fun y => M.mulVec (G y)) x =
                      deltaInvariant Dx.imageEquation ∧
                    (0 < localSectionDelta (fun y => M.mulVec (G y)) x ↔ x ∈ Z) ∧
                    ∀ (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0),
                      Dx.imageEquation = ofFunction W hW →
                      ∀ T ∈ 𝓝 (0 : Source 2), ∃ ρ : ℝ, 0 < ρ ∧
                        closedBall (0 : Source 2) ρ ⊆ T ∧
                        ∀ᶠ y in 𝓝 (0 : Source 2), W y = 0 ↔
                          ∃ z ∈ closedBall (0 : Source 2) ρ,
                            M.mulVec (G (x + z)) - M.mulVec (G x) =
                              hyperplaneInclusion 2 y) ∧
                deltaInvariant D.imageEquation =
                  deltaInvariant (g'.1.component 0) +
                    ∑ x ∈ Z, localSectionDelta (fun y => M.mulVec (G y)) x := by
  classical
  obtain ⟨M, hdet, hsqM, hfinM⟩ := g.exists_generic_target_matrix hi
  let L : Source 3 →L[ℂ] Source 3 := (Matrix.toLin' M).toContinuousLinearMap
  have hL (y : Source 3) : L y = M.mulVec y := rfl
  have hG' : AnalyticAt ℂ (fun x => M.mulVec (G x)) 0 := (L.analyticAt _).comp hG
  have hG'0 : M.mulVec (G 0) = 0 := by rw [hG0, Matrix.mulVec_zero]
  set G' : Source 2 → Source 3 := fun x => M.mulVec (G x) with hG'def
  set g' := PointedMapGerm.ofFunction G' hG' hG'0 with hg'def
  have hcomp (j : Fin 3) : g'.1.component j = germLinearCombination g.1.component (M j) := by
    rw [hg, germLinearCombination_ofFunction_component G hG hG0 (M j)]
    apply Subtype.ext
    rw [hg'def, PointedMapGerm.ofFunction, MapGerm.component_ofFunction]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards with x
    simp [hG'def, Matrix.mulVec, dotProduct]
  have hsq' : Squarefree (g'.1.component 0) := by rw [hcomp 0]; exact hsqM
  have haxis' : HasFiniteIntersection (g'.1.component 0) (g'.1.component 2) := by
    rw [hcomp 0, hcomp 2]
    exact hfinM
  have hMinj : Function.Injective M.mulVec := by
    intro a b hab
    have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
    have h := congrArg (M⁻¹).mulVec hab
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu] using h
  have hi' : g'.HasInjectiveRepresentative := by
    obtain ⟨G₁, hG₁, hG₁0, hg₁, S, hS, hinj⟩ := hi
    have hGG₁ : G =ᶠ[𝓝 0] G₁ :=
      Filter.Germ.coe_eq.mp (congrArg (fun p => p.1.1) (hg.symm.trans hg₁))
    refine ⟨G', hG', hG'0, rfl, S ∩ {x | G x = G₁ x}, inter_mem hS hGG₁, ?_⟩
    intro a ha b hb hab
    apply hinj ha.1 hb.1
    rw [← ha.2, ← hb.2]
    exact hMinj hab
  obtain ⟨D⟩ := g'.exists_sectionImageFactorization hi' hsq'
  have hgd : g.differential = fderiv ℂ G 0 := by
    rw [hg, PointedMapGerm.differential_ofFunction]
  have hg'd : g'.differential = L.comp g.differential := by
    rw [hg'def, PointedMapGerm.differential_ofFunction, hgd]
    exact (L.hasFDerivAt.comp 0 hG.differentiableAt.hasFDerivAt).fderiv
  have hdiff : g.differential = 0 → g'.differential = 0 := by
    intro h0
    rw [hg'd, h0, ContinuousLinearMap.comp_zero]
  have hdiffinj : Function.Injective g.differential → Function.Injective g'.differential := by
    intro hinjd
    rw [hg'd]
    exact hMinj.comp hinjd
  obtain ⟨N, hpos, hzero, r₀, hr₀, hmain⟩ :=
    plane_section_specialization g' hi' D haxis' G' hG' hG'0 rfl
  refine ⟨M, hdet, hG', hG'0, hi', hsq', D, ?_, N, fun h0 => hpos (hdiff h0),
    fun hinjd => hzero (hdiffinj hinjd), r₀, hr₀, hmain⟩
  obtain ⟨A, hA, hfin, hfree, hrank⟩ := D.imageQuotient_finite_free hi' haxis'
  refine ⟨A, hA, hfin, hfree, ?_⟩
  rw [hrank]
  exact (D.finiteDimensional_and_deltaInvariant_imageEquation hi').2.1


end OnLeConjecture.Analytic
