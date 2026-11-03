/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionAssembly

/-!
# Section data with coefficients in prescribed open sets

The existing coordinate selection chooses the first coefficient vector `q`
and the companion row `r` in `Set.univ`. The underlying selection theorems
accept arbitrary nonempty open sets. We choose `q` in a prescribed nonempty
open set `U` and `r` in a prescribed nonempty open set `U₃`, keeping one tree,
one coefficient vector, one invertible target matrix with rows `q, s, r` and
one analytic representative throughout. The second row `s` is a row
completion and is not constrained.

* `RawProjectiveWeakBlowupTree.exists_tree_section_coordinates_in_open`,
* `PointedMapGerm.exists_generic_target_matrix_in_open`,
* `ResolutionSectionAssembly.exists_of_tree_coordinates`: the assembly
  construction for given tree coordinates, with the same proof as
  `PointedMapGerm.exists_resolutionSectionAssembly`,
* `PointedMapGerm.exists_resolutionSectionAssembly_in_open`.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve

namespace RawProjectiveWeakBlowupTree

/-- **Tree coordinates in prescribed open sets.** The statement of
`exists_tree_section_coordinates`, with the first row `q` in `U` and the third
row in `U₃`. -/
theorem exists_tree_section_coordinates_in_open (g : PointedMapGerm 2 3)
    (hi : g.HasInjectiveRepresentative) (U U₃ : Set (Fin 3 → ℂ))
    (hU : IsOpen U) (hne : U.Nonempty) (hU₃ : IsOpen U₃) (hne₃ : U₃.Nonempty) :
    ∃ (T : RawProjectiveWeakBlowupTree g.1.component) (q : Fin 3 → ℂ)
      (A : Matrix (Fin 3) (Fin 3) ℂ),
      (∀ p, germLinearCombination (T.generators p) q ∉
        maximalIdeal 2 ^ (T.multiplicity p + 1)) ∧
      Squarefree (germLinearCombination g.1.component q) ∧
      2 * deltaInvariant (germLinearCombination g.1.component q) + (∑ p, T.multiplicity p) =
        ∑ p, (T.multiplicity p) ^ 2 ∧
      A.det ≠ 0 ∧ A 0 = q ∧
      HasFiniteIntersection (germLinearCombination g.1.component (A 0))
        (germLinearCombination g.1.component (A 2)) ∧
      q ∈ U ∧ A 2 ∈ U₃ ∧
      ∀ p, Squarefree (germLinearCombination (T.generators p) q) := by
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
  obtain ⟨q₀, -, hq₀⟩ := T.exists_exact_coefficients Set.univ isOpen_univ Set.univ_nonempty
  obtain ⟨V, -, ⟨q, hqV⟩, hVU, hV⟩ :=
    T.exists_open_reduced_members_delta_identity q₀ hq₀ U hU hne
  obtain ⟨hmembers, hdelta⟩ := hV q hqV
  have hq := fun p => (hmembers p).1
  have hsq : Squarefree (germLinearCombination g.1.component q) := by
    simpa only [T.generators_root] using (hmembers T.root).2
  obtain ⟨r, hrU, hfin, -⟩ := T.exists_companion_intersection_eq_squareSum_mem_open q hq
    U₃ hU₃ hne₃
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsq
    exact not_squarefree_zero hsq
  obtain ⟨s, hs⟩ := exists_row_completion_of_finite_intersection g q r hq0 hfin
  refine ⟨T, q, targetThreeRows q s r, hq, hsq, hdelta, ?_, rfl, hfin, hVU hqV, hrU,
    fun p => (hmembers p).2⟩
  intro hdet
  apply hs
  simp [Matrix.det_fin_three, targetThreeRows] at hdet ⊢
  linear_combination -hdet

end RawProjectiveWeakBlowupTree

/-- **Generic target matrix in prescribed open sets.** The statement of
`exists_generic_target_matrix`, with the first row in `U` and the third row
in `U₃`. -/
theorem PointedMapGerm.exists_generic_target_matrix_in_open (g : PointedMapGerm 2 3)
    (hi : g.HasInjectiveRepresentative) (U U₃ : Set (Fin 3 → ℂ))
    (hU : IsOpen U) (hne : U.Nonempty) (hU₃ : IsOpen U₃) (hne₃ : U₃.Nonempty) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℂ, M.det ≠ 0 ∧
      Squarefree (germLinearCombination g.1.component (M 0)) ∧
      HasFiniteIntersection (germLinearCombination g.1.component (M 0))
        (germLinearCombination g.1.component (M 2)) ∧
      M 0 ∈ U ∧ M 2 ∈ U₃ := by
  obtain ⟨-, q, M, -, hsq, -, hdet, hrow, hfin, hqU, hr, -⟩ :=
    RawProjectiveWeakBlowupTree.exists_tree_section_coordinates_in_open g hi U U₃ hU hne hU₃ hne₃
  exact ⟨M, hdet, hrow ▸ hsq, hfin, hrow ▸ hqU, hr⟩

namespace ResolutionSectionAssembly

/-- **Assembly from given tree coordinates.** Every tree `T`, coefficient
vector `q` and invertible matrix `M` with the conclusions of
`exists_tree_section_coordinates` are the tree, coefficients and matrix of an
assembly. The proof is that of `PointedMapGerm.exists_resolutionSectionAssembly`
after its first step. -/
theorem exists_of_tree_coordinates (g : PointedMapGerm 2 3)
    (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative)
    (T : RawProjectiveWeakBlowupTree g.1.component) (q : Fin 3 → ℂ)
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hsqv : Squarefree (germLinearCombination g.1.component q))
    (hδ : 2 * deltaInvariant (germLinearCombination g.1.component q) +
      (∑ p, T.multiplicity p) = ∑ p, (T.multiplicity p) ^ 2)
    (hdet : A.det ≠ 0) (hrow : A 0 = q)
    (hfinA : HasFiniteIntersection (germLinearCombination g.1.component (A 0))
      (germLinearCombination g.1.component (A 2))) :
    ∃ B : ResolutionSectionAssembly g hd hi,
      B.tree = T ∧ B.coefficients = q ∧ B.matrix = A := by
  classical
  have hi' := hi
  obtain ⟨G, hG, hG0, hg, S₀, hS₀, hinj₀⟩ := hi'
  let L : Source 3 →L[ℂ] Source 3 := (Matrix.toLin' A).toContinuousLinearMap
  have hH : AnalyticAt ℂ (fun x => A.mulVec (G x)) 0 := (L.analyticAt _).comp hG
  have hH0 : A.mulVec (G 0) = 0 := by rw [hG0, Matrix.mulVec_zero]
  set H : Source 2 → Source 3 := fun x => A.mulVec (G x) with hHdef
  set f := PointedMapGerm.ofFunction H hH hH0 with hfdef
  have hcomp (j : Fin 3) : f.1.component j = germLinearCombination g.1.component (A j) := by
    rw [hg, germLinearCombination_ofFunction_component G hG hG0 (A j)]
    apply Subtype.ext
    rw [hfdef, PointedMapGerm.ofFunction, MapGerm.component_ofFunction]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards with x
    simp [hHdef, Matrix.mulVec, dotProduct]
  have hf0 : f.1.component 0 = germLinearCombination g.1.component q := by rw [hcomp 0, hrow]
  have hsqf : Squarefree (f.1.component 0) := by rw [hf0]; exact hsqv
  have haxis : HasFiniteIntersection (f.1.component 0) (f.1.component 2) := by
    rw [hcomp 0, hcomp 2]
    exact hfinA
  have hMinj : Function.Injective A.mulVec := by
    intro a b hab
    have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
    have h := congrArg (A⁻¹).mulVec hab
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu] using h
  have hif : f.HasInjectiveRepresentative :=
    ⟨H, hH, hH0, rfl, S₀, hS₀, fun a ha b hb hab => hinj₀ ha hb (hMinj hab)⟩
  have hspan : Submodule.span ℂ (Set.range f.1.component) =
      Submodule.span ℂ (Set.range g.1.component) := by
    rw [show f.1.component = fun i => ∑ j, A i j • g.1.component j from funext hcomp]
    exact span_matrix_linear_combinations A hdet g.1.component
  have hmax : (f.criticalJacobianFactorization hif).maxMultiplicity =
      (g.criticalJacobianFactorization hi).maxMultiplicity :=
    PointedMapGerm.criticalJacobian_maxMultiplicity_eq_of_span_eq g f hi hif hspan
  have hdf : f.differential = 0 := by
    rw [hfdef, PointedMapGerm.differential_ofFunction]
    have hgd : fderiv ℂ G 0 = 0 := by
      rw [← PointedMapGerm.differential_ofFunction G hG hG0, ← hg]
      exact hd
    have hHd : HasFDerivAt H (L.comp (fderiv ℂ G 0)) 0 :=
      L.hasFDerivAt.comp 0 hG.differentiableAt.hasFDerivAt
    rw [hHd.fderiv, hgd, ContinuousLinearMap.comp_zero]
  obtain ⟨D⟩ := f.exists_sectionImageFactorization hif hsqf
  obtain ⟨hWmem, hWnot⟩ :=
    T.imageEquation_exact_squareSum_of_component_zero hi q hq f hif hf0 hspan D
  obtain ⟨-, hδW, -⟩ := D.finiteDimensional_and_deltaInvariant_imageEquation hif
  obtain ⟨N, hpos, -, r₀, hr₀, hmain⟩ :=
    plane_section_specialization f hif D haxis H hH hH0 rfl
  have hcrit := eventually_critical_transverse_image_equation f hif hsqf H hH hH0 rfl
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hcrit
  set δsing := Module.finrank ℂ (Germ 2 ⧸ (LinearMap.range f.pullbackAlgHom.toLinearMap ⊔
    (Ideal.span {f.1.component 0}).restrictScalars ℂ)) with hδsing
  refine ⟨{
    tree := T
    coefficients := q
    coefficients_exact := hq
    matrix := A
    matrix_det := hdet
    matrix_row_zero := hrow
    G := G
    G_analytic := hG
    G_zero := hG0
    G_eq := hg
    H := H
    H_eq := fun x => rfl
    H_analytic := hH
    H_zero := hH0
    H_injective := hif
    sourceEquation := germLinearCombination g.1.component q
    sourceEquation_eq := rfl
    sourceEquation_component := hf0
    sourceEquation_squarefree := hsqv
    factorization := D
    imageEquation := D.imageEquation
    imageEquation_eq := rfl
    imageEquation_squarefree := D.imageEquation_squarefree hif
    imageEquation_mem := hWmem
    imageEquation_not_mem := hWnot
    imageEquation_zero_set := fun W hW hWeq U hU => by
      obtain ⟨ρ, hρ, hρU, -, hiff⟩ :=
        D.exists_closedBall_section_image_eq_zero_set hif H hH hH0 rfl W hW hWeq U hU
      exact ⟨ρ, hρ, hρU, hiff⟩
    central_delta := hδ
    singularDelta := δsing
    image_delta := by rw [← hf0]; exact hδW
    count := N
    count_pos := hpos hdf
    radius := min r₀ ε
    radius_pos := lt_min hr₀ hε
    levels := ?_ }, rfl, rfl, rfl⟩
  intro r hr hrle
  have hr₀' : r ≤ r₀ := hrle.trans (min_le_left _ _)
  have hrε : r ≤ ε := hrle.trans (min_le_right _ _)
  filter_upwards [hmain r hr hr₀'] with s hs hs0
  obtain ⟨Z, hZ, hcard, hinjr, hemb, hpoint, hδZ⟩ := hs hs0
  have hinjx (x : Source 2) (hx : x ∈ ball (0 : Source 2) r) (hHx : AnalyticAt ℂ H x) :
      (PointedMapGerm.recenterOfFunction H x hHx).HasInjectiveRepresentative :=
    PointedMapGerm.recenter_hasInjectiveRepresentative H x hHx _ (isOpen_ball.mem_nhds hx) hinjr
  have hlocal (x : Source 2) (hx : x ∈ ball (0 : Source 2) r) (hvx : H x 0 = s) :
      localSectionDelta H x = deltaInvariant (localSectionEquation H x) ∧
      (localSectionEquation H x ∈ maximalIdeal 2 ^ 2 ↔ x ∈ Z) := by
    obtain ⟨-, hHx, Dx, -, hsing, -, -, -⟩ := hpoint x hx hvx
    obtain ⟨D', hD', hδ'⟩ := exists_localSectionEquation_spec H x hHx (hinjx x hx hHx) Dx
    refine ⟨hδ', ?_⟩
    rw [hD', mem_ideal_iff_of_associated (D'.associated_imageEquation Dx (hinjx x hx hHx))]
    exact hsing
  refine ⟨Z, hZ, hcard, hinjr, hemb, fun x hx hvx => ⟨(hpoint x hx hvx).1, (hlocal x hx hvx).2⟩,
    ?_, ?_⟩
  · intro x hxZ
    obtain ⟨hx, hvx, hni⟩ := (hZ x).mp hxZ
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hs0 (hvx.symm.trans (by simp [hHdef, hG0]))
    obtain ⟨hHx, e, P, β, w, a, hPm, he, hep, hβ, hβinj, hwirr, hwker, hwm, hwn, ha2, ham⟩ :=
      hεsub (ball_subset_ball hrε hx) hx0 hni
    obtain ⟨-, hHx', Dx, -, -, -, -, -⟩ := hpoint x hx hvx
    obtain ⟨D', hD', -⟩ := exists_localSectionEquation_spec H x hHx (hinjx x hx hHx) Dx
    have hass : Associated w (localSectionEquation H x) := by
      rw [hD']
      exact associated_imageEquation_of_transverse_parametrization (hinjx x hx hHx) D' e he
        P hPm hep β hβ w hwker
    refine ⟨hHx, D', e, β, a, hD', hass.irreducible hwirr,
      (mem_ideal_iff_of_associated hass _).mp hwm,
      fun h => hwn ((mem_ideal_iff_of_associated hass _).mpr h), ha2, hmax ▸ ham, he, hβ, hβinj,
      ?_, ?_⟩
    · rw [hwker]
      exact Ideal.span_singleton_eq_span_singleton.mpr hass
    · intro W hW hWeq U hU
      rw [hD'] at hWeq
      obtain ⟨ρ, hρ, hρU, -, hiff⟩ := D'.exists_closedBall_section_image_eq_zero_set
        (hinjx x hx hHx) (fun z => H (x + z) - H x) _ _ rfl W hW hWeq U hU
      exact ⟨ρ, hρ, hρU, hiff⟩
  · have hsum : ∑ x ∈ Z, localSectionDelta H x = δsing := by
      have h1 := hδZ
      rw [hδW] at h1
      omega
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro x hxZ
    obtain ⟨hx, hvx, -⟩ := (hZ x).mp hxZ
    exact ((hlocal x hx hvx).1).symm

end ResolutionSectionAssembly

/-- **Assembly with prescribed open coefficients.** The first coefficient
vector lies in the prescribed nonempty open set `U`, the third row of the
target matrix lies in the prescribed nonempty open set `U₃`, and the member
`q ⋅ g_p` of the weak-transform generators at every tree vertex `p` is
reduced. -/
theorem PointedMapGerm.exists_resolutionSectionAssembly_in_open₂
    (g : PointedMapGerm 2 3) (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative)
    (U U₃ : Set (Fin 3 → ℂ)) (hU : IsOpen U) (hne : U.Nonempty)
    (hU₃ : IsOpen U₃) (hne₃ : U₃.Nonempty) :
    ∃ A : ResolutionSectionAssembly g hd hi, A.coefficients ∈ U ∧ A.matrix 2 ∈ U₃ ∧
      ∀ p, Squarefree (germLinearCombination (A.tree.generators p) A.coefficients) := by
  obtain ⟨T, q, M, hq, hsq, hδ, hdet, hrow, hfin, hqU, hr, hred⟩ :=
    RawProjectiveWeakBlowupTree.exists_tree_section_coordinates_in_open g hi U U₃ hU hne hU₃ hne₃
  obtain ⟨B, hBT, hBq, hBM⟩ := ResolutionSectionAssembly.exists_of_tree_coordinates g hd hi
    T q M hq hsq hδ hdet hrow hfin
  subst hBT hBq hBM
  exact ⟨B, hqU, hr, hred⟩

/-- **Assembly with coefficients in a prescribed open set.** -/
theorem PointedMapGerm.exists_resolutionSectionAssembly_in_open
    (g : PointedMapGerm 2 3) (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative)
    (U : Set (Fin 3 → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ A : ResolutionSectionAssembly g hd hi, A.coefficients ∈ U := by
  obtain ⟨A, hA, -, -⟩ := g.exists_resolutionSectionAssembly_in_open₂ hd hi U Set.univ hU hne
    isOpen_univ Set.univ_nonempty
  exact ⟨A, hA⟩

end OnLeConjecture.Analytic
