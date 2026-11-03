/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurvePreparedEquation
public import OnLeConjecture.Analytic.FinitePrincipalImage

/-!
# Representatives of irreducible analytic plane curves

Preparation of one nonconstant component and elimination of the parameter
give analytic equations for a curve image. The exact pullback kernel then
proves coverage of the full nearby zero set of the irreducible equation.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

open LocalComplexGeometry

/-- Extract the last coordinate as a point of the one dimensional source. -/
noncomputable def curveGraphSourceCLM (n : ℕ) : ComplexEuclidean (n + 1) →L[ℂ] Source 1 :=
  ContinuousLinearMap.pi fun _ => lastCoordinateCLM n

@[simp]
theorem curveGraphSourceCLM_appendLastCLE (n : ℕ) (z : Source n) (t : ℂ) :
    curveGraphSourceCLM n (appendLastCLE n (z, t)) = fun _ => t := by
  ext j
  exact lastCoordinateCLM_appendLastCLE n z t

/-- A nonconstant pointed analytic curve has a closed-ball image described
by finitely many analytic equations near the target origin. -/
theorem exists_curve_image_equations
    {m : ℕ} (G : Source 1 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hn : ∃ i, (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom (Germ.coordinate i) ≠ 0)
    (S : Set (Source 1)) (hS : S ∈ 𝓝 0) :
    ∃ (r : ℝ) (s : ℕ) (E : Fin s → Source m → ℂ),
      0 < r ∧ closedBall (0 : Source 1) r ⊆ S ∧
      AnalyticOnNhd ℂ G (closedBall 0 r) ∧
      (∀ k, AnalyticAt ℂ (E k) 0) ∧
      ∀ᶠ y in 𝓝 0,
        (∀ k, E k y = 0) ↔ ∃ x ∈ closedBall (0 : Source 1) r, G x = y := by
  obtain ⟨i, hi⟩ := hn
  obtain ⟨d, hd, a, ha, ha0, hcoord⟩ :=
    exists_curve_parameter_prepared_equation G hG hG0 i hi
  let H (j : Fin m) (z : ComplexEuclidean (m + 1)) :=
    G (curveGraphSourceCLM m z) j - dropLastCLM m z j
  have hH (j : Fin m) : AnalyticAt ℂ (H j) 0 := by
    have hcomp : AnalyticAt ℂ (fun z => G (curveGraphSourceCLM m z)) 0 := by
      apply hG.comp_of_eq ((curveGraphSourceCLM m).analyticAt 0)
      exact map_zero _
    exact (((ContinuousLinearMap.proj (R := ℂ) j).analyticAt _).comp hcomp).sub
      (((ContinuousLinearMap.proj (R := ℂ) j).comp (dropLastCLM m)).analyticAt 0)
  obtain ⟨E, hE, hprojection⟩ :=
    exists_analytic_equations_for_prepared_projection hd a ha ha0 H hH
  obtain ⟨r, hr, hrsub⟩ := nhds_basis_closedBall.mem_iff.mp
    (inter_mem hS (hG.eventually_analyticAt.and hcoord))
  let V := (curveGraphSourceCLM m) ⁻¹' closedBall (0 : Source 1) r
  have hV : V ∈ 𝓝 (0 : ComplexEuclidean (m + 1)) := by
    apply (curveGraphSourceCLM m).continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using closedBall_mem_nhds (0 : Source 1) hr
  refine ⟨r, d * m + 1, E, hr,
    fun x hx => (hrsub hx).1, fun x hx => (hrsub hx).2.1, hE, ?_⟩
  filter_upwards [hprojection V hV, hprojection Set.univ (Filter.univ_mem)] with y hyV hyAll
  constructor
  · intro hyE
    obtain ⟨t, ht, _, hzero⟩ := hyV.mp hyE
    refine ⟨fun _ => t, ?_, ?_⟩
    · simpa only [V, Set.mem_preimage, curveGraphSourceCLM_appendLastCLE] using ht
    · ext j
      simpa only [H, curveGraphSourceCLM_appendLastCLE,
        dropLastCLM_appendLastCLE, sub_eq_zero] using hzero j
  · rintro ⟨x, hx, rfl⟩
    apply hyAll.mpr
    refine ⟨x 0, Set.mem_univ _, (hrsub hx).2.2, ?_⟩
    intro j
    have hvec : (fun _ : Fin 1 => x 0) = x := by ext k; exact congrArg x (Subsingleton.elim _ _)
    simp only [H, curveGraphSourceCLM_appendLastCLE, hvec, dropLastCLM_appendLastCLE, sub_self]

/-- An injective nonconstant curve with the stated exact kernel covers the
entire nearby zero set of its equation. -/
theorem exists_curve_closedBall_image_eq_zero_set
    {m : ℕ} (G : Source 1 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hn : ∃ i, (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom (Germ.coordinate i) ≠ 0)
    (F : Source m → ℂ) (hF : AnalyticAt ℂ F 0)
    (hker : ∀ h, (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom h = 0 ↔
      Germ.ofFunction F hF ∣ h)
    (S : Set (Source 1)) (hS : S ∈ 𝓝 0) (hinj : InjOn G S) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : Source 1) r ⊆ S ∧
      AnalyticOnNhd ℂ G (closedBall 0 r) ∧
      (∀ x ∈ closedBall (0 : Source 1) r, G x = 0 → x = 0) ∧
      (∀ x ∈ closedBall (0 : Source 1) r, F (G x) = 0) ∧
      ∀ᶠ y in 𝓝 0,
        F y = 0 ↔ ∃ x ∈ closedBall (0 : Source 1) r, G x = y := by
  have hv := (hker (Germ.ofFunction F hF)).mpr dvd_rfl
  have hvanishevent : ∀ᶠ x in 𝓝 (0 : Source 1), F (G x) = 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun q : Germ 1 => q.1) hv)
  obtain ⟨r, s, E, hr, hrsub, hanalytic, hE, himage⟩ :=
    exists_curve_image_equations G hG hG0 hn (S ∩ {x | F (G x) = 0}) (inter_mem hS hvanishevent)
  have hGt : Tendsto G (𝓝 0) (𝓝 (0 : Source m)) := by
    simpa only [hG0] using hG.continuousAt.tendsto
  have hdiv (k : Fin s) : Germ.ofFunction F hF ∣ Germ.ofFunction (E k) (hE k) := by
    apply (hker _).mp
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hGt.eventually himage, closedBall_mem_nhds (0 : Source 1) hr] with x hx hxball
    exact (hx.mpr ⟨x, hxball, rfl⟩) k
  have htarget : ∀ᶠ y in 𝓝 (0 : Source m), ∀ k, F y = 0 → E k y = 0 :=
    Filter.eventually_all.mpr fun k =>
      Germ.eventually_zero_imp_zero_of_dvd F (E k) hF (hE k) (hdiv k)
  refine ⟨r, hr, fun x hx => (hrsub hx).1, hanalytic, ?_, fun x hx => (hrsub hx).2, ?_⟩
  · intro x hx hzero
    exact hinj (hrsub hx).1 (mem_of_mem_nhds hS) (hzero.trans hG0.symm)
  · filter_upwards [himage, htarget] with y hy hzeroes
    constructor
    · intro hyF
      exact hy.mp (fun k => hzeroes k hyF)
    · rintro ⟨x, hx, rfl⟩
      exact (hrsub hx).2

/-- Proper representative coverage of a principal curve zero set, with
arbitrarily prescribed injective source neighborhood. -/
theorem exists_proper_curve_representative_image_eq_zero_set
    {m : ℕ} (G : Source 1 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hn : ∃ i, (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom (Germ.coordinate i) ≠ 0)
    (F : Source m → ℂ) (hF : AnalyticAt ℂ F 0)
    (hker : ∀ h, (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom h = 0 ↔
      Germ.ofFunction F hF ∣ h)
    (S : Set (Source 1)) (hS : S ∈ 𝓝 0) (hinj : InjOn G S) :
    ∃ (U : Set (Source 1)) (V : Set (Source m)) (hUV : MapsTo G U V),
      IsOpen U ∧ 0 ∈ U ∧ U ⊆ S ∧ AnalyticOnNhd ℂ G U ∧
      IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ F V ∧
      IsProperMap (hUV.restrict G U V) ∧
      Topology.IsClosedEmbedding (hUV.restrict G U V) ∧
      G '' U = {y | y ∈ V ∧ F y = 0} := by
  obtain ⟨r, hr, hrS, hGK, hzero, hFG, himage⟩ :=
    exists_curve_closedBall_image_eq_zero_set G hG hG0 hn F hF hker S hS hinj
  obtain ⟨V₀, hV₀sub, hV₀, hV₀0⟩ := _root_.mem_nhds_iff.mp
    (himage.and hF.eventually_analyticAt)
  have hW0 : (0 : Source 1) ∈ ball 0 (r / 2) := mem_ball_self (by linarith)
  have hWK : ball (0 : Source 1) (r / 2) ⊆ interior (closedBall 0 r) := by
    intro x hx
    apply ball_subset_interior_closedBall
    exact ball_subset_ball (by linarith) hx
  obtain ⟨U, V, hUV, hU, hU0, hUW, hV, hV0, hVV₀, hconfine, hp⟩ :=
    exists_proper_restriction_of_compact_unique_fibre G
      (isCompact_closedBall (0 : Source 1) r) hGK.continuousOn
      isOpen_ball hW0 hWK hV₀ hV₀0 hG0 hzero
  have hUK : U ⊆ closedBall (0 : Source 1) r :=
    fun x hx => interior_subset (hWK (hUW hx))
  have hUS := hUK.trans hrS
  refine ⟨U, V, hUV, hU, hU0, hUS, hGK.mono hUK,
    hV, hV0, fun y hy => (hV₀sub (hVV₀ hy)).2, hp, ?_, ?_⟩
  · rw [Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap]
    refine ⟨hp.continuous, ?_, hp.isClosedMap⟩
    intro x y hxy
    apply Subtype.ext
    exact hinj (hUS x.property) (hUS y.property) (congrArg Subtype.val hxy)
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hUV hx, hFG x (hUK hx)⟩
    · rintro ⟨hyV, hyF⟩
      obtain ⟨x, hx, hxy⟩ := (hV₀sub (hVV₀ hyV)).1.mp hyF
      exact ⟨x, hconfine x hx (hxy ▸ hyV), hxy⟩

namespace Germ

/-- Every irreducible analytic plane equation has a proper injective
analytic parametrization onto its entire local zero set. Its differential
is nonzero at every nonzero parameter. -/
theorem exists_proper_immersed_parametrization_onto_zero_set
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (hirr : Irreducible (ofFunction F hF)) :
    ∃ (G : Source 1 → Source 2) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0),
      (∀ h : Germ 2, (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom h = 0 ↔
        ofFunction F hF ∣ h) ∧
      ∃ (U : Set (Source 1)) (V : Set (Source 2)) (hUV : MapsTo G U V),
        IsOpen U ∧ 0 ∈ U ∧ AnalyticOnNhd ℂ G U ∧
        IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ F V ∧
        IsProperMap (hUV.restrict G U V) ∧
        Topology.IsClosedEmbedding (hUV.restrict G U V) ∧
        G '' U = {y | y ∈ V ∧ F y = 0} ∧
        ∀ z ∈ U, z ≠ 0 → fderiv ℂ G z ≠ 0 := by
  obtain ⟨γ, hinj, hn, hker⟩ :=
    exists_injective_parametrization_with_kernel_of_irreducible (ofFunction F hF) hirr
  obtain ⟨G, hG, hG0, hγ, r, hr, _, hGin, _, hderiv⟩ :=
    hinj.exists_immersed_curve_representative hn F hF ((hker _).mpr dvd_rfl)
  rw [hγ] at hn hker
  obtain ⟨U, V, hUV, hU, hU0, hUS, hGU, hV, hV0, hFV, hp, hemb, himage⟩ :=
    exists_proper_curve_representative_image_eq_zero_set G hG hG0 hn F hF hker
      (closedBall 0 r) (closedBall_mem_nhds (0 : Source 1) hr) hGin
  exact ⟨G, hG, hG0, hker, U, V, hUV, hU, hU0, hGU, hV, hV0, hFV,
    hp, hemb, himage, fun z hz => hderiv z (hUS hz)⟩

end Germ

end OnLeConjecture.Analytic
