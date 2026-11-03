/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IrreducibleCurveParametrization
public import OnLeConjecture.Analytic.Injectivity
public import OnLeConjecture.Analytic.CoordinateAxesFactorization
public import OnLeConjecture.Analytic.OneVariableDerivativeOrder
public import OnLeConjecture.Analytic.ReducedMemberCriticalIntersection

/-!
# Injective parametrizations along a finite resolution chain

A nonzero analytic germ in one variable has an isolated zero. Consequently,
blowing down an injectively parametrized curve preserves local injectivity
when its exceptional coordinate is nonzero as a germ. The finite smooth
resolution chain then constructs a locally injective pointed parametrization
annihilating each irreducible plane equation.
-/

public section

namespace OnLeConjecture.Analytic

open Filter OnLeConjecture.Analytic.Germ
open scoped Topology

namespace Germ

/-- A nonconstant pointed analytic scalar function of one variable has
nonzero derivative at every sufficiently small nonzero parameter. -/
theorem eventually_derivative_ne_zero_of_nonzero_pointed_germ
    (f : Source 1 → ℂ) (hf : AnalyticAt ℂ f 0) (hfzero : f 0 = 0)
    (hne : ofFunction f hf ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : Source 1), z ≠ 0 →
      fderiv ℂ f z (coordinateVector (0 : Fin 1)) ≠ 0 := by
  have hmem : ofFunction f hf ∈ maximalIdeal 1 := hfzero
  have hderivne := (derivative_ne_zero_and_order_add_one (ofFunction f hf) hmem hne).1
  let df : Source 1 → ℂ := fun z => fderiv ℂ f z (coordinateVector (0 : Fin 1))
  have hdf : AnalyticAt ℂ df 0 :=
    ((ContinuousLinearMap.apply ℂ ℂ (coordinateVector (0 : Fin 1))).analyticAt
      (fderiv ℂ f 0)).comp hf.fderiv
  have hdfne : ofFunction df hdf ≠ 0 := hderivne
  filter_upwards [eventually_zero_imp_eq_zero_of_oneVariable_ne_zero df hdf hdfne]
    with z hz hzne hdz
  exact hzne (hz hdz)

/-- The coordinate hyperplane inclusion is injective on every neighborhood. -/
theorem hyperplaneInclusionGerm_hasInjectiveRepresentative (n : ℕ) :
    (hyperplaneInclusionGerm n).HasInjectiveRepresentative := by
  refine ⟨hyperplaneInclusion n, (hyperplaneInclusion n).analyticAt 0,
    map_zero _, rfl, Set.univ, Filter.univ_mem, ?_⟩
  intro x _ y _ heq
  ext i
  exact congrArg (fun z : Source (n + 1) => z i.succ) heq

end Germ

namespace PointedMapGerm

/-- A blowdown is locally injective along an injective curve whose
exceptional coordinate does not vanish identically. -/
theorem HasInjectiveRepresentative.pointBlowupChart_comp
    {γ : PointedMapGerm 1 2} (hγ : γ.HasInjectiveRepresentative)
    (hy : γ.pullbackRingHom (coordinate (1 : Fin 2)) ≠ 0) (c : ℂ) :
    ((pointBlowupChartGerm c).comp γ).HasInjectiveRepresentative := by
  obtain ⟨G, hG, hG0, rfl, s, hs, hGinj⟩ := hγ
  have hGy : AnalyticAt ℂ (fun z => G z 1) 0 :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt (G 0)).comp hG
  have hGyne : Germ.ofFunction (fun z => G z 1) hGy ≠ 0 := by
    rw [pullback_coordinate] at hy
    exact hy
  have hzero := eventually_zero_imp_eq_zero_of_oneVariable_ne_zero _ hGy hGyne
  let t : Set (Source 1) := {z | G z 1 = 0 → z = 0}
  have ht : t ∈ 𝓝 (0 : Source 1) := hzero
  have hchart : AnalyticAt ℂ (pointBlowupChart c) (G 0) := by
    rw [hG0]
    exact pointBlowupChart_analyticAt c
  rw [pointBlowupChartGerm, comp_ofFunction]
  refine ⟨pointBlowupChart c ∘ G,
    hchart.comp hG,
    (by simp [hG0]), rfl, s ∩ t, inter_mem hs ht, ?_⟩
  intro x hx y hy hxy
  have hsecond : G x 1 = G y 1 := by
    simpa [pointBlowupChart] using congrArg (fun z : Source 2 => z 1) hxy
  by_cases hxzero : G x 1 = 0
  · exact (hx.2 hxzero).trans (hy.2 (hsecond.symm.trans hxzero)).symm
  · apply hGinj hx.1 hy.1
    have hfirst : G x 1 * (G x 0 + c) = G y 1 * (G y 0 + c) := by
      simpa [pointBlowupChart] using congrArg (fun z : Source 2 => z 0) hxy
    rw [← hsecond] at hfirst
    have hfirstcoord : G x 0 = G y 0 :=
      add_right_cancel (mul_left_cancel₀ hxzero hfirst)
    ext i
    fin_cases i
    · exact hfirstcoord
    · exact hsecond

/-- A nonconstant locally injective curve has an analytic representative
on a closed parameter ball which lies in the prescribed equation and has
nonzero differential away from the origin. -/
theorem HasInjectiveRepresentative.exists_immersed_curve_representative
    {γ : PointedMapGerm 1 2} (hinj : γ.HasInjectiveRepresentative)
    (hnonconstant : ∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0)
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (hvanish : γ.pullbackRingHom (Germ.ofFunction F hF) = 0) :
    ∃ (G : Source 1 → Source 2) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0),
      γ = ofFunction G hG hG0 ∧
      ∃ r : ℝ, 0 < r ∧
        AnalyticOnNhd ℂ G (Metric.closedBall 0 r) ∧
        Set.InjOn G (Metric.closedBall 0 r) ∧
        (∀ z ∈ Metric.closedBall 0 r, F (G z) = 0) ∧
        ∀ z ∈ Metric.closedBall 0 r, z ≠ 0 → fderiv ℂ G z ≠ 0 := by
  obtain ⟨G, hG, hG0, rfl, s, hs, hGinj⟩ := hinj
  obtain ⟨i, hi⟩ := hnonconstant
  have hGi : AnalyticAt ℂ (fun z => G z i) 0 :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i).analyticAt (G 0)).comp hG
  have hGine : Germ.ofFunction (fun z => G z i) hGi ≠ 0 := by
    rw [pullback_coordinate] at hi
    exact hi
  have hGizero : G 0 i = 0 := by rw [hG0]; rfl
  have hderiv := eventually_derivative_ne_zero_of_nonzero_pointed_germ _ hGi hGizero hGine
  have hvanishevent : ∀ᶠ z in 𝓝 (0 : Source 1), F (G z) = 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun q : Germ 1 => q.1) hvanish)
  have hproperties : ∀ᶠ z in 𝓝 (0 : Source 1),
      AnalyticAt ℂ G z ∧ z ∈ s ∧ F (G z) = 0 ∧
        (z ≠ 0 → fderiv ℂ (fun w => G w i) z (coordinateVector (0 : Fin 1)) ≠ 0) := by
    filter_upwards [hG.eventually_analyticAt, hs, hvanishevent, hderiv] with z hz hs hzF hdz
    exact ⟨hz, hs, hzF, hdz⟩
  obtain ⟨r, hr, hrproperties⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hproperties
  refine ⟨G, hG, hG0, rfl, r, hr, (fun z hz => (hrproperties hz).1),
    hGinj.mono (fun z hz => (hrproperties hz).2.1),
    (fun z hz => (hrproperties hz).2.2.1), ?_⟩
  intro z hz hzne hzero
  apply (hrproperties hz).2.2.2 hzne
  have hcomp := fderiv_comp z
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i).differentiableAt
    (hrproperties hz).1.differentiableAt
  rw [ContinuousLinearMap.fderiv, hzero] at hcomp
  exact congrArg (fun L : Source 1 →L[ℂ] ℂ => L (coordinateVector (0 : Fin 1))) hcomp

end PointedMapGerm

namespace Germ

/-- A smooth plane equation admits a nonconstant, locally injective pointed
parametrization. -/
theorem exists_injective_parametrization_of_smooth
    (f : Germ 2) (hf : f ∈ maximalIdeal 2) (hn : f ∉ maximalIdeal 2 ^ 2) :
    ∃ γ : PointedMapGerm 1 2, γ.pullbackRingHom f = 0 ∧
      (∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0) ∧
      γ.HasInjectiveRepresentative := by
  obtain ⟨e, he⟩ := PlaneCurve.exists_equiv_pullback_eq_coordinate f hf
    (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf hn).1
  refine ⟨e.forward.comp (hyperplaneInclusionGerm 1), ?_, ?_,
    PointedMapGerm.comp_hasInjectiveRepresentative _ _
      e.forward_hasInjectiveRepresentative (hyperplaneInclusionGerm_hasInjectiveRepresentative 1)⟩
  · rw [PointedMapGerm.pullbackRingHom_comp]
    change hyperplaneRestriction 1 (e.pullbackAlgEquiv f) = 0
    rw [he, hyperplaneRestriction_coordinate_zero]
  · apply PointedMapGerm.exists_nonzero_coordinate_pullback_comp_equiv
    refine ⟨1, ?_⟩
    change hyperplaneRestriction 1 (coordinate (1 : Fin 2)) ≠ 0
    simpa only [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
      hyperplaneRestriction_coordinate_succ] using coordinate_zero_ne_zero

/-- Local injectivity is preserved through every coordinate change and
blowdown in a finite smooth-resolution chain. -/
theorem HasFiniteSmoothBlowupChain.exists_injective_parametrization
    {f : Germ 2} (h : HasFiniteSmoothBlowupChain f) :
    ∃ γ : PointedMapGerm 1 2, γ.pullbackRingHom f = 0 ∧
      (∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0) ∧
      γ.HasInjectiveRepresentative := by
  induction h with
  | smooth f hf hn => exact exists_injective_parametrization_of_smooth f hf hn
  | source f e _ ih =>
    obtain ⟨γ, hγ, hnonconstant, hinj⟩ := ih
    refine ⟨e.forward.comp γ, ?_,
      γ.exists_nonzero_coordinate_pullback_comp_equiv hnonconstant e,
      PointedMapGerm.comp_hasInjectiveRepresentative _ _ e.forward_hasInjectiveRepresentative hinj⟩
    rw [PointedMapGerm.pullbackRingHom_comp]
    exact hγ
  | blowup f m _ ho hn c _ ih =>
    obtain ⟨γ, hγ, hnonconstant, hinj⟩ := ih
    have hy : γ.pullbackRingHom (coordinate (1 : Fin 2)) ≠ 0 := by
      intro hz
      have hall := γ.coordinate_pullbacks_eq_zero_of_finite_pair _ _
        (finite_intersection_exceptional_pointBlowupTransform c m f ho hn) hz hγ
      obtain ⟨i, hi⟩ := hnonconstant
      exact hi (hall i)
    refine ⟨(pointBlowupChartGerm c).comp γ, ?_, ⟨1, ?_⟩,
      hinj.pointBlowupChart_comp hy c⟩
    · rw [PointedMapGerm.pullbackRingHom_comp]
      change γ.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom f) = 0
      rw [pointBlowupTransform_factor c m f ho, map_mul, hγ, mul_zero]
    · rw [PointedMapGerm.pullbackRingHom_comp]
      change γ.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom (coordinate 1)) ≠ 0
      rwa [pointBlowupChartGerm_pullback_one]

/-- Every irreducible plane analytic equation admits a nonconstant pointed
parametrization with an injective representative near the origin. -/
theorem exists_injective_parametrization_of_irreducible
    (f : Germ 2) (hf : Irreducible f) :
    ∃ γ : PointedMapGerm 1 2, γ.pullbackRingHom f = 0 ∧
      (∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0) ∧
      γ.HasInjectiveRepresentative :=
  (hasFiniteSmoothBlowupChain_of_irreducible f hf).exists_injective_parametrization

/-- The locally injective parametrization detects exactly the principal
ideal of the irreducible equation. -/
theorem exists_injective_parametrization_with_kernel_of_irreducible
    (f : Germ 2) (hf : Irreducible f) :
    ∃ γ : PointedMapGerm 1 2, γ.HasInjectiveRepresentative ∧
      (∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0) ∧
      ∀ h : Germ 2, γ.pullbackRingHom h = 0 ↔ f ∣ h := by
  obtain ⟨γ, hγf, hγ, hinj⟩ := exists_injective_parametrization_of_irreducible f hf
  exact ⟨γ, hinj, hγ, parametrization_pullback_eq_zero_iff_dvd f hf γ hγf hγ⟩

/-- Ideal form of the exact kernel statement for a nonconstant
parametrization of an irreducible plane equation. -/
theorem parametrization_kernel_eq_span_singleton
    (f : Germ 2) (hf : Irreducible f) (γ : PointedMapGerm 1 2)
    (hγf : γ.pullbackRingHom f = 0)
    (hγ : ∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0) :
    RingHom.ker γ.pullbackRingHom = Ideal.span {f} := by
  ext h
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact parametrization_pullback_eq_zero_iff_dvd f hf γ hγf hγ h

/-- An irreducible analytic plane equation admits an injective analytic
representative on a closed parameter ball, with nonzero differential at
every nonzero parameter and image contained in its zero set. -/
theorem exists_injective_immersed_parametrization_representative_of_irreducible
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (hirr : Irreducible (ofFunction F hF)) :
    ∃ (G : Source 1 → Source 2) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0),
      (∀ h : Germ 2, (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom h = 0 ↔
        ofFunction F hF ∣ h) ∧
      ∃ r : ℝ, 0 < r ∧
        AnalyticOnNhd ℂ G (Metric.closedBall 0 r) ∧
        Set.InjOn G (Metric.closedBall 0 r) ∧
        (∀ z ∈ Metric.closedBall 0 r, F (G z) = 0) ∧
        ∀ z ∈ Metric.closedBall 0 r, z ≠ 0 → fderiv ℂ G z ≠ 0 := by
  obtain ⟨γ, hinj, hnonconstant, hker⟩ :=
    exists_injective_parametrization_with_kernel_of_irreducible (ofFunction F hF) hirr
  obtain ⟨G, hG, hG0, hγ, r, hr, han, hinj, hzero, hderiv⟩ :=
    hinj.exists_immersed_curve_representative hnonconstant F hF ((hker _).mpr dvd_rfl)
  exact ⟨G, hG, hG0, hγ ▸ hker, r, hr, han, hinj, hzero, hderiv⟩

end Germ

end OnLeConjecture.Analytic
