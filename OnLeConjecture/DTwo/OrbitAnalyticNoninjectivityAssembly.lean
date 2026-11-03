/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitAnalyticImageNoninjectivity
public import OnLeConjecture.DTwo.OrbitNoninjectivity
public import OnLeConjecture.Analytic.AnalyticCoordinateEndomorphism

/-!
# Analytic assembly of the quadratic orbit contradiction

The analytic normalization produces a polynomial correction in the first two
target coordinates and a first homogeneous residual outside the orbit
subring. Subtracting that correction from the third coordinate preserves
local injectivity. The residual map then satisfies the tail hypotheses of the
quadratic orbit collision theorem.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.DThree

/-- The projection from three target coordinates onto the first two. -/
@[expose]
noncomputable def orbitPlaneProjectionFunction
    (z : Source 3) : Source 2 := ![z 0, z 1]

theorem orbitPlaneProjectionFunction_analyticAt :
    AnalyticAt ℂ orbitPlaneProjectionFunction 0 := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt
      (0 : Source 3)
  · exact (ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt
      (0 : Source 3)

theorem orbitPlaneProjectionFunction_zero :
    orbitPlaneProjectionFunction 0 = 0 := by
  funext i
  fin_cases i
  · rfl
  · rfl

/-- The pointed analytic germ defined by the first two target coordinates. -/
@[expose]
noncomputable def orbitPlaneProjection : PointedMapGerm 3 2 :=
  PointedMapGerm.ofFunction orbitPlaneProjectionFunction
    orbitPlaneProjectionFunction_analyticAt
    orbitPlaneProjectionFunction_zero

@[simp]
theorem orbitPlaneProjection_component_zero :
    orbitPlaneProjection.1.component 0 = Germ.coordinate (0 : Fin 3) := by
  apply Subtype.ext
  rw [show orbitPlaneProjection.1.component 0 =
      (MapGerm.ofFunction orbitPlaneProjectionFunction
        orbitPlaneProjectionFunction_analyticAt).component 0 by rfl,
    MapGerm.component_ofFunction]
  rfl

@[simp]
theorem orbitPlaneProjection_component_one :
    orbitPlaneProjection.1.component 1 = Germ.coordinate (1 : Fin 3) := by
  apply Subtype.ext
  rw [show orbitPlaneProjection.1.component 1 =
      (MapGerm.ofFunction orbitPlaneProjectionFunction
        orbitPlaneProjectionFunction_analyticAt).component 1 by rfl,
    MapGerm.component_ofFunction]
  rfl

/-- Projection recovers a plane germ when the first two components agree. -/
theorem orbitPlaneProjection_comp_eq
    (F : PointedMapGerm 2 3) (g : PointedMapGerm 2 2)
    (hcomponentZero : F.1.component 0 = g.1.component 0)
    (hcomponentOne : F.1.component 1 = g.1.component 1) :
    orbitPlaneProjection.comp F = g := by
  apply PointedMapGerm.ext_components
  intro i
  fin_cases i
  · rw [PointedMapGerm.component_comp_general]
    change F.pullbackRingHom (orbitPlaneProjection.1.component 0) =
      g.1.component 0
    rw [orbitPlaneProjection_component_zero, F.pullback_coordinate,
      hcomponentZero]
  · rw [PointedMapGerm.component_comp_general]
    change F.pullbackRingHom (orbitPlaneProjection.1.component 1) =
      g.1.component 1
    rw [orbitPlaneProjection_component_one, F.pullback_coordinate,
      hcomponentOne]

/-- A polynomial in the first two coordinates, regarded as a germ on the
three dimensional target. -/
@[expose]
noncomputable def orbitThreeCoordinateCorrection
    (Q : OrbitBaseRing ℂ) : Germ 3 :=
  orbitPlaneProjection.pullbackRingHom (orbitTargetPolynomialAlgHom Q)

/-- Pullback of the three coordinate correction is evaluation at the first
two components. -/
theorem pullback_orbitThreeCoordinateCorrection
    (F : PointedMapGerm 2 3) (g : PointedMapGerm 2 2)
    (hcomponentZero : F.1.component 0 = g.1.component 0)
    (hcomponentOne : F.1.component 1 = g.1.component 1)
    (Q : OrbitBaseRing ℂ) :
    F.pullbackRingHom (orbitThreeCoordinateCorrection Q) =
      orbitAnalyticEvaluationAlgHom g Q := by
  rw [orbitThreeCoordinateCorrection,
    ← RingHom.comp_apply,
    ← PointedMapGerm.pullbackRingHom_comp,
    orbitPlaneProjection_comp_eq F g hcomponentZero hcomponentOne,
    orbitAnalyticEvaluationAlgHom_eq_pullback]

private theorem coordinatePolynomial_mem_maximalIdeal_of_isHomogeneous
    {P : MvPolynomial (Fin 2) ℂ} {r : ℕ}
    (hP : P.IsHomogeneous r) (hr : 1 ≤ r) :
    Germ.coordinatePolynomialAlgHom 2 P ∈ Germ.maximalIdeal 2 := by
  rw [← pow_one (Germ.maximalIdeal 2)]
  apply Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mp
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro d hd
  exact hP.coeff_eq_zero (by omega)

private theorem orbitCorrection_mem_maximalIdeal_of_initialForm
    (F : PointedMapGerm 2 3) (g : PointedMapGerm 2 2)
    {Q : OrbitBaseRing ℂ} {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r) (hr : 1 ≤ r)
    (hinitial :
      (F.1.component 2 - orbitAnalyticEvaluationAlgHom g Q) -
          Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.maximalIdeal 2 ^ (r + 1)) :
    orbitAnalyticEvaluationAlgHom g Q ∈ Germ.maximalIdeal 2 := by
  have htail :
      (F.1.component 2 - orbitAnalyticEvaluationAlgHom g Q) -
          Germ.coordinatePolynomialAlgHom 2 R ∈ Germ.maximalIdeal 2 := by
    exact Ideal.pow_le_self (by omega) hinitial
  have hpolynomial :
      Germ.coordinatePolynomialAlgHom 2 R ∈ Germ.maximalIdeal 2 :=
    coordinatePolynomial_mem_maximalIdeal_of_isHomogeneous hR hr
  have hresidual :
      F.1.component 2 - orbitAnalyticEvaluationAlgHom g Q ∈
        Germ.maximalIdeal 2 := by
    have hsum := (Germ.maximalIdeal 2).add_mem htail hpolynomial
    convert hsum using 1
    ring
  have hcomponent : F.1.component 2 ∈ Germ.maximalIdeal 2 :=
    F.coordinateIdeal_le_maximalIdeal
      (MapGerm.component_mem_coordinateIdeal F.1 2)
  have hdifference := (Germ.maximalIdeal 2).sub_mem hcomponent hresidual
  convert hdifference using 1
  ring

private theorem orbitTargetCorrection_mem_maximalIdeal
    (g : PointedMapGerm 2 2) (Q : OrbitBaseRing ℂ)
    (hcorrection : orbitAnalyticEvaluationAlgHom g Q ∈
      Germ.maximalIdeal 2) :
    orbitTargetPolynomialAlgHom Q ∈ Germ.maximalIdeal 2 := by
  rw [Germ.mem_maximalIdeal_iff] at hcorrection ⊢
  rw [orbitAnalyticEvaluationAlgHom_eq_pullback,
    PointedMapGerm.valueRingHom_pullback] at hcorrection
  exact hcorrection

/-- A first homogeneous residual outside the orbit subring contradicts local
injectivity of the original three coordinate germ. -/
theorem orbitNonbaseInitialForm_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3) (g : PointedMapGerm 2 2)
    (hcomponentZero : F.1.component 0 = g.1.component 0)
    (hcomponentOne : F.1.component 1 = g.1.component 1)
    (hphi : g.1.component 0 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hpsi : g.1.component 1 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      Germ.maximalIdeal 2 ^ 4)
    {Q : OrbitBaseRing ℂ} {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r) (hr : 4 ≤ r)
    (hdivides : orbitPolynomialLambda ℂ ^ 4 ∣ R)
    (hnotBase : R ∉ Set.range (orbitBaseToSource ℂ))
    (hinitial :
      (F.1.component 2 - orbitAnalyticEvaluationAlgHom g Q) -
          Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.maximalIdeal 2 ^ (r + 1)) :
    ¬ F.HasInjectiveRepresentative := by
  intro hinjective
  have hcorrection := orbitCorrection_mem_maximalIdeal_of_initialForm
    F g hR (by omega) hinitial
  have htargetCorrection := orbitTargetCorrection_mem_maximalIdeal
    g Q hcorrection
  have hthreeCorrection : orbitThreeCoordinateCorrection Q ∈
      Germ.maximalIdeal 3 := by
    exact orbitPlaneProjection.pullback_mem_maximalIdeal htargetCorrection
  let residualComponents : Fin 3 → Germ 2 := ![
    F.1.component 0,
    F.1.component 1,
    F.1.component 2 - orbitAnalyticEvaluationAlgHom g Q]
  have hresidualComponents : ∀ i,
      residualComponents i ∈ Germ.maximalIdeal 2 := by
    intro i
    fin_cases i
    · exact F.coordinateIdeal_le_maximalIdeal
        (MapGerm.component_mem_coordinateIdeal F.1 0)
    · exact F.coordinateIdeal_le_maximalIdeal
        (MapGerm.component_mem_coordinateIdeal F.1 1)
    · exact (Germ.maximalIdeal 2).sub_mem
        (F.coordinateIdeal_le_maximalIdeal
          (MapGerm.component_mem_coordinateIdeal F.1 2)) hcorrection
  obtain ⟨H, hH⟩ := PointedMapGerm.exists_with_components
    residualComponents hresidualComponents
  let inverseComponents : Fin 3 → Germ 3 := ![
    Germ.coordinate (0 : Fin 3),
    Germ.coordinate (1 : Fin 3),
    Germ.coordinate (2 : Fin 3) + orbitThreeCoordinateCorrection Q]
  have hinverseComponents : ∀ i,
      inverseComponents i ∈ Germ.maximalIdeal 3 := by
    intro i
    fin_cases i
    · exact Germ.coordinate_mem_maximalIdeal 0
    · exact Germ.coordinate_mem_maximalIdeal 1
    · exact (Germ.maximalIdeal 3).add_mem
        (Germ.coordinate_mem_maximalIdeal 2) hthreeCorrection
  obtain ⟨inverse, hinverse⟩ := PointedMapGerm.exists_with_components
    inverseComponents hinverseComponents
  have hprojectionH : orbitPlaneProjection.comp H = g := by
    apply orbitPlaneProjection_comp_eq
    · rw [hH]
      exact hcomponentZero
    · rw [hH]
      exact hcomponentOne
  have hpullbackCorrection :
      H.pullbackRingHom (orbitThreeCoordinateCorrection Q) =
        orbitAnalyticEvaluationAlgHom g Q := by
    rw [orbitThreeCoordinateCorrection,
      ← RingHom.comp_apply,
      ← PointedMapGerm.pullbackRingHom_comp,
      hprojectionH,
      orbitAnalyticEvaluationAlgHom_eq_pullback]
  have hinverseComp : inverse.comp H = F := by
    apply PointedMapGerm.ext_components
    intro i
    fin_cases i
    · rw [PointedMapGerm.component_comp_general]
      change H.pullbackRingHom (inverse.1.component 0) = F.1.component 0
      rw [hinverse]
      change H.pullbackRingHom (Germ.coordinate (0 : Fin 3)) =
        F.1.component 0
      rw [H.pullback_coordinate, hH]
      rfl
    · rw [PointedMapGerm.component_comp_general]
      change H.pullbackRingHom (inverse.1.component 1) = F.1.component 1
      rw [hinverse]
      change H.pullbackRingHom (Germ.coordinate (1 : Fin 3)) =
        F.1.component 1
      rw [H.pullback_coordinate, hH]
      rfl
    · rw [PointedMapGerm.component_comp_general]
      change H.pullbackRingHom (inverse.1.component 2) = F.1.component 2
      rw [hinverse]
      change H.pullbackRingHom
        (Germ.coordinate (2 : Fin 3) + orbitThreeCoordinateCorrection Q) =
          F.1.component 2
      rw [map_add, H.pullback_coordinate, hpullbackCorrection, hH]
      simp [residualComponents]
  have hHInjective : H.HasInjectiveRepresentative := by
    apply PointedMapGerm.hasInjectiveRepresentative_of_comp inverse H
    rw [hinverseComp]
    exact hinjective
  obtain ⟨representative, hanalytic, hzero, hrepresentative,
      hcomponents⟩ :=
    OnLeConjecture.DThree.PointedMapGerm.exists_pairRepresentative_with_components H
  have htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (orbitInitialPolynomialMap R i) ∈
        Germ.weightedOrderIdeal 1 (orbitInitialDegrees r i + 1) := by
    intro i
    rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal_pow]
    fin_cases i
    · rw [hcomponents, hH]
      simpa [residualComponents, orbitInitialPolynomialMap,
        orbitInitialDegrees, hcomponentZero] using hphi
    · rw [hcomponents, hH]
      simpa [residualComponents, orbitInitialPolynomialMap,
        orbitInitialDegrees, hcomponentOne] using hpsi
    · rw [hcomponents, hH]
      simpa [residualComponents, orbitInitialPolynomialMap,
        orbitInitialDegrees] using hinitial
  have hnoninjective :=
    orbitHomogeneousWeightedOrderTails_not_hasInjectiveRepresentative
      hR hr hdivides hnotBase representative hanalytic hzero htail
  apply hnoninjective
  rw [← hrepresentative]
  exact hHInjective

/-- The analytic normalization dichotomy and the orbit collision theorem
exclude the normalized squarefree quadratic branch under the two minor
divisibilities. -/
theorem orbitNormalizedPointedMap_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3) (g : PointedMapGerm 2 2)
    (hfinite : g.IsFiniteAtOrigin)
    (hcomponentZero : F.1.component 0 = g.1.component 0)
    (hcomponentOne : F.1.component 1 = g.1.component 1)
    (hphi : g.1.component 0 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hpsi : g.1.component 1 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      Germ.maximalIdeal 2 ^ 4)
    (horder : F.1.component 2 ∈ Germ.maximalIdeal 2 ^ 4)
    (hminorTwelve : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hminorThirteen : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0) (F.1.component 2)) :
    ¬ F.HasInjectiveRepresentative := by
  intro hinjective
  obtain ⟨k, Q, R, _hprevious, _hnonremovable, hR, _hRne,
      hdivides, hnotBase, hinitial⟩ :=
    orbitFirstNonbaseLambdaFourInitialForm_of_injective_minors
      F g hfinite hcomponentZero hcomponentOne hphi hpsi horder
        hminorTwelve hminorThirteen hinjective
  exact orbitNonbaseInitialForm_not_hasInjectiveRepresentative
    F g hcomponentZero hcomponentOne hphi hpsi hR (by omega)
      hdivides hnotBase (by
        simpa only [show 4 + k + 1 = 5 + k by omega] using hinitial)
      hinjective

end OnLeConjecture.DTwo
