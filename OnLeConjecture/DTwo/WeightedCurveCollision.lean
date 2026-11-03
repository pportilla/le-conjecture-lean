/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.PairCurveCollisionPersistence
public import OnLeConjecture.DThree.PairRepresentativeComponents

/-!
# Weighted collisions along analytic pair curves

A finite-order third difference along a curve of the initial plane fibre
persists for the analytic weighted tails. The first point need not be
regular for the plane map. Only the derivative at the eliminated second
point is required to be invertible.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic DThree

theorem analyticAt_weightedPolynomialMap_at
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ) (point : ℂ × ℂ) :
    AnalyticAt ℂ (weightedPolynomialMap P) point := by
  rw [analyticAt_pi_iff]
  intro i
  have hcoordinate (j : Fin 2) : AnalyticAt ℂ
      (fun z : ℂ × ℂ => (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z j) point :=
    (((ContinuousLinearMap.proj (R := ℂ) j).comp
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm.toContinuousLinearMap).analyticAt point)
  simpa [weightedPolynomialMap, MvPolynomial.aeval_def] using
    AnalyticAt.aeval_mvPolynomial hcoordinate (P i)

theorem weighted_curve_orderTails_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a : ℕ) (ha : 0 < a)
    (degrees : Fin 3 → ℕ) (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![a, 1] (degrees i))
    (htail : ∀ i, g.1.component i - Germ.coordinatePolynomialAlgHom 2 (P i) ∈
      Germ.weightedOrderIdeal a (degrees i + 1))
    (first : ℂ → ℂ × ℂ) (second : ℂ → Fin 2 → ℂ)
    (hfirst : AnalyticAt ℂ first 0) (hsecond : AnalyticAt ℂ second 0)
    (hseparate : first 0 ≠ orbitPointOfFinTwo (second 0))
    (m : ℕ) (u : ℂ → ℂ) (hm : 0 < m) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hcurve : ∀ᶠ s in nhds 0,
      weightedPolynomialMap P (first s) -
        weightedPolynomialMap P (orbitPointOfFinTwo (second s)) = ![0, 0, s ^ m * u s])
    (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ))
    (hD : HasStrictFDerivAt (fun q : Fin 2 → ℂ =>
      ![weightedPolynomialMap P (first 0) 0 - weightedPolynomialMap P (orbitPointOfFinTwo q) 0,
        weightedPolynomialMap P (first 0) 1 - weightedPolynomialMap P (orbitPointOfFinTwo q) 1])
      D (second 0)) (hDinvertible : D.IsInvertible) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨representative, hanalytic, hzero, heq, hcomponents⟩ :=
    OnLeConjecture.DThree.PointedMapGerm.exists_pairRepresentative_with_components g
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal a ha degrees P hP
      representative hanalytic (fun i => by rw [hcomponents i]; exact htail i)
  let initial := weightedPolynomialMap P
  let pair := (first 0, orbitPointOfFinTwo (second 0))
  let Phi := orbitPairRescaledPerturbation initial remainder
  have hPhi : AnalyticAt ℂ Phi (0, pair) := by
    apply analyticAt_orbitPairRescaledPerturbation
    · exact analyticAt_weightedPolynomialMap_at P _
    · exact analyticAt_weightedPolynomialMap_at P _
    · exact (hexpansion _).remainder_analyticAt
    · exact (hexpansion _).remainder_analyticAt
  let modelPlane : ℂ × (Fin 2 → ℂ) → Fin 2 → ℂ := fun s =>
    ![initial (first s.1) 0 - initial (orbitPointOfFinTwo s.2) 0,
      initial (first s.1) 1 - initial (orbitPointOfFinTwo s.2) 1]
  let modelThird : ℂ × (Fin 2 → ℂ) → ℂ := fun s =>
    initial (first s.1) 2 - initial (orbitPointOfFinTwo s.2) 2
  have hspecialPlane (s : ℂ) (q : Fin 2 → ℂ) :
      pairCurvePlanePart Phi first ((0, s), q) = modelPlane (s, q) := by
    ext i
    fin_cases i <;> simp [pairCurvePlanePart, pairCurveReparametrization, Phi,
      orbitPairInitialDifference, modelPlane]
  have hspecialThird (s : ℂ) (q : Fin 2 → ℂ) :
      pairCurveThirdPart Phi first ((0, s), q) = modelThird (s, q) := by
    simp [pairCurveThirdPart, pairCurveReparametrization, Phi,
      orbitPairInitialDifference, modelThird]
  have hmodelZero : ∀ᶠ s in nhds 0, modelPlane (s, second s) = 0 := by
    filter_upwards [hcurve] with s hs
    ext i
    fin_cases i
    · exact congrFun hs 0
    · exact congrFun hs 1
  have hfactor : ∀ᶠ s in nhds 0, modelThird (s, second s) = s ^ m * u s := by
    filter_upwards [hcurve] with s hs
    exact congrFun hs 2
  rw [heq]
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_weightedPairRescaledZeros a ha degrees initial
    representative remainder pair hseparate (hexpansion _) (hexpansion _)
  exact eventually_exists_pairCurve_collisionZero_mem_nhds Phi first second (second 0)
    hfirst hsecond rfl hPhi modelPlane hspecialPlane D hD hDinvertible hmodelZero
    modelThird hspecialThird m u hm hu hu0 hfactor

end OnLeConjecture.DTwo
