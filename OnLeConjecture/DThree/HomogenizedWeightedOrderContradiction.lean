/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HomogenizedResiduePolynomialMap
public import OnLeConjecture.DThree.HomogenizedResidueRotationNoninjectivity

/-!
# The weighted order contradiction for the homogenized rotation maps

Membership of each analytic correction in the next weighted order ideal
produces the radial expansions at the two rotation chart points. The
homogenized rotation collision then excludes an injective representative.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- Corrections of weighted order greater than the homogenized `E` initial
coordinates exclude an injective representative. -/
theorem eHomogenizedWeightedOrderTails_not_hasInjectiveRepresentative
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eHomogenizedResiduePolynomialMap a N r p i) ∈
        Germ.weightedOrderIdeal a
          (homogenizedRotationDegrees a N r i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (homogenizedRotationDegrees a N r)
        (eHomogenizedResiduePolynomialMap a N r p)
          (eHomogenizedResiduePolynomialMap_isWeightedHomogeneous a N r p)
            representative hanalytic htail
  apply eHomogenizedWeightedRotationCollision_not_hasInjectiveRepresentative
    a N r p hdegree x zeta representative remainder hanalytic hzero
  · simpa only [weightedPolynomialMap_eHomogenizedResiduePolynomialMap] using
      hexpansion (x, 1)
  · simpa only [weightedPolynomialMap_eHomogenizedResiduePolynomialMap] using
      hexpansion (x, zeta)
  · exact ha
  · exact hzetaA
  · exact hzetaR
  · exact hp
  · exact hx

/-- Corrections of weighted order greater than the homogenized `H` initial
coordinates exclude an injective representative. -/
theorem hHomogenizedWeightedOrderTails_not_hasInjectiveRepresentative
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hHomogenizedResiduePolynomialMap a N r p i) ∈
        Germ.weightedOrderIdeal a
          (homogenizedRotationDegrees a N r i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (homogenizedRotationDegrees a N r)
        (hHomogenizedResiduePolynomialMap a N r p)
          (hHomogenizedResiduePolynomialMap_isWeightedHomogeneous a N r p)
            representative hanalytic htail
  apply hHomogenizedWeightedRotationCollision_not_hasInjectiveRepresentative
    a N r p hdegree x zeta representative remainder hanalytic hzero
  · simpa only [weightedPolynomialMap_hHomogenizedResiduePolynomialMap] using
      hexpansion (x, 1)
  · simpa only [weightedPolynomialMap_hHomogenizedResiduePolynomialMap] using
      hexpansion (x, zeta)
  · exact ha
  · exact hzetaA
  · exact hzetaR
  · exact hp
  · exact hx

/-- Coefficientwise weighted divisibility of the homogenized `E` corrections
excludes an injective representative. -/
theorem eHomogenizedWeightedCoefficientTails_not_hasInjectiveRepresentative
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x)
    (htail : ∀ i,
      Germ.WeightedCoefficientDivisibility a
        (homogenizedRotationDegrees a N r i + 1)
        (pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eHomogenizedResiduePolynomialMap a N r p i))) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply eHomogenizedWeightedOrderTails_not_hasInjectiveRepresentative
    a N r p hdegree x zeta representative hanalytic hzero
      ha hzetaA hzetaR hp hx
  intro i
  exact Germ.mem_weightedOrderIdeal_of_weightedCoefficientDivisibility
    a (homogenizedRotationDegrees a N r i + 1) ha _ (htail i)

/-- Coefficientwise weighted divisibility of the homogenized `H` corrections
excludes an injective representative. -/
theorem hHomogenizedWeightedCoefficientTails_not_hasInjectiveRepresentative
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x)
    (htail : ∀ i,
      Germ.WeightedCoefficientDivisibility a
        (homogenizedRotationDegrees a N r i + 1)
        (pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hHomogenizedResiduePolynomialMap a N r p i))) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply hHomogenizedWeightedOrderTails_not_hasInjectiveRepresentative
    a N r p hdegree x zeta representative hanalytic hzero
      ha hzetaA hzetaR hp hx
  intro i
  exact Germ.mem_weightedOrderIdeal_of_weightedCoefficientDivisibility
    a (homogenizedRotationDegrees a N r i + 1) ha _ (htail i)

end OnLeConjecture.DThree
