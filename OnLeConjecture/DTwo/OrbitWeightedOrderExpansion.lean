/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitCollision
public import OnLeConjecture.DThree.WeightedOrderExpansion

/-!
# Weighted order expansion for the quadratic orbit map

The quadratic orbit map has source weights `(1, 1)` and target degrees
`(2, 3, r)`. Membership of the three corrections in the next weighted order
ideals therefore produces one analytic radial remainder at every affine chart
point.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.DThree

/-- The target degrees of the quadratic orbit map. -/
@[expose]
def orbitInitialDegrees (r : ℕ) : Fin 3 → ℕ := ![2, 3, r]

/-- The three polynomial coordinates of the quadratic orbit map. -/
@[expose]
noncomputable def orbitInitialPolynomialMap
    (R : OrbitSourceForm) : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![orbitPolynomialPhi ℂ, orbitPolynomialPsi ℂ, R]

/-- Evaluation of the polynomial coordinates is the quadratic orbit map. -/
theorem weightedPolynomialMap_orbitInitialPolynomialMap
    (R : OrbitSourceForm) (z : ℂ × ℂ) :
    weightedPolynomialMap (orbitInitialPolynomialMap R) z =
      ![orbitPhi z.1 z.2, orbitPsi z.1 z.2,
        MvPolynomial.eval ![z.1, z.2] R] := by
  funext i
  fin_cases i <;>
    simp [weightedPolynomialMap, orbitInitialPolynomialMap,
      orbitPolynomialPhi, orbitPolynomialPsi, orbitPolynomialS,
      orbitPolynomialLambda, orbitPhi, orbitPsi]

/-- The three polynomial coordinates have degrees `(2, 3, r)` for source
weights `(1, 1)`. -/
theorem orbitInitialPolynomialMap_isWeightedHomogeneous
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (i : Fin 3) :
    (orbitInitialPolynomialMap R i).IsWeightedHomogeneous
      ![1, 1] (orbitInitialDegrees r i) := by
  have hweights : (![1, 1] : Fin 2 → ℕ) = 1 := by
    funext j
    fin_cases j <;> rfl
  change R.IsWeightedHomogeneous (1 : Fin 2 → ℕ) r at hR
  rw [hweights]
  fin_cases i
  · simpa [orbitInitialPolynomialMap, orbitInitialDegrees] using
      (orbitPolynomialPhi_isHomogeneous (K := ℂ))
  · simpa [orbitInitialPolynomialMap, orbitInitialDegrees] using
      (orbitPolynomialPsi_isHomogeneous (K := ℂ))
  · simpa [orbitInitialPolynomialMap, orbitInitialDegrees] using hR

/-- Corrections of order greater than the three homogeneous coordinates
produce one radial expansion at every affine chart point. -/
theorem exists_orbitWeightedRadialExpansion
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (orbitInitialPolynomialMap R i) ∈
        Germ.weightedOrderIdeal 1 (orbitInitialDegrees r i + 1)) :
    ∃ remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ,
      ∀ z : ℂ × ℂ,
        HasWeightedRadialExpansionAt 1 (orbitInitialDegrees r)
          (weightedPolynomialMap (orbitInitialPolynomialMap R))
            representative remainder z := by
  exact exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
    1 (by norm_num) (orbitInitialDegrees r) (orbitInitialPolynomialMap R)
      (orbitInitialPolynomialMap_isWeightedHomogeneous hR)
        representative hanalytic htail

/-- Coefficientwise ordinary order divisibility gives the same radial
expansion. -/
theorem exists_orbitWeightedRadialExpansion_of_coefficientDivisibility
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (htail : ∀ i,
      Germ.WeightedCoefficientDivisibility 1
        (orbitInitialDegrees r i + 1)
        (pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (orbitInitialPolynomialMap R i))) :
    ∃ remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ,
      ∀ z : ℂ × ℂ,
        HasWeightedRadialExpansionAt 1 (orbitInitialDegrees r)
          (weightedPolynomialMap (orbitInitialPolynomialMap R))
            representative remainder z := by
  apply exists_orbitWeightedRadialExpansion hR representative hanalytic
  intro i
  exact Germ.mem_weightedOrderIdeal_of_weightedCoefficientDivisibility
    1 (orbitInitialDegrees r i + 1) (by norm_num) _ (htail i)

end OnLeConjecture.DTwo
