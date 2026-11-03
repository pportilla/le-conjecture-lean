/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddResidueZeroNoninjectivity
public import OnLeConjecture.DThree.HResidueZeroReflectionLine

/-!
# Noninvariant H residue zero branch

The reflection support alternative supplies either a reflection line
collision or an odd hard decomposition. The weighted residue zero persistence
theorems exclude injectivity in both cases.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A noninvariant homogeneous H form followed by a positive power
substitution is incompatible with an injective representative. -/
theorem hNoninvariantResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a)
    (R : Form ℂ)
    (hR : R.IsHomogeneous N)
    (hnoninvariant : R ≠ eRotateForm (-1) R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  rcases
      h_noninvariant_reflectionLineCollision_or_weighted_descent_add_odd_power
        hR hnoninvariant with hreflection |
      ⟨Rzero, coefficient, hcoefficient, hnotEven, hdecomposition⟩
  · obtain ⟨data⟩ := hreflection
    exact
      hReflectionLineResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a ha hR data representative hanalytic hzero htail
  · have hNodd : Odd N := by
      rwa [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact
      hHardOddResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a ha R Rzero coefficient N hR hdecomposition hNodd hcoefficient
          representative hanalytic hzero htail

end OnLeConjecture.DThree
