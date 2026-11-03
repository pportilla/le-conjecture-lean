/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EResidueZeroCNineNoninjectivity
public import OnLeConjecture.DThree.EResidueZeroRotationLine

/-!
# Noninvariant E residue zero branch

The cubic rotation support alternative supplies either a rotation line
collision or the hard C9 decomposition. The corresponding weighted
persistence theorem excludes injectivity in each case.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A noninvariant homogeneous E form followed by a positive power
substitution is incompatible with an injective representative. -/
theorem eNoninvariantResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    {omega : ℂ} (a N : ℕ) (ha : 0 < a)
    (R : Form ℂ)
    (homega : IsPrimitiveRoot omega 3)
    (hR : R.IsHomogeneous N)
    (hnoninvariant : R ≠ eRotateForm omega R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (eResidueZeroDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  rcases e_noninvariant_rotationLineCollision_or_source_descent_add_pure_power
      homega hR hnoninvariant with hrotation |
      ⟨Rzero, coefficient, hcoefficient, hnotdiv, hdecomposition⟩
  · obtain ⟨data⟩ := hrotation
    exact
      eRotationLineResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a ha homega hR data representative hanalytic hzero htail
  · apply
      eCNineHardResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a ha homega Rzero coefficient N
    · rw [← hdecomposition]
      exact hR
    · exact hcoefficient
    · exact hnotdiv
    · intro i
      rw [← hdecomposition]
      exact htail i

end OnLeConjecture.DThree
