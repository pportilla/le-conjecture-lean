/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EResidueZeroBranchReduction
public import OnLeConjecture.DThree.HResidueZeroBranchReduction

/-!
# Pointed map interfaces for residue zero

The E and H residue zero contradictions are transferred from analytic pair
representatives to component statements for pointed map germs.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- The normalized E residue zero component tails exclude an injective
representative. -/
theorem eResidueZeroPointedMap_not_hasInjectiveRepresentative
    {omega : ℂ} (g : PointedMapGerm 2 3)
    (a N : ℕ) (ha : 0 < a)
    (R : Form ℂ)
    (homega : IsPrimitiveRoot omega 3)
    (hR : R.IsHomogeneous N)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R)
    (hnotbase : ∀ Rzero : ESourceRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (eBaseToSource ℂ))
    (htail : ∀ i,
      g.1.component i - Germ.coordinatePolynomialAlgHom 2
          (eResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (eResidueZeroDegrees a N i + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨representative, hanalytic, hzero, hg, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components g
  rw [hg]
  apply eResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha R homega hR hdiv hnotbase representative hanalytic hzero
  intro i
  rw [hcomponents i]
  exact htail i

/-- The normalized H residue zero component tails exclude an injective
representative. -/
theorem hResidueZeroPointedMap_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3)
    (a N : ℕ) (ha : 0 < a) (hN : 5 ≤ N)
    (R : Form ℂ) (hR : R.IsHomogeneous N)
    (hnotbase : ∀ Rzero : Form ℂ,
      hQuadraticSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (hBaseToWeightedForm ℂ))
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 3 0) R)
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) R)
    (htail : ∀ i,
      g.1.component i - Germ.coordinatePolynomialAlgHom 2
          (hResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨representative, hanalytic, hzero, hg, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components g
  rw [hg]
  apply hResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha hN R hR hnotbase hPdiv hQdiv representative hanalytic hzero
  intro i
  rw [hcomponents i]
  exact htail i

end OnLeConjecture.DThree
