/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HResidueZeroInvariantContradiction
public import OnLeConjecture.DThree.HResidueZeroNoninvariant

/-!
# H residue zero branch reduction

Reflection invariance and its negation exhaust the H residue zero case. The
invariant case uses conic descent and the noninvariant case uses reflection
support and the odd hard norm.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Every H residue zero form satisfying the conic base exclusion and the two
ordinary Jacobian divisibilities is incompatible with an injective
representative. -/
theorem hResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
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
  by_cases hinvariant : R = eRotateForm (-1) R
  · exact
      hInvariantResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a N ha hN R hR hinvariant hnotbase hPdiv hQdiv representative
          hanalytic hzero htail
  · exact
      hNoninvariantResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a N ha R hR hinvariant representative hanalytic hzero htail

end OnLeConjecture.DThree
