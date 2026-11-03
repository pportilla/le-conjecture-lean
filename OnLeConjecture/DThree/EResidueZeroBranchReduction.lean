/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EResidueZeroInvariantBranchReduction
public import OnLeConjecture.DThree.EResidueZeroNoninvariant

/-!
# E residue zero branch reduction

Cubic rotation invariance and its negation exhaust the E residue zero case.
The invariant case uses residual theta descent and the noninvariant case uses
the rotation line and C9 alternatives.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Every E residue zero form satisfying the base exclusion and ordinary
Jacobian divisibility is incompatible with an injective representative. -/
theorem eResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    {omega : ℂ} (a N : ℕ) (ha : 0 < a)
    (R : Form ℂ)
    (homega : IsPrimitiveRoot omega 3)
    (hR : R.IsHomogeneous N)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R)
    (hnotbase : ∀ Rzero : ESourceRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (eBaseToSource ℂ))
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
  by_cases hinvariant : R = eRotateForm omega R
  · exact
      eInvariantResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a N ha R homega hR hinvariant hdiv hnotbase representative
          hanalytic hzero htail
  · exact
      eNoninvariantResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a N ha R homega hR hinvariant representative hanalytic hzero htail

end OnLeConjecture.DThree
