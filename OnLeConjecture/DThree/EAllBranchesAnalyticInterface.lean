/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineAnalyticPersistence
public import OnLeConjecture.DThree.ERotationLineNoninjectivity
public import OnLeConjecture.DThree.OrdinaryOrderExpansion

/-!
# The three branches of the normalized E case

The rotation invariant branch, the rotation line branch, and the remaining
degree nine branch all contradict local injectivity under the same ordinary
tail conditions.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Every homogeneous third form in the normalized `E` case excludes an
injective representative under the Jacobian, base exclusion, and ordinary
tail hypotheses. -/
theorem eAllBranchesMaximalIdealTails_not_hasInjectiveRepresentative
    {omega : ℂ} (R : Form ℂ) (N : ℕ)
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
            (eInvariantPolynomialMap R i) ∈
        Germ.maximalIdeal 2 ^ (eInvariantDegrees N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  by_cases hinvariant : R = eRotateForm omega R
  · exact eInvariantMaximalIdealTails_not_hasInjectiveRepresentative
      R N homega hR hinvariant hdiv hnotbase representative hanalytic
        hzero htail
  · rcases e_noninvariant_rotationLineCollision_or_source_descent_add_pure_power
      homega hR hinvariant with hline | hhard
    · obtain ⟨data⟩ := hline
      exact eRotationLineMaximalIdealTails_not_hasInjectiveRepresentative
        homega hR data representative hanalytic hzero htail
    · obtain ⟨Rzero, coefficient, hcoefficient, hnotdiv, hform⟩ := hhard
      have hhardHomogeneous :
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N).IsHomogeneous N := by
        rw [← hform]
        exact hR
      apply eCNineHardMaximalIdealTails_not_hasInjectiveRepresentative
        homega Rzero coefficient N hhardHomogeneous hcoefficient hnotdiv
          representative hanalytic hzero
      intro i
      rw [← hform]
      exact htail i

end OnLeConjecture.DThree
