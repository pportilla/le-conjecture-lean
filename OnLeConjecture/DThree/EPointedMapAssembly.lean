/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EAllBranchesAnalyticInterface
public import OnLeConjecture.DThree.PairRepresentativeComponents

/-!
# The normalized E case for pointed map germs

The analytic collision theorem for the three classified E branches is stated
for a representative on the coordinate product. This file applies it to a
pointed plane map germ whose component germs have the prescribed initial
forms.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A pointed plane map germ with the normalized E initial forms cannot have
an injective representative under the Jacobian and base exclusion
hypotheses. -/
theorem eNormalizedPointedMap_not_hasInjectiveRepresentative
    {omega : ℂ} (g : PointedMapGerm 2 3) (R : Form ℂ) (N : ℕ)
    (homega : IsPrimitiveRoot omega 3)
    (hR : R.IsHomogeneous N)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R)
    (hnotbase : ∀ Rzero : ESourceRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (eBaseToSource ℂ))
    (htail : ∀ i,
      g.1.component i - Germ.coordinatePolynomialAlgHom 2
          (eInvariantPolynomialMap R i) ∈
        Germ.maximalIdeal 2 ^ (eInvariantDegrees N i + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨representative, hanalytic, hzero, hg, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components g
  rw [hg]
  apply eAllBranchesMaximalIdealTails_not_hasInjectiveRepresentative
    R N homega hR hdiv hnotbase representative hanalytic hzero
  intro i
  rw [hcomponents i]
  exact htail i

end OnLeConjecture.DThree
