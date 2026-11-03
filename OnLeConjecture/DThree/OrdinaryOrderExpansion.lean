/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrdinaryWeightedOrder
public import OnLeConjecture.DThree.EInvariantBranchReduction

/-!
# Radial expansion from ordinary initial forms

For source weights `(1,1)`, ordinary order in the maximal ideal filtration is
the finite monomial order used by the radial collision argument. This file
connects ordinary homogeneous initial forms to the invariant `E` exclusion.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Ordinary correction order supplies the radial remainder for three
homogeneous initial forms. -/
theorem exists_hasOrdinaryRadialExpansionAt_of_mem_maximalIdeal_pow
    (degrees : Fin 3 → ℕ)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![1, 1] (degrees i))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hrepresentative i -
          Germ.coordinatePolynomialAlgHom 2 (P i) ∈
        Germ.maximalIdeal 2 ^ (degrees i + 1)) :
    ∃ remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ,
      ∀ z : ℂ × ℂ,
        HasWeightedRadialExpansionAt 1 degrees
          (weightedPolynomialMap P) representative remainder z := by
  apply exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
    1 (by simp) degrees P hP representative hrepresentative
  intro i
  rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal_pow]
  exact htail i

/-- In the invariant `E` branch, ordinary correction terms of order strictly
greater than their initial degrees exclude an injective representative. -/
theorem eInvariantMaximalIdealTails_not_hasInjectiveRepresentative
    {omega : ℂ} (R : Form ℂ) (N : ℕ)
    (homega : IsPrimitiveRoot omega 3)
    (hR : R.IsHomogeneous N)
    (hinvariant : R = eRotateForm omega R)
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
  apply eInvariantWeightedOrderTails_not_hasInjectiveRepresentative
    R N homega hR hinvariant hdiv hnotbase representative hanalytic hzero
  intro i
  rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal_pow]
  exact htail i

end OnLeConjecture.DThree
