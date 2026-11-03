/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EInvariantRegularNoninjectivity

/-!
# The weighted order contradiction at a regular invariant E root

Membership of the analytic correction in the next ordinary order ideal
produces the radial expansions at the two points of a regular residual
collision.  Persistence then excludes an injective representative.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Corrections of order greater than the invariant initial coordinates
exclude an injective representative when the residual root has two nonzero
cube coordinates. -/
theorem eInvariantRegularWeightedOrderTails_not_hasInjectiveRepresentative
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n N : ℕ) (z : ℂ)
    (hR : R.IsHomogeneous N)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hThetaHomogeneous :
      EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hw : eResidualW z 1 ≠ 0)
    (hW : eResidualW 1 z ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eInvariantPolynomialMap R i) ∈
        Germ.weightedOrderIdeal 1 (eInvariantDegrees N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨s, g, hs, hg⟩ :=
    exists_eInvariantRegularChartCoordinates z hw
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      1 (by simp) (eInvariantDegrees N) (eInvariantPolynomialMap R)
        (eInvariantPolynomialMap_isWeightedHomogeneous R N hR)
          representative hanalytic htail
  apply eWeightedInvariantRegularCollision_not_hasInjectiveRepresentative
    Rzero R c n N z s g representative remainder hanalytic hzero
      (hexpansion (s * z, 1)) (hexpansion (s, g)) hdescent
        hdecomposition hThetaHomogeneous hp hzRoot hzOne hs hg hW

/-- Coefficient divisibility of the analytic correction gives the weighted
order hypothesis at a regular invariant residual root. -/
theorem
    eInvariantRegularWeightedCoefficientTails_not_hasInjectiveRepresentative
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n N : ℕ) (z : ℂ)
    (hR : R.IsHomogeneous N)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hThetaHomogeneous :
      EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hw : eResidualW z 1 ≠ 0)
    (hW : eResidualW 1 z ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      Germ.WeightedCoefficientDivisibility 1
        (eInvariantDegrees N i + 1)
        (pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eInvariantPolynomialMap R i))) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply eInvariantRegularWeightedOrderTails_not_hasInjectiveRepresentative
    Rzero R c n N z hR hdescent hdecomposition hThetaHomogeneous hp
      hzRoot hzOne hw hW representative hanalytic hzero
  intro i
  exact Germ.mem_weightedOrderIdeal_of_weightedCoefficientDivisibility
    1 (eInvariantDegrees N i + 1) (by simp) _ (htail i)

end OnLeConjecture.DThree
