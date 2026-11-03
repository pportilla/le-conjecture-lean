/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EInvariantExceptionalPersistence
public import OnLeConjecture.DThree.EInvariantRegularNoninjectivity

/-!
# Noninjectivity from an exceptional invariant E collision

The exceptional persistence theorem supplies collisions of the original
representative converging to the origin.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- An exceptional invariant `E` collision excludes injectivity on every
neighborhood of the origin. -/
theorem not_neighborhood_injective_of_eWeightedInvariantExceptionalCollision
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n N : ℕ)
    (z s : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt 1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (s * z, 1))
    (hsecond : HasWeightedRadialExpansionAt 1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (s, 0))
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hW : eResidualW 1 z = 0) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  have hsNe : s ≠ 0 := eInvariant_chart_s_ne_zero hs
  have hdistinct : s * z ≠ s := by
    intro hequal
    apply hzOne
    apply mul_left_cancel₀ hsNe
    simpa using hequal
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_first
    1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (s * z) s 0 (by simp) hdistinct
          hfirst hsecond
  intro U hU
  exact eventually_exists_eWeightedInvariantExceptionalZero_mem_nhds
    Rzero R c n z s remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt hdescent hdecomposition hhomogeneous hp
        hzRoot hzOne hs hW U hU

/-- An exceptional invariant `E` collision excludes an injective
representative of the pointed map germ. -/
theorem eWeightedInvariantExceptionalCollision_not_hasInjectiveRepresentative
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n N : ℕ)
    (z s : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hfirst : HasWeightedRadialExpansionAt 1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (s * z, 1))
    (hsecond : HasWeightedRadialExpansionAt 1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (s, 0))
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hW : eResidualW 1 z = 0) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact
    not_neighborhood_injective_of_eWeightedInvariantExceptionalCollision
      Rzero R c n N z s representative remainder hfirst hsecond
        hdescent hdecomposition hhomogeneous hp hzRoot hzOne hs hW

/-- Weighted order tails exclude an injective representative at an
exceptional invariant residual root. -/
theorem eInvariantExceptionalWeightedOrderTails_not_hasInjectiveRepresentative
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n N : ℕ) (z : ℂ)
    (hR : R.IsHomogeneous N)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hThetaHomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hw : eResidualW z 1 ≠ 0)
    (hW : eResidualW 1 z = 0)
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
  obtain ⟨s, _, hs, _⟩ := exists_eInvariantRegularChartCoordinates z hw
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      1 (by simp) (eInvariantDegrees N) (eInvariantPolynomialMap R)
        (eInvariantPolynomialMap_isWeightedHomogeneous R N hR)
          representative hanalytic htail
  apply eWeightedInvariantExceptionalCollision_not_hasInjectiveRepresentative
    Rzero R c n N z s representative remainder hanalytic hzero
      (hexpansion (s * z, 1)) (hexpansion (s, 0)) hdescent
        hdecomposition hThetaHomogeneous hp hzRoot hzOne hs hW

end OnLeConjecture.DThree
