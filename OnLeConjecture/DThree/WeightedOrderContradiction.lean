/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.WeightedOrderExpansion
public import OnLeConjecture.DThree.WeightedResidueNoninjectivity

/-!
# The weighted order contradiction for the residual monomial maps

The two polynomial initial maps are written in the common polynomial
coordinate ring. Membership of every analytic correction in the next
weighted order ideal supplies the radial remainder and hence contradicts
local injectivity.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- The polynomial `E` residual initial map. -/
@[expose]
noncomputable def eResiduePolynomialMap
    (a M : ℕ) (c : ℂ) : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 ^ 3 +
      MvPolynomial.C 3 * MvPolynomial.X 1 ^ (3 * a),
    MvPolynomial.X 0 ^ 4 +
      MvPolynomial.C 4 *
        (MvPolynomial.X 0 * MvPolynomial.X 1 ^ (3 * a)),
    MvPolynomial.C c * MvPolynomial.X 1 ^ M]

/-- The polynomial `H` residual initial map. -/
@[expose]
noncomputable def hResiduePolynomialMap
    (a M : ℕ) (c : ℂ) : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 ^ 3 +
      MvPolynomial.C 3 *
        (MvPolynomial.X 0 * MvPolynomial.X 1 ^ (2 * a)),
    MvPolynomial.X 0 ^ 4 +
      MvPolynomial.C 4 *
        (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ (2 * a)) +
      MvPolynomial.C 2 * MvPolynomial.X 1 ^ (4 * a),
    MvPolynomial.C c * MvPolynomial.X 1 ^ M]

/-- The three coordinates of the `E` polynomial map have the required
weighted degrees. -/
theorem eResiduePolynomialMap_isWeightedHomogeneous
    (a M : ℕ) (c : ℂ) (i : Fin 3) :
    (eResiduePolynomialMap a M c i).IsWeightedHomogeneous ![a, 1]
      (residueWeightedDegrees a M i) := by
  have hx : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] a :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 0
  have hy : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
  fin_cases i
  · have hfirst :
        (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) ℂ)
          |>.IsWeightedHomogeneous ![a, 1] (3 * a) := by
      simpa [nsmul_eq_mul] using hx.pow 3
    have hsecond :
        (MvPolynomial.C 3 * MvPolynomial.X (1 : Fin 2) ^ (3 * a) :
          MvPolynomial (Fin 2) ℂ)
          |>.IsWeightedHomogeneous ![a, 1] (3 * a) := by
      simpa [nsmul_eq_mul] using (hy.pow (3 * a)).C_mul (3 : ℂ)
    simpa [eResiduePolynomialMap, residueWeightedDegrees] using
      hfirst.add hsecond
  · have hfirst :
        (MvPolynomial.X (0 : Fin 2) ^ 4 : MvPolynomial (Fin 2) ℂ)
          |>.IsWeightedHomogeneous ![a, 1] (4 * a) := by
      simpa [nsmul_eq_mul] using hx.pow 4
    have hsecond :
        (MvPolynomial.C 4 *
          (MvPolynomial.X (0 : Fin 2) *
            MvPolynomial.X (1 : Fin 2) ^ (3 * a)) :
          MvPolynomial (Fin 2) ℂ)
          |>.IsWeightedHomogeneous ![a, 1] (4 * a) := by
      have hraw := (hx.mul (hy.pow (3 * a))).C_mul (4 : ℂ)
      have hdegree : a + (3 * a) • 1 = 4 * a := by
        simp
        omega
      simpa only [hdegree] using hraw
    simpa [eResiduePolynomialMap, residueWeightedDegrees] using
      hfirst.add hsecond
  · simpa [eResiduePolynomialMap, residueWeightedDegrees] using
      (hy.pow M).C_mul c

/-- The three coordinates of the `H` polynomial map have the required
weighted degrees. -/
theorem hResiduePolynomialMap_isWeightedHomogeneous
    (a M : ℕ) (c : ℂ) (i : Fin 3) :
    (hResiduePolynomialMap a M c i).IsWeightedHomogeneous ![a, 1]
      (residueWeightedDegrees a M i) := by
  have hx : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] a :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 0
  have hy : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
  fin_cases i
  · have hfirst :
        (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) ℂ)
          |>.IsWeightedHomogeneous ![a, 1] (3 * a) := by
      simpa [nsmul_eq_mul] using hx.pow 3
    have hsecond :
        (MvPolynomial.C 3 *
          (MvPolynomial.X (0 : Fin 2) *
            MvPolynomial.X (1 : Fin 2) ^ (2 * a)) :
          MvPolynomial (Fin 2) ℂ)
          |>.IsWeightedHomogeneous ![a, 1] (3 * a) := by
      have hraw := (hx.mul (hy.pow (2 * a))).C_mul (3 : ℂ)
      have hdegree : a + (2 * a) • 1 = 3 * a := by
        simp
        omega
      simpa only [hdegree] using hraw
    simpa [hResiduePolynomialMap, residueWeightedDegrees] using
      hfirst.add hsecond
  · have hfirst :
        (MvPolynomial.X (0 : Fin 2) ^ 4 : MvPolynomial (Fin 2) ℂ)
          |>.IsWeightedHomogeneous ![a, 1] (4 * a) := by
      simpa [nsmul_eq_mul] using hx.pow 4
    have hsecond :
        (MvPolynomial.C 4 *
          (MvPolynomial.X (0 : Fin 2) ^ 2 *
            MvPolynomial.X (1 : Fin 2) ^ (2 * a)) :
          MvPolynomial (Fin 2) ℂ)
          |>.IsWeightedHomogeneous ![a, 1] (4 * a) := by
      have hraw := ((hx.pow 2).mul (hy.pow (2 * a))).C_mul (4 : ℂ)
      have hdegree : (2 • a) + (2 * a) • 1 = 4 * a := by
        simp
        omega
      simpa only [hdegree] using hraw
    have hthird :
        (MvPolynomial.C 2 * MvPolynomial.X (1 : Fin 2) ^ (4 * a) :
          MvPolynomial (Fin 2) ℂ)
          |>.IsWeightedHomogeneous ![a, 1] (4 * a) := by
      simpa [nsmul_eq_mul] using (hy.pow (4 * a)).C_mul (2 : ℂ)
    simpa [hResiduePolynomialMap, residueWeightedDegrees] using
      (hfirst.add hsecond).add hthird
  · simpa [hResiduePolynomialMap, residueWeightedDegrees] using
      (hy.pow M).C_mul c

/-- Polynomial evaluation recovers the `E` residual monomial map. -/
theorem weightedPolynomialMap_eResiduePolynomialMap
    (a M : ℕ) (c : ℂ) :
    weightedPolynomialMap (eResiduePolynomialMap a M c) =
      eResidueMonomialMap a M c := by
  funext z i
  fin_cases i
  · simp [weightedPolynomialMap, eResiduePolynomialMap,
      eResidueMonomialMap]
  · simp [weightedPolynomialMap, eResiduePolynomialMap,
      eResidueMonomialMap]
    ring
  · simp [weightedPolynomialMap, eResiduePolynomialMap,
      eResidueMonomialMap]

/-- Polynomial evaluation recovers the `H` residual monomial map. -/
theorem weightedPolynomialMap_hResiduePolynomialMap
    (a M : ℕ) (c : ℂ) :
    weightedPolynomialMap (hResiduePolynomialMap a M c) =
      hResidueMonomialMap a M c := by
  funext z i
  fin_cases i
  · simp [weightedPolynomialMap, hResiduePolynomialMap,
      hResidueMonomialMap]
    ring
  · simp [weightedPolynomialMap, hResiduePolynomialMap,
      hResidueMonomialMap]
    ring
  · simp [weightedPolynomialMap, hResiduePolynomialMap,
      hResidueMonomialMap]

/-- Corrections of weighted order greater than the `E` initial coordinates
exclude an injective representative. -/
theorem eWeightedOrderTails_not_hasInjectiveRepresentative
    (a M : ℕ) (c : ℂ) (ha : 0 < a) (hM : 0 < M) (hc : c ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eResiduePolynomialMap a M c i) ∈
        Germ.weightedOrderIdeal a
          (residueWeightedDegrees a M i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (residueWeightedDegrees a M) (eResiduePolynomialMap a M c)
        (eResiduePolynomialMap_isWeightedHomogeneous a M c)
          representative hanalytic htail
  apply eWeightedResidueCollision_not_hasInjectiveRepresentative
    a M c ha hM hc representative remainder hanalytic hzero
  · intro certificate
    simpa [weightedPolynomialMap_eResiduePolynomialMap] using
      hexpansion (certificate.firstCoordinate, 1)
  · intro certificate
    simpa [weightedPolynomialMap_eResiduePolynomialMap] using
      hexpansion (certificate.secondCoordinate, 1)

/-- Corrections of weighted order greater than the `H` initial coordinates
exclude an injective representative. -/
theorem hWeightedOrderTails_not_hasInjectiveRepresentative
    (a M : ℕ) (c : ℂ) (ha : 0 < a) (hM : 0 < M) (hc : c ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hResiduePolynomialMap a M c i) ∈
        Germ.weightedOrderIdeal a
          (residueWeightedDegrees a M i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (residueWeightedDegrees a M) (hResiduePolynomialMap a M c)
        (hResiduePolynomialMap_isWeightedHomogeneous a M c)
          representative hanalytic htail
  apply hWeightedResidueCollision_not_hasInjectiveRepresentative
    a M c ha hM hc representative remainder hanalytic hzero
  · intro certificate
    simpa [weightedPolynomialMap_hResiduePolynomialMap] using
      hexpansion (certificate.firstCoordinate, 1)
  · intro certificate
    simpa [weightedPolynomialMap_hResiduePolynomialMap] using
      hexpansion (certificate.secondCoordinate, 1)

/-- Coefficientwise weighted divisibility of the `E` corrections excludes an
injective representative. -/
theorem eWeightedCoefficientTails_not_hasInjectiveRepresentative
    (a M : ℕ) (c : ℂ) (ha : 0 < a) (hM : 0 < M) (hc : c ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      Germ.WeightedCoefficientDivisibility a
        (residueWeightedDegrees a M i + 1)
        (pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eResiduePolynomialMap a M c i))) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply eWeightedOrderTails_not_hasInjectiveRepresentative
    a M c ha hM hc representative hanalytic hzero
  intro i
  exact Germ.mem_weightedOrderIdeal_of_weightedCoefficientDivisibility
    a (residueWeightedDegrees a M i + 1) ha _ (htail i)

/-- Coefficientwise weighted divisibility of the `H` corrections excludes an
injective representative. -/
theorem hWeightedCoefficientTails_not_hasInjectiveRepresentative
    (a M : ℕ) (c : ℂ) (ha : 0 < a) (hM : 0 < M) (hc : c ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      Germ.WeightedCoefficientDivisibility a
        (residueWeightedDegrees a M i + 1)
        (pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hResiduePolynomialMap a M c i))) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply hWeightedOrderTails_not_hasInjectiveRepresentative
    a M c ha hM hc representative hanalytic hzero
  intro i
  exact Germ.mem_weightedOrderIdeal_of_weightedCoefficientDivisibility
    a (residueWeightedDegrees a M i + 1) ha _ (htail i)

end OnLeConjecture.DThree
