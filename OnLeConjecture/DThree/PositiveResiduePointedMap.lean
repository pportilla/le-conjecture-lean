/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.PairRepresentativeComponents
public import OnLeConjecture.DThree.PositiveResidueContradiction
public import OnLeConjecture.DThree.WeightedResidueChartPolynomial

/-!
# Positive residue contradiction for pointed map germs

The residue decomposition supplies the chart polynomial and its degree bound.
The existing collision theorem can therefore be applied directly to a pointed
map germ with the normalized E or H initial pair.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A normalized E initial pair and a nonzero weighted third form with
positive residue exclude an injective representative. -/
theorem ePositiveResiduePointedMap_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a)
    (R : Form ℂ) (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hRzero : R ≠ 0) (hresidue : 0 < D % a)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a 0 3) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a 1 0 0 4 0) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨p, hpdegree, hpzero, hrepresentation⟩ :=
    exists_nonzero_weightedResidueChartPolynomial a D ha R hR hRzero
  have haTwo : 2 ≤ a := by
    have hresidueLt : D % a < a := Nat.mod_lt D ha
    omega
  obtain ⟨representative, hanalytic, hzero, hg, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components g
  rw [hg]
  apply ePositiveResidueWeightedOrderTails_not_hasInjectiveRepresentative
    a (D / a) (D % a) p hpdegree representative hanalytic hzero
      haTwo hresidue (Nat.mod_lt D ha) hpzero
  intro i
  rw [hcomponents i]
  fin_cases i
  · change g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
        (eHomogenizedResiduePolynomialMap
          a (D / a) (D % a) p 0) ∈
      Germ.weightedOrderIdeal a
        (homogenizedRotationDegrees a (D / a) (D % a) 0 + 1)
    have hpolynomial :
        eHomogenizedResiduePolynomialMap
            a (D / a) (D % a) p 0 =
          weightedCubicPolynomial a 0 3 := by
        simp [eHomogenizedResiduePolynomialMap, weightedCubicPolynomial]
    rw [hpolynomial]
    exact htailZero
  · change g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
        (eHomogenizedResiduePolynomialMap
          a (D / a) (D % a) p 1) ∈
      Germ.weightedOrderIdeal a
        (homogenizedRotationDegrees a (D / a) (D % a) 1 + 1)
    have hpolynomial :
        eHomogenizedResiduePolynomialMap
            a (D / a) (D % a) p 1 =
          weightedQuarticPolynomial a 1 0 0 4 0 := by
        simp [eHomogenizedResiduePolynomialMap, weightedQuarticPolynomial]
        ring
    rw [hpolynomial]
    exact htailOne
  · change g.1.component 2 - Germ.coordinatePolynomialAlgHom 2
        (eHomogenizedResiduePolynomialMap
          a (D / a) (D % a) p 2) ∈
      Germ.weightedOrderIdeal a
        (homogenizedRotationDegrees a (D / a) (D % a) 2 + 1)
    have hpolynomial :
        eHomogenizedResiduePolynomialMap
            a (D / a) (D % a) p 2 = R := by
        simpa [eHomogenizedResiduePolynomialMap] using hrepresentation.symm
    have hdegree :
        homogenizedRotationDegrees a (D / a) (D % a) 2 = D := by
      change D % a + a * (D / a) = D
      exact (weightedDegree_eq_residue_add_mul_quotient a D).symm
    rw [hpolynomial, hdegree]
    exact htailTwo

/-- A normalized H initial pair and a nonzero weighted third form with
positive residue exclude an injective representative. -/
theorem hPositiveResiduePointedMap_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a)
    (R : Form ℂ) (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hRzero : R ≠ 0) (hresidue : 0 < D % a)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a 3 0) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a 1 0 4 0 2) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨p, hpdegree, hpzero, hrepresentation⟩ :=
    exists_nonzero_weightedResidueChartPolynomial a D ha R hR hRzero
  have haTwo : 2 ≤ a := by
    have hresidueLt : D % a < a := Nat.mod_lt D ha
    omega
  obtain ⟨representative, hanalytic, hzero, hg, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components g
  rw [hg]
  apply hPositiveResidueWeightedOrderTails_not_hasInjectiveRepresentative
    a (D / a) (D % a) p hpdegree representative hanalytic hzero
      haTwo hresidue (Nat.mod_lt D ha) hpzero
  intro i
  rw [hcomponents i]
  fin_cases i
  · change g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
        (hHomogenizedResiduePolynomialMap
          a (D / a) (D % a) p 0) ∈
      Germ.weightedOrderIdeal a
        (homogenizedRotationDegrees a (D / a) (D % a) 0 + 1)
    have hpolynomial :
        hHomogenizedResiduePolynomialMap
            a (D / a) (D % a) p 0 =
          weightedCubicPolynomial a 3 0 := by
        simp [hHomogenizedResiduePolynomialMap, weightedCubicPolynomial]
        ring
    rw [hpolynomial]
    exact htailZero
  · change g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
        (hHomogenizedResiduePolynomialMap
          a (D / a) (D % a) p 1) ∈
      Germ.weightedOrderIdeal a
        (homogenizedRotationDegrees a (D / a) (D % a) 1 + 1)
    have hpolynomial :
        hHomogenizedResiduePolynomialMap
            a (D / a) (D % a) p 1 =
          weightedQuarticPolynomial a 1 0 4 0 2 := by
        simp [hHomogenizedResiduePolynomialMap, weightedQuarticPolynomial]
        ring
    rw [hpolynomial]
    exact htailOne
  · change g.1.component 2 - Germ.coordinatePolynomialAlgHom 2
        (hHomogenizedResiduePolynomialMap
          a (D / a) (D % a) p 2) ∈
      Germ.weightedOrderIdeal a
        (homogenizedRotationDegrees a (D / a) (D % a) 2 + 1)
    have hpolynomial :
        hHomogenizedResiduePolynomialMap
            a (D / a) (D % a) p 2 = R := by
        simpa [hHomogenizedResiduePolynomialMap] using hrepresentation.symm
    have hdegree :
        homogenizedRotationDegrees a (D / a) (D % a) 2 = D := by
      change D % a + a * (D / a) = D
      exact (weightedDegree_eq_residue_add_mul_quotient a D).symm
    rw [hpolynomial, hdegree]
    exact htailTwo

end OnLeConjecture.DThree
