/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HomogenizedWeightedOrderContradiction
public import OnLeConjecture.DThree.WeightedOrderContradiction

/-!
# The positive residue branch in order three

When `0 < r < a`, the dehomogenized third form either has a complex root or
is constant. A root gives the rotation collision. A constant gives the pure
monomial collision. This dichotomy completes the weighted analytic exclusion
for the positive residue branch of both classified pairs.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- Homogenizing a constant polynomial gives the corresponding pure power. -/
theorem weightedHomogenizedPolynomial_C
    (a N : ℕ) (c : ℂ) :
    weightedHomogenizedPolynomial a N (C c) =
      MvPolynomial.C c * MvPolynomial.X 1 ^ (a * N) := by
  classical
  rw [weightedHomogenizedPolynomial, Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    rw [Polynomial.coeff_C_of_ne_zero hi0, map_zero, zero_mul, zero_mul]
  · simp

/-- The positive residue factor changes the homogenization of a constant
polynomial into the pure power of total weighted degree `r + a * N`. -/
theorem weightedThirdInitialPolynomial_C
    (a N r : ℕ) (c : ℂ) :
    weightedThirdInitialPolynomial a N r (C c) =
      MvPolynomial.C c * MvPolynomial.X 1 ^ (r + a * N) := by
  rw [weightedThirdInitialPolynomial, weightedHomogenizedPolynomial_C,
    pow_add]
  ring

/-- The homogenized `E` polynomial map of a constant chart polynomial is the
pure monomial map. -/
theorem eHomogenizedResiduePolynomialMap_C
    (a N r : ℕ) (c : ℂ) :
    eHomogenizedResiduePolynomialMap a N r (C c) =
      eResiduePolynomialMap a (r + a * N) c := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact weightedThirdInitialPolynomial_C a N r c

/-- The homogenized `H` polynomial map of a constant chart polynomial is the
pure monomial map. -/
theorem hHomogenizedResiduePolynomialMap_C
    (a N r : ℕ) (c : ℂ) :
    hHomogenizedResiduePolynomialMap a N r (C c) =
      hResiduePolynomialMap a (r + a * N) c := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact weightedThirdInitialPolynomial_C a N r c

/-- The degree tuples in the constant and pure monomial descriptions agree. -/
theorem homogenizedRotationDegrees_eq_residueWeightedDegrees
    (a N r : ℕ) :
    homogenizedRotationDegrees a N r =
      residueWeightedDegrees a (r + a * N) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl

/-- A complex polynomial has a root unless it is its constant coefficient. -/
theorem exists_root_or_eq_C (p : ℂ[X]) :
    (∃ x : ℂ, p.IsRoot x) ∨ p = C (p.coeff 0) := by
  by_cases hdegree : p.degree = 0
  · right
    exact p.eq_C_of_degree_eq_zero hdegree
  · left
    exact IsAlgClosed.exists_root p hdegree

/-- The positive residue branch for the `E` pair excludes an injective
representative under the next weighted order conditions. -/
theorem ePositiveResidueWeightedOrderTails_not_hasInjectiveRepresentative
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (ha : 2 ≤ a) (hr0 : 0 < r) (hra : r < a) (hp : p ≠ 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eHomogenizedResiduePolynomialMap a N r p i) ∈
        Germ.weightedOrderIdeal a
          (homogenizedRotationDegrees a N r i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  rcases exists_root_or_eq_C p with ⟨x, hx⟩ | hconstant
  · obtain ⟨zeta, hzetaA, hzetaR, _⟩ :=
      exists_root_of_unity_not_fixed a r ha hr0 hra
    exact eHomogenizedWeightedOrderTails_not_hasInjectiveRepresentative
      a N r p hdegree x zeta representative hanalytic hzero
        (by omega) hzetaA hzetaR hp hx htail
  · let c := p.coeff 0
    have hc : c ≠ 0 := by
      intro hc
      apply hp
      change p.coeff 0 = 0 at hc
      rw [hconstant, hc, map_zero]
    apply eWeightedOrderTails_not_hasInjectiveRepresentative
      a (r + a * N) c (by omega) (by omega) hc representative
        hanalytic hzero
    intro i
    rw [← homogenizedRotationDegrees_eq_residueWeightedDegrees,
      ← eHomogenizedResiduePolynomialMap_C]
    rw [← hconstant]
    exact htail i

/-- The positive residue branch for the `H` pair excludes an injective
representative under the next weighted order conditions. -/
theorem hPositiveResidueWeightedOrderTails_not_hasInjectiveRepresentative
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (ha : 2 ≤ a) (hr0 : 0 < r) (hra : r < a) (hp : p ≠ 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hHomogenizedResiduePolynomialMap a N r p i) ∈
        Germ.weightedOrderIdeal a
          (homogenizedRotationDegrees a N r i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  rcases exists_root_or_eq_C p with ⟨x, hx⟩ | hconstant
  · obtain ⟨zeta, hzetaA, hzetaR, _⟩ :=
      exists_root_of_unity_not_fixed a r ha hr0 hra
    exact hHomogenizedWeightedOrderTails_not_hasInjectiveRepresentative
      a N r p hdegree x zeta representative hanalytic hzero
        (by omega) hzetaA hzetaR hp hx htail
  · let c := p.coeff 0
    have hc : c ≠ 0 := by
      intro hc
      apply hp
      change p.coeff 0 = 0 at hc
      rw [hconstant, hc, map_zero]
    apply hWeightedOrderTails_not_hasInjectiveRepresentative
      a (r + a * N) c (by omega) (by omega) hc representative
        hanalytic hzero
    intro i
    rw [← homogenizedRotationDegrees_eq_residueWeightedDegrees,
      ← hHomogenizedResiduePolynomialMap_C]
    rw [← hconstant]
    exact htail i

/-- The coefficient divisibility conditions imply the positive residue
contradiction for the `E` pair. -/
theorem
    ePositiveResidueWeightedCoefficientTails_not_hasInjectiveRepresentative
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (ha : 2 ≤ a) (hr0 : 0 < r) (hra : r < a) (hp : p ≠ 0)
    (htail : ∀ i,
      Germ.WeightedCoefficientDivisibility a
        (homogenizedRotationDegrees a N r i + 1)
        (pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eHomogenizedResiduePolynomialMap a N r p i))) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply ePositiveResidueWeightedOrderTails_not_hasInjectiveRepresentative
    a N r p hdegree representative hanalytic hzero ha hr0 hra hp
  intro i
  exact Germ.mem_weightedOrderIdeal_of_weightedCoefficientDivisibility
    a (homogenizedRotationDegrees a N r i + 1) (by omega) _ (htail i)

/-- The coefficient divisibility conditions imply the positive residue
contradiction for the `H` pair. -/
theorem
    hPositiveResidueWeightedCoefficientTails_not_hasInjectiveRepresentative
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (ha : 2 ≤ a) (hr0 : 0 < r) (hra : r < a) (hp : p ≠ 0)
    (htail : ∀ i,
      Germ.WeightedCoefficientDivisibility a
        (homogenizedRotationDegrees a N r i + 1)
        (pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hHomogenizedResiduePolynomialMap a N r p i))) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply hPositiveResidueWeightedOrderTails_not_hasInjectiveRepresentative
    a N r p hdegree representative hanalytic hzero ha hr0 hra hp
  intro i
  exact Germ.mem_weightedOrderIdeal_of_weightedCoefficientDivisibility
    a (homogenizedRotationDegrees a N r i + 1) (by omega) _ (htail i)

end OnLeConjecture.DThree
