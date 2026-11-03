/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HomogenizedResidueRotation
public import OnLeConjecture.DThree.WeightedOrderExpansion
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Polynomial coordinates for the homogenized rotation maps

The third coordinate is represented by a two variable polynomial obtained
from the dehomogenized polynomial `p`. Evaluation recovers the complete
homogenized rotation maps, and every coordinate has its stated weighted
degree.
-/

public section

open scoped BigOperators

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The polynomial `H(x, y ^ a)` associated with a dehomogenized polynomial
of degree at most `N`. -/
@[expose]
noncomputable def weightedHomogenizedPolynomial
    (a N : ℕ) (p : ℂ[X]) : MvPolynomial (Fin 2) ℂ :=
  ∑ i ∈ Finset.range (N + 1),
    MvPolynomial.C (p.coeff i) * MvPolynomial.X 0 ^ i *
      MvPolynomial.X 1 ^ (a * (N - i))

/-- The polynomial `y ^ r * H(x, y ^ a)`. -/
@[expose]
noncomputable def weightedThirdInitialPolynomial
    (a N r : ℕ) (p : ℂ[X]) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X 1 ^ r * weightedHomogenizedPolynomial a N p

/-- Polynomial coordinates of the homogenized `E` rotation map. -/
@[expose]
noncomputable def eHomogenizedResiduePolynomialMap
    (a N r : ℕ) (p : ℂ[X]) : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 ^ 3 +
      MvPolynomial.C 3 * MvPolynomial.X 1 ^ (3 * a),
    MvPolynomial.X 0 ^ 4 +
      MvPolynomial.C 4 *
        (MvPolynomial.X 0 * MvPolynomial.X 1 ^ (3 * a)),
    weightedThirdInitialPolynomial a N r p]

/-- Polynomial coordinates of the homogenized `H` rotation map. -/
@[expose]
noncomputable def hHomogenizedResiduePolynomialMap
    (a N r : ℕ) (p : ℂ[X]) : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 ^ 3 +
      MvPolynomial.C 3 *
        (MvPolynomial.X 0 * MvPolynomial.X 1 ^ (2 * a)),
    MvPolynomial.X 0 ^ 4 +
      MvPolynomial.C 4 *
        (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ (2 * a)) +
      MvPolynomial.C 2 * MvPolynomial.X 1 ^ (4 * a),
    weightedThirdInitialPolynomial a N r p]

theorem weightedHomogenizedPolynomial_isWeightedHomogeneous
    (a N : ℕ) (p : ℂ[X]) :
    (weightedHomogenizedPolynomial a N p).IsWeightedHomogeneous
      ![a, 1] (a * N) := by
  have hx : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] a :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 0
  have hy : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
  rw [weightedHomogenizedPolynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i hi
  have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hdegree : i • a + (a * (N - i)) • 1 = a * N := by
    simp only [nsmul_eq_mul, mul_one]
    calc
      i * a + a * (N - i) = a * i + a * (N - i) := by
        rw [Nat.mul_comm i a]
      _ = a * (i + (N - i)) := by rw [Nat.mul_add]
      _ = a * N := by rw [Nat.add_sub_of_le hiN]
  have hterm := ((hx.pow i).mul (hy.pow (a * (N - i)))).C_mul
    (p.coeff i)
  simpa only [hdegree, mul_assoc] using hterm

theorem weightedThirdInitialPolynomial_isWeightedHomogeneous
    (a N r : ℕ) (p : ℂ[X]) :
    (weightedThirdInitialPolynomial a N r p).IsWeightedHomogeneous
      ![a, 1] (r + a * N) := by
  have hy : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
  have hproduct := (hy.pow r).mul
    (weightedHomogenizedPolynomial_isWeightedHomogeneous a N p)
  simpa [weightedThirdInitialPolynomial, nsmul_eq_mul] using hproduct

theorem eHomogenizedResiduePolynomialMap_isWeightedHomogeneous
    (a N r : ℕ) (p : ℂ[X]) (i : Fin 3) :
    (eHomogenizedResiduePolynomialMap a N r p i).IsWeightedHomogeneous
      ![a, 1] (homogenizedRotationDegrees a N r i) := by
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
    simpa [eHomogenizedResiduePolynomialMap,
      homogenizedRotationDegrees] using hfirst.add hsecond
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
    simpa [eHomogenizedResiduePolynomialMap,
      homogenizedRotationDegrees] using hfirst.add hsecond
  · simpa [eHomogenizedResiduePolynomialMap,
      homogenizedRotationDegrees] using
        weightedThirdInitialPolynomial_isWeightedHomogeneous a N r p

theorem hHomogenizedResiduePolynomialMap_isWeightedHomogeneous
    (a N r : ℕ) (p : ℂ[X]) (i : Fin 3) :
    (hHomogenizedResiduePolynomialMap a N r p i).IsWeightedHomogeneous
      ![a, 1] (homogenizedRotationDegrees a N r i) := by
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
    simpa [hHomogenizedResiduePolynomialMap,
      homogenizedRotationDegrees] using hfirst.add hsecond
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
    simpa [hHomogenizedResiduePolynomialMap,
      homogenizedRotationDegrees] using
        (hfirst.add hsecond).add hthird
  · simpa [hHomogenizedResiduePolynomialMap,
      homogenizedRotationDegrees] using
        weightedThirdInitialPolynomial_isWeightedHomogeneous a N r p

theorem weightedPolynomialMap_weightedHomogenizedPolynomial
    (a N : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) :
    MvPolynomial.eval
        ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)
        (weightedHomogenizedPolynomial a N p) =
      weightedHomogenizedValue a N p z := by
  simp only [weightedHomogenizedPolynomial, weightedHomogenizedValue,
    homogeneousBinaryFormValue, MvPolynomial.eval_sum,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_pow,
    MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i hi
  change p.coeff i *
      ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z) 0 ^ i *
        ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z) 1 ^
          (a * (N - i)) =
    p.coeff i * z.1 ^ i * (z.2 ^ a) ^ (N - i)
  rw [show ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z) 0 = z.1 by
      simp,
    show ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z) 1 = z.2 by
      simp,
    pow_mul]

theorem weightedPolynomialMap_weightedThirdInitialPolynomial
    (a N r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) :
    MvPolynomial.eval
        ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)
        (weightedThirdInitialPolynomial a N r p) =
      weightedThirdInitialValue a N r p z := by
  rw [weightedThirdInitialPolynomial, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_X,
    weightedPolynomialMap_weightedHomogenizedPolynomial]
  rfl

/-- Polynomial evaluation recovers the homogenized `E` rotation map. -/
theorem weightedPolynomialMap_eHomogenizedResiduePolynomialMap
    (a N r : ℕ) (p : ℂ[X]) :
    weightedPolynomialMap (eHomogenizedResiduePolynomialMap a N r p) =
      eHomogenizedResidueRotationMap a N r p := by
  funext z i
  fin_cases i
  · simp [weightedPolynomialMap, eHomogenizedResiduePolynomialMap,
      eHomogenizedResidueRotationMap]
  · simp [weightedPolynomialMap, eHomogenizedResiduePolynomialMap,
      eHomogenizedResidueRotationMap]
    ring
  · exact weightedPolynomialMap_weightedThirdInitialPolynomial
      a N r p z

/-- Polynomial evaluation recovers the homogenized `H` rotation map. -/
theorem weightedPolynomialMap_hHomogenizedResiduePolynomialMap
    (a N r : ℕ) (p : ℂ[X]) :
    weightedPolynomialMap (hHomogenizedResiduePolynomialMap a N r p) =
      hHomogenizedResidueRotationMap a N r p := by
  funext z i
  fin_cases i
  · simp [weightedPolynomialMap, hHomogenizedResiduePolynomialMap,
      hHomogenizedResidueRotationMap]
    ring
  · simp [weightedPolynomialMap, hHomogenizedResiduePolynomialMap,
      hHomogenizedResidueRotationMap]
    ring
  · exact weightedPolynomialMap_weightedThirdInitialPolynomial
      a N r p z

end OnLeConjecture.DThree
