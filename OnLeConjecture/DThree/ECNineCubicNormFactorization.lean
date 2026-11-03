/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineUnitChartNorm
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Norm factorization for a cubic power basis

The norm of an element in a cubic power basis has an explicit formula.
After the cubic relation splits in a target ring, this formula is the product
of the three evaluations at its roots.
-/

public section

noncomputable section

open Polynomial Module

namespace OnLeConjecture.DThree

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The norm formula for a basis formed by the first three powers of an
element satisfying a cubic equation. -/
theorem cubicBasis_norm_formula
    (b : Basis (Fin 3) R A) (r : A) (a : R)
    (hb : ∀ i : Fin 3, b i = r ^ (i : ℕ))
    (hr : r ^ 3 = algebraMap R A a) (z : A) :
    Algebra.norm R z =
      (b.repr z 0) ^ 3 + a * (b.repr z 1) ^ 3 +
        a ^ 2 * (b.repr z 2) ^ 3 -
          3 * a * (b.repr z 0) * (b.repr z 1) * (b.repr z 2) := by
  let c : Fin 3 → R := fun i ↦ b.repr z i
  have hz : z = c 0 • b 0 + c 1 • b 1 + c 2 • b 2 := by
    rw [← b.sum_repr z, Fin.sum_univ_three]
  have hb0 : b 0 = 1 := by simpa using hb 0
  have hb1 : b 1 = r := by simpa using hb 1
  have hb2 : b 2 = r ^ 2 := by simpa using hb 2
  have hprod0 : z * b 0 = c 0 • b 0 + c 1 • b 1 + c 2 • b 2 := by
    simpa only [hb0, mul_one] using hz
  have hprod1 :
      z * b 1 = (a * c 2) • b 0 + c 0 • b 1 + c 1 • b 2 := by
    rw [hz, hb0, hb1, hb2, Algebra.smul_def, Algebra.smul_def,
      Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def,
      add_mul, add_mul]
    simp only [map_mul, mul_one]
    linear_combination (algebraMap R A (c 2)) * hr
  have hprod2 :
      z * b 2 = (a * c 1) • b 0 + (a * c 2) • b 1 + c 0 • b 2 := by
    rw [hz, hb0, hb1, hb2, Algebra.smul_def, Algebra.smul_def,
      Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def,
      add_mul, add_mul]
    simp only [map_mul, mul_one]
    linear_combination
      (algebraMap R A (c 1) + algebraMap R A (c 2) * r) * hr
  rw [Algebra.norm_eq_matrix_det b]
  have h00 : Algebra.leftMulMatrix b z 0 0 = c 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hprod0]
    simp
  have h10 : Algebra.leftMulMatrix b z 1 0 = c 1 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hprod0]
    simp
  have h20 : Algebra.leftMulMatrix b z 2 0 = c 2 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hprod0]
    simp
  have h01 : Algebra.leftMulMatrix b z 0 1 = a * c 2 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hprod1]
    simp
  have h11 : Algebra.leftMulMatrix b z 1 1 = c 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hprod1]
    simp
  have h21 : Algebra.leftMulMatrix b z 2 1 = c 1 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hprod1]
    simp
  have h02 : Algebra.leftMulMatrix b z 0 2 = a * c 1 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hprod2]
    simp
  have h12 : Algebra.leftMulMatrix b z 1 2 = a * c 2 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hprod2]
    simp
  have h22 : Algebra.leftMulMatrix b z 2 2 = c 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hprod2]
    simp
  rw [Matrix.det_fin_three, h00, h10, h20, h01, h11, h21, h02, h12, h22]
  dsimp only [c]
  ring

/-- Evaluation of an element written in a cubic power basis. -/
@[expose]
def cubicBasisEvaluation {S : Type*} [CommRing S]
    (f : R →+* S) (b : Basis (Fin 3) R A) (z : A) (x : S) : S :=
  f (b.repr z 0) + f (b.repr z 1) * x + f (b.repr z 2) * x ^ 2

/-- The product identity for evaluation at the three roots of a cubic
equation. -/
theorem cubic_product_identity {S : Type*} [CommRing S]
    (c0 c1 c2 x omega : S) (homega : omega ^ 2 + omega + 1 = 0) :
    (c0 + c1 * x + c2 * x ^ 2) *
        (c0 + c1 * (omega * x) + c2 * (omega * x) ^ 2) *
      (c0 + c1 * (omega ^ 2 * x) + c2 * (omega ^ 2 * x) ^ 2) =
        c0 ^ 3 + c1 ^ 3 * x ^ 3 + c2 ^ 3 * x ^ 6 -
          3 * c0 * c1 * c2 * x ^ 3 := by
  linear_combination
    x * (c0 + c1 * x + c2 * x ^ 2) *
      (c0 * c1 + c0 * c2 * omega ^ 2 * x - c0 * c2 * omega * x +
        c0 * c2 * x + c1 ^ 2 * omega * x - c1 ^ 2 * x +
        c1 * c2 * omega ^ 3 * x ^ 2 - c1 * c2 * omega * x ^ 2 +
        c1 * c2 * x ^ 2 + c2 ^ 2 * omega ^ 4 * x ^ 3 -
        c2 ^ 2 * omega ^ 3 * x ^ 3 + c2 ^ 2 * omega * x ^ 3 -
        c2 ^ 2 * x ^ 3) * homega

/-- Evaluation through a ring homomorphism agrees with the expression in
the basis coordinates. -/
theorem cubicBasisEvaluation_eq_map
    {S : Type*} [CommRing S]
    (b : Basis (Fin 3) R A) (r : A)
    (hb : ∀ i : Fin 3, b i = r ^ (i : ℕ))
    (z : A) (f : R →+* S) (g : A →+* S)
    (hbase : g.comp (algebraMap R A) = f) (x : S)
    (hroot : g r = x) :
    cubicBasisEvaluation f b z x = g z := by
  let c : Fin 3 → R := fun i ↦ b.repr z i
  have hz : z = c 0 • b 0 + c 1 • b 1 + c 2 • b 2 := by
    rw [← b.sum_repr z, Fin.sum_univ_three]
  have hb0 : b 0 = 1 := by simpa using hb 0
  have hb1 : b 1 = r := by simpa using hb 1
  have hb2 : b 2 = r ^ 2 := by simpa using hb 2
  change f (c 0) + f (c 1) * x + f (c 2) * x ^ 2 = g z
  conv_rhs => rw [hz]
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def,
    map_add, map_add, map_mul, map_mul, map_mul,
    hb0, hb1, hb2, map_one, hroot, map_pow]
  have hcoeff (q : R) : g (algebraMap R A q) = f q := by
    exact DFunLike.congr_fun hbase q
  rw [hcoeff, hcoeff, hcoeff]
  simp [hroot]

/-- A cubic norm splits as the product of the evaluations at its three
roots. -/
theorem map_cubicBasis_norm_eq_product
    {S : Type*} [CommRing S]
    (b : Basis (Fin 3) R A) (r : A) (a : R)
    (hb : ∀ i : Fin 3, b i = r ^ (i : ℕ))
    (hr : r ^ 3 = algebraMap R A a) (z : A)
    (f : R →+* S) (alpha omega : S)
    (halpha : alpha ^ 3 = f a)
    (homega : omega ^ 2 + omega + 1 = 0) :
    f (Algebra.norm R z) =
      cubicBasisEvaluation f b z alpha *
        cubicBasisEvaluation f b z (omega * alpha) *
          cubicBasisEvaluation f b z (omega ^ 2 * alpha) := by
  rw [cubicBasis_norm_formula b r a hb hr z]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat,
    cubicBasisEvaluation]
  rw [cubic_product_identity _ _ _ _ _ homega]
  rw [show alpha ^ 6 = (alpha ^ 3) ^ 2 by ring, halpha]
  ring

end OnLeConjecture.DThree
