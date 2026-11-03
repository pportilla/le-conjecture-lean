/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariablePowerSubstitution
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ENat.BigOperators

/-!
# Orders of resultants from analytic root factorizations

An explicit factorization into monic linear factors computes a polynomial
resultant as a product of evaluations. Over the discrete valuation ring of
analytic germs in one variable, its vanishing order is consequently the
sum of the orders of those evaluations.

Roots are indexed with multiplicity and need not be distinct. The order
takes values in the extended natural numbers, so zero evaluations and zero
resultants are included. The final results use an actual positive power
substitution on analytic germs and a factorization after that substitution.
Existence of such a factorization and identification of resultant order
with a plane intersection multiplicity are not asserted here.
-/

public section

open scoped BigOperators

namespace OnLeConjecture.Analytic

namespace PolynomialResultant

open _root_.Polynomial

/-- A factorization into monic linear factors computes the resultant with
any upper bound on the second polynomial's degree. -/
theorem eq_prod_eval_of_root_factorization
    {R : Type*} [CommRing R] [Nontrivial R]
    (d n : ℕ) (P Q : R[X]) (root : Fin d → R)
    (hfactor : P = ∏ i, (X - C (root i)))
    (hQdegree : Q.natDegree ≤ n) :
    P.resultant Q P.natDegree n = ∏ i, Q.eval (root i) := by
  classical
  rw [hfactor, _root_.Polynomial.resultant_prod_left
    Finset.univ (fun i : Fin d => X - C (root i)) Q n (by simp) hQdegree]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [natDegree_X_sub_C, resultant_X_sub_C_left Q n (root i) hQdegree]

end PolynomialResultant

namespace Germ

open _root_.Polynomial

/-- The order of a finite product of one-variable analytic germs is the
sum of their orders, including products with a zero factor. -/
theorem vanishingOrder_finset_prod
    {ι : Type*} (s : Finset ι) (q : ι → Germ 1) :
    Germ.vanishingOrder (∏ i ∈ s, q i) =
      ∑ i ∈ s, Germ.vanishingOrder (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Germ.vanishingOrder_mul, ih,
        Finset.sum_insert hi]

/-- The order of a fixed-degree resultant equals the sum of evaluation
orders along an explicit analytic root factorization. -/
theorem vanishingOrder_resultant_eq_sum_of_root_factorization
    (d n : ℕ) (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hfactor : P = ∏ i, (X - C (root i)))
    (hQdegree : Q.natDegree ≤ n) :
    Germ.vanishingOrder (P.resultant Q P.natDegree n) =
      ∑ i, Germ.vanishingOrder (Q.eval (root i)) := by
  rw [PolynomialResultant.eq_prod_eval_of_root_factorization
    d n P Q root hfactor hQdegree, Germ.vanishingOrder_finset_prod]

/-- A uniform lower bound on the evaluation orders gives the degree times
that bound for the resultant order. -/
theorem mul_le_vanishingOrder_resultant_of_root_orders
    (d n L : ℕ) (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hfactor : P = ∏ i, (X - C (root i)))
    (hQdegree : Q.natDegree ≤ n)
    (hroot : ∀ i, (L : ℕ∞) ≤ Germ.vanishingOrder (Q.eval (root i))) :
    ((d * L : ℕ) : ℕ∞) ≤ Germ.vanishingOrder (P.resultant Q P.natDegree n) := by
  rw [Germ.vanishingOrder_resultant_eq_sum_of_root_factorization
    d n P Q root hfactor hQdegree]
  calc
    ((d * L : ℕ) : ℕ∞) = ∑ _i : Fin d, (L : ℕ∞) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i, Germ.vanishingOrder (Q.eval (root i)) :=
      Finset.sum_le_sum (fun i _hi => hroot i)

/-- Strict evaluation-order bounds give a strict resultant-order bound
when the root factorization has positive degree. -/
theorem mul_lt_vanishingOrder_resultant_of_root_orders
    (d n L : ℕ) (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hd : 0 < d)
    (hfactor : P = ∏ i, (X - C (root i)))
    (hQdegree : Q.natDegree ≤ n)
    (hroot : ∀ i, (L : ℕ∞) < Germ.vanishingOrder (Q.eval (root i))) :
    ((d * L : ℕ) : ℕ∞) < Germ.vanishingOrder (P.resultant Q P.natDegree n) := by
  have hsuccessor (i : Fin d) :
      ((L + 1 : ℕ) : ℕ∞) ≤ Germ.vanishingOrder (Q.eval (root i)) := by
    simpa using (ENat.natCast_add_one_le_iff (m := L)).mpr (hroot i)
  have hlower := Germ.mul_le_vanishingOrder_resultant_of_root_orders
    d n (L + 1) P Q root hfactor hQdegree hsuccessor
  have hstrict : ((d * L : ℕ) : ℕ∞) < ((d * (L + 1) : ℕ) : ℕ∞) := by
    exact_mod_cast (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self L) hd)
  exact hstrict.trans_le hlower

/-- The scalar order formula for the usual resultant is the case where
the second degree bound is its actual degree. -/
theorem vanishingOrder_resultant_eq_sum
    (d : ℕ) (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hfactor : P = ∏ i, (X - C (root i))) :
    Germ.vanishingOrder (P.resultant Q) =
      ∑ i, Germ.vanishingOrder (Q.eval (root i)) :=
  Germ.vanishingOrder_resultant_eq_sum_of_root_factorization
    d Q.natDegree P Q root hfactor le_rfl

/-- The resultant is nonzero exactly when every evaluation at the roots in
the factorization is nonzero. -/
theorem resultant_ne_zero_iff_evaluations_ne_zero
    (d : ℕ) (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hfactor : P = ∏ i, (X - C (root i))) :
    P.resultant Q ≠ 0 ↔ ∀ i, Q.eval (root i) ≠ 0 := by
  classical
  rw [PolynomialResultant.eq_prod_eval_of_root_factorization
    d Q.natDegree P Q root hfactor le_rfl]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]

/-- For a nonzero resultant the extended-order identity becomes an identity
of finite natural orders. -/
theorem vanishingOrder_resultant_toNat_eq_sum
    (d : ℕ) (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hfactor : P = ∏ i, (X - C (root i)))
    (hresultant : P.resultant Q ≠ 0) :
    (Germ.vanishingOrder (P.resultant Q)).toNat =
      ∑ i, (Germ.vanishingOrder (Q.eval (root i))).toNat := by
  have hroot := (Germ.resultant_ne_zero_iff_evaluations_ne_zero
    d P Q root hfactor).mp hresultant
  rw [Germ.vanishingOrder_resultant_eq_sum d P Q root hfactor]
  apply ENat.toNat_sum
  intro i _hi htop
  exact hroot i (Germ.vanishingOrder_eq_top_iff.mp htop)

/-- The lower resultant-order bound is an ordinary natural-number bound
when the resultant is nonzero. -/
theorem mul_le_vanishingOrder_resultant_toNat
    (d L : ℕ) (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hfactor : P = ∏ i, (X - C (root i)))
    (hresultant : P.resultant Q ≠ 0)
    (hroot : ∀ i, (L : ℕ∞) ≤ Germ.vanishingOrder (Q.eval (root i))) :
    d * L ≤ (Germ.vanishingOrder (P.resultant Q)).toNat := by
  have hbound := Germ.mul_le_vanishingOrder_resultant_of_root_orders
    d Q.natDegree L P Q root hfactor le_rfl hroot
  have hfinite : Germ.vanishingOrder (P.resultant Q) ≠ ⊤ := by
    intro htop
    exact hresultant (Germ.vanishingOrder_eq_top_iff.mp htop)
  simpa using ENat.toNat_le_toNat hbound hfinite

/-- Strict evaluation-order bounds give a strict finite natural-number
bound when the degree is positive and the resultant is nonzero. -/
theorem mul_lt_vanishingOrder_resultant_toNat
    (d L : ℕ) (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hd : 0 < d)
    (hfactor : P = ∏ i, (X - C (root i)))
    (hresultant : P.resultant Q ≠ 0)
    (hroot : ∀ i, (L : ℕ∞) < Germ.vanishingOrder (Q.eval (root i))) :
    d * L < (Germ.vanishingOrder (P.resultant Q)).toNat := by
  have hbound := Germ.mul_lt_vanishingOrder_resultant_of_root_orders
    d Q.natDegree L P Q root hd hfactor le_rfl hroot
  have hfinite : Germ.vanishingOrder (P.resultant Q) ≠ ⊤ := by
    intro htop
    exact hresultant (Germ.vanishingOrder_eq_top_iff.mp htop)
  rw [← ENat.natCast_toNat hfinite] at hbound
  exact_mod_cast hbound

/-- After a positive power substitution, the evaluation orders of a root
factorization add up to the substitution exponent times the original
resultant order. -/
theorem power_mul_vanishingOrder_resultant_eq_sum
    (s d : ℕ) (hs : 1 ≤ s)
    (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hPmonic : P.Monic)
    (hfactor : P.map (Germ.oneVariablePowerMapGerm s hs).pullbackRingHom =
      ∏ i, (X - C (root i))) :
    s • Germ.vanishingOrder (P.resultant Q) =
      ∑ i, Germ.vanishingOrder
        ((Q.map (Germ.oneVariablePowerMapGerm s hs).pullbackRingHom).eval (root i)) := by
  let φ := (Germ.oneVariablePowerMapGerm s hs).pullbackRingHom
  have hmapDegree : (P.map φ).natDegree = P.natDegree := hPmonic.natDegree_map φ
  have hQdegree : (Q.map φ).natDegree ≤ Q.natDegree := natDegree_map_le
  rw [← Germ.vanishingOrder_oneVariablePowerMapGerm_pullback s hs,
    ← _root_.Polynomial.resultant_map_map]
  change Germ.vanishingOrder
      ((P.map φ).resultant (Q.map φ) P.natDegree Q.natDegree) = _
  rw [← hmapDegree]
  exact Germ.vanishingOrder_resultant_eq_sum_of_root_factorization
    d Q.natDegree (P.map φ) (Q.map φ) root hfactor hQdegree

/-- Lower evaluation-order bounds after ramification give the corresponding
bound on the original resultant order multiplied by the ramification
exponent. -/
theorem mul_le_power_mul_vanishingOrder_resultant
    (s d L : ℕ) (hs : 1 ≤ s)
    (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hPmonic : P.Monic)
    (hfactor : P.map (Germ.oneVariablePowerMapGerm s hs).pullbackRingHom =
      ∏ i, (X - C (root i)))
    (hroot : ∀ i, (L : ℕ∞) ≤ Germ.vanishingOrder
      ((Q.map (Germ.oneVariablePowerMapGerm s hs).pullbackRingHom).eval (root i))) :
    ((d * L : ℕ) : ℕ∞) ≤ s • Germ.vanishingOrder (P.resultant Q) := by
  rw [Germ.power_mul_vanishingOrder_resultant_eq_sum s d hs P Q root hPmonic hfactor]
  calc
    ((d * L : ℕ) : ℕ∞) = ∑ _i : Fin d, (L : ℕ∞) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i, Germ.vanishingOrder
        ((Q.map (Germ.oneVariablePowerMapGerm s hs).pullbackRingHom).eval (root i)) :=
      Finset.sum_le_sum (fun i _hi => hroot i)

/-- Strict evaluation-order bounds after ramification give a strict bound
for positive degree, including when the resultant vanishes identically. -/
theorem mul_lt_power_mul_vanishingOrder_resultant
    (s d L : ℕ) (hs : 1 ≤ s) (hd : 0 < d)
    (P Q : Polynomial (Germ 1)) (root : Fin d → Germ 1)
    (hPmonic : P.Monic)
    (hfactor : P.map (Germ.oneVariablePowerMapGerm s hs).pullbackRingHom =
      ∏ i, (X - C (root i)))
    (hroot : ∀ i, (L : ℕ∞) < Germ.vanishingOrder
      ((Q.map (Germ.oneVariablePowerMapGerm s hs).pullbackRingHom).eval (root i))) :
    ((d * L : ℕ) : ℕ∞) < s • Germ.vanishingOrder (P.resultant Q) := by
  have hsuccessor (i : Fin d) :
      ((L + 1 : ℕ) : ℕ∞) ≤ Germ.vanishingOrder
        ((Q.map (Germ.oneVariablePowerMapGerm s hs).pullbackRingHom).eval (root i)) := by
    simpa using (ENat.natCast_add_one_le_iff (m := L)).mpr (hroot i)
  have hlower := Germ.mul_le_power_mul_vanishingOrder_resultant
    s d (L + 1) hs P Q root hPmonic hfactor hsuccessor
  have hstrict : ((d * L : ℕ) : ℕ∞) < ((d * (L + 1) : ℕ) : ℕ∞) := by
    exact_mod_cast (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self L) hd)
  exact hstrict.trans_le hlower

end Germ

end OnLeConjecture.Analytic
