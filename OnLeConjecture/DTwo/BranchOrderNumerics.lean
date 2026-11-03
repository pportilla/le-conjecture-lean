/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.AnalyticBranchPullback
public import OnLeConjecture.DTwo.NumericalAlternatives
public import OnLeConjecture.DTwo.OddBranchIntersection
public import OnLeConjecture.DTwo.QuadraticIntersectionMatrix

/-!
# Branch orders and the numerical alternatives in order two

This file combines the analytic order estimates on the branches of
`x² + yᵏ = 0` with the arithmetic classification of the possible point
bases.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.PlaneCurve

/-- The odd branch estimate for a prepared coordinate, together with its
exact finite order, forces the numerical conclusion of the odd case. -/
theorem odd_numerical_reduction_of_prepared_branch_order
    {k a₁ m M : ℕ}
    (hkOdd : Odd k) (hk : 3 ≤ k) (ha₁ : a₁ ≤ k)
    (hM : M = 2 * k - 2 + a₁) (hm : k - 1 + a₁ ≤ m)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1)
    (A B : Germ 2)
    (hjacobian : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (Germ.quadraticBaseSubstitutionAlgHom k (by omega) A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom k (by omega) B))
    (hdifferential : Germ.differential
      (Germ.quadraticBaseSubstitutionAlgHom k (by omega) A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k (by omega) B) = 0)
    (horder : Germ.vanishingOrder
      ((Germ.oddQuadraticBranchMapGerm k (by omega) epsilon).pullbackRingHom
        (Germ.centeredQuadraticBaseDecomposition k (by omega) A B)) = M) :
    a₁ = 0 ∧ m = k - 1 := by
  let e := (m - 1) / k
  have hmPositive : 1 ≤ m := by omega
  have hbound :=
    Germ.oddQuadraticBranch_centered_vanishingOrder_of_jacobian_dvd
      hkOdd hmPositive epsilon hepsilon A B hjacobian
  dsimp only at hbound
  have hboundNat : min (2 * m) ((2 * e + 1) * k) ≤ M := by
    dsimp only [e]
    rw [horder] at hbound
    exact ENat.natCast_le_natCast.mp hbound
  have hzeroNat (hezero : e = 0) : 2 * m ≤ M := by
    have hzero :=
      Germ.oddQuadraticBranch_centered_vanishingOrder_of_div_eq_zero
        hkOdd hmPositive epsilon hepsilon A B (by simpa [e] using hezero)
          hjacobian hdifferential
    dsimp only at hzero
    rw [horder] at hzero
    exact ENat.natCast_le_natCast.mp hzero
  exact odd_numerical_reduction k a₁ m M e hk ha₁ hM hm rfl
    hzeroNat (fun _ ↦ hboundNat)

/-- In the odd case, finite intersection with the prepared quadratic curve
identifies its intersection multiplicity with the order on the normalization
branch. -/
theorem odd_numerical_reduction_of_prepared_finite_intersection
    {k a₁ m M : ℕ}
    (hkOdd : Odd k) (hk : 3 ≤ k) (ha₁ : a₁ ≤ k)
    (hM : M = 2 * k - 2 + a₁) (hm : k - 1 + a₁ ≤ m)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1)
    (A B : Germ 2)
    (hjacobian : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (Germ.quadraticBaseSubstitutionAlgHom k (by omega) A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom k (by omega) B))
    (hdifferential : Germ.differential
      (Germ.quadraticBaseSubstitutionAlgHom k (by omega) A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k (by omega) B) = 0)
    (hfinite : HasFiniteIntersection (Germ.quadraticBaseEquation k)
      (Germ.centeredQuadraticBaseDecomposition k (by omega) A B))
    (hintersection : intersectionMultiplicity
      (Germ.quadraticBaseEquation k)
      (Germ.centeredQuadraticBaseDecomposition k (by omega) A B)
        hfinite = M) :
    a₁ = 0 ∧ m = k - 1 := by
  let u := Germ.centeredQuadraticBaseDecomposition k (by omega) A B
  let p :=
    (Germ.oddQuadraticBranchMapGerm k (by omega) epsilon).pullbackRingHom u
  have hp : p ≠ 0 :=
    Germ.oddQuadraticBranchMapGerm_pullback_ne_zero_of_base
      k (by omega) epsilon hepsilon u hfinite
  have hpTop : Germ.vanishingOrder p ≠ ⊤ := by
    rw [ne_eq, Germ.vanishingOrder_eq_top_iff]
    exact hp
  have horderNat : (Germ.vanishingOrder p).toNat = M := by
    rw [← hintersection]
    exact (Germ.intersectionMultiplicity_odd_quadratic_eq_branch_order
      k (by omega) hkOdd epsilon hepsilon u hfinite).symm
  have horder : Germ.vanishingOrder p = M := by
    calc
      Germ.vanishingOrder p =
          ((Germ.vanishingOrder p).toNat : ℕ∞) :=
        (ENat.natCast_toNat hpTop).symm
      _ = M := by rw [horderNat]
  exact odd_numerical_reduction_of_prepared_branch_order
    hkOdd hk ha₁ hM hm epsilon hepsilon A B hjacobian hdifferential
      (by simpa only [u, p] using horder)

/-- In the even case, the orders on the two branches add to the total
intersection number. Their analytic lower bounds therefore imply the branch
inequality used in the numerical classification. -/
theorem even_numerical_alternatives_of_prepared_branch_orders
    {a a₁ m nPlus nMinus : ℕ}
    (ha : 1 ≤ a) (ha₁ : a₁ ≤ 2 * a)
    (hm : 2 * a + a₁ ≤ m)
    (hpolar : 2 * (m - 1) ≤ 6 * a + a₁ - 2)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1)
    (A B : Germ 2)
    (hjacobian : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ (2 * a))
        (Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B))
    (horderPlus : Germ.vanishingOrder
      ((Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
        (Germ.centeredQuadraticBaseDecomposition
          (2 * a) (by omega) A B)) = nPlus)
    (horderMinus : Germ.vanishingOrder
      ((Germ.evenQuadraticBranchMapGerm a ha (-epsilon)).pullbackRingHom
        (Germ.centeredQuadraticBaseDecomposition
          (2 * a) (by omega) A B)) = nMinus)
    (hsum : nPlus + nMinus = 4 * a + a₁) :
    (a₁ = 0 ∧ m = 2 * a) ∨
      (a₁ = 2 * a ∧ m = 4 * a) := by
  have hmPositive : 1 ≤ m := by omega
  have hbounds :=
    Germ.evenQuadraticBranches_centered_vanishingOrder_of_jacobian_dvd
      ha hmPositive epsilon hepsilon A B hjacobian
  apply even_numerical_alternatives a a₁ m ha ha₁ hm hpolar
  intro hmStrict
  let e := (m - 1) / (2 * a)
  have hePositive : 1 ≤ e := by
    dsimp only [e]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * a)).2
    omega
  have hthree : 3 * a ≤ a + e * (2 * a) := by
    have hmul : 2 * a ≤ e * (2 * a) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (2 * a) hePositive
    omega
  have hmin : min m (3 * a) ≤
      min m (a + e * (2 * a)) := by
    exact min_le_min_left m hthree
  have hplusWithTop : ((min m (3 * a) : ℕ) : ℕ∞) ≤ nPlus := by
    rw [← horderPlus]
    exact le_trans (by exact_mod_cast hmin) hbounds.1
  have hminusWithTop : ((min m (3 * a) : ℕ) : ℕ∞) ≤ nMinus := by
    rw [← horderMinus]
    exact le_trans (by exact_mod_cast hmin) hbounds.2
  have hplus : min m (3 * a) ≤ nPlus :=
    ENat.natCast_le_natCast.mp hplusWithTop
  have hminus : min m (3 * a) ≤ nMinus :=
    ENat.natCast_le_natCast.mp hminusWithTop
  omega

/-- In the even case, finite intersection with the prepared quadratic curve
supplies the sum of the two branch orders used by the numerical
classification. -/
theorem even_numerical_alternatives_of_prepared_finite_intersection
    {a a₁ m : ℕ}
    (ha : 1 ≤ a) (ha₁ : a₁ ≤ 2 * a)
    (hm : 2 * a + a₁ ≤ m)
    (hpolar : 2 * (m - 1) ≤ 6 * a + a₁ - 2)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1)
    (A B : Germ 2)
    (hjacobian : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ (2 * a))
        (Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B))
    (hfinite : HasFiniteIntersection
      (Germ.quadraticBaseEquation (2 * a))
      (Germ.centeredQuadraticBaseDecomposition
        (2 * a) (by omega) A B))
    (hintersection : intersectionMultiplicity
      (Germ.quadraticBaseEquation (2 * a))
      (Germ.centeredQuadraticBaseDecomposition
        (2 * a) (by omega) A B) hfinite = 4 * a + a₁) :
    (a₁ = 0 ∧ m = 2 * a) ∨
      (a₁ = 2 * a ∧ m = 4 * a) := by
  let u := Germ.centeredQuadraticBaseDecomposition
    (2 * a) (by omega) A B
  let pPlus :=
    (Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u
  let pMinus :=
    (Germ.evenQuadraticBranchMapGerm a ha (-epsilon)).pullbackRingHom u
  have hne :=
    Germ.evenQuadraticBranchMapGerm_pullbacks_ne_zero_of_base
      a ha epsilon hepsilon u hfinite
  have hplusTop : Germ.vanishingOrder pPlus ≠ ⊤ := by
    rw [ne_eq, Germ.vanishingOrder_eq_top_iff]
    exact hne.1
  have hminusTop : Germ.vanishingOrder pMinus ≠ ⊤ := by
    rw [ne_eq, Germ.vanishingOrder_eq_top_iff]
    exact hne.2
  let nPlus := (Germ.vanishingOrder pPlus).toNat
  let nMinus := (Germ.vanishingOrder pMinus).toNat
  have horderPlus : Germ.vanishingOrder pPlus = nPlus := by
    exact (ENat.natCast_toNat hplusTop).symm
  have horderMinus : Germ.vanishingOrder pMinus = nMinus := by
    exact (ENat.natCast_toNat hminusTop).symm
  have hsum : nPlus + nMinus = 4 * a + a₁ := by
    have hbranch :=
      Germ.intersectionMultiplicity_even_quadratic_eq_branch_sum
        a ha epsilon hepsilon u hfinite
    rw [hintersection] at hbranch
    have hplus := Germ.intersectionMultiplicity_evenBranchFactor_eq_order
      a ha epsilon u hne.1
    have hminus := Germ.intersectionMultiplicity_evenBranchFactor_eq_order
      a ha (-epsilon) u hne.2
    dsimp only [nPlus, nMinus]
    rw [hplus, hminus] at hbranch
    exact hbranch.symm
  exact even_numerical_alternatives_of_prepared_branch_orders
    ha ha₁ hm hpolar epsilon hepsilon A B hjacobian
      (by simpa only [u, pPlus] using horderPlus)
      (by simpa only [u, pMinus] using horderMinus) hsum

end OnLeConjecture.DTwo
