/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.MapNumericalReduction
public import OnLeConjecture.Numerical.SmallPointBasisCounts

/-!
# Point basis input for the order two numerical reduction

The point basis formulas determine the intersection number and the lower
bound for the maximal transverse multiplicity. The polar inequality then
determines the bound for the number of entries equal to one. This module
supplies those consequences to the map level numerical reduction.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.Numerical
open OnLeConjecture.PlaneCurve

namespace PointedMapGerm

/-- In the odd case, the point basis identities and the polar inequality
supply every numerical hypothesis of the map level branch reduction. -/
theorem odd_numerical_reduction_of_pointBasis
    (f : PointedMapGerm 2 3) {N k m : ℕ}
    (c : PointBasisCertificate N)
    (hd : c.d = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hkOdd : Odd k)
    (hk : 3 ≤ k)
    (hkCount : k = 2 * c.multiplicityCount 2 + 1)
    (htransverse : c.S ≤ m)
    (hpolar : 2 * (m - 1) ≤
      6 * c.multiplicityCount 2 + c.multiplicityCount 1 - 1)
    (hfirst : f.1.component (0 : Fin 3) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ k)
    (hminors : ∀ i : Fin 2,
      Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
        Germ.jacobian (f.1.component (0 : Fin 3))
          (f.1.component i.succ))
    (hdifferential : f.differential = 0)
    (i : Fin 2)
    (hfinite : HasFiniteIntersection (f.1.component (0 : Fin 3))
      (f.1.component i.succ))
    (hintersection : intersectionMultiplicity
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite = c.M) :
    c.multiplicityCount 1 = 0 ∧ m = k - 1 := by
  have hS := c.S_eq_two_mul_count_two_add_count_one hd hpositive
  have hM := c.M_eq_four_mul_count_two_add_count_one hd hpositive
  have haOne : c.multiplicityCount 1 ≤ k := by omega
  have hm : k - 1 + c.multiplicityCount 1 ≤ m := by omega
  have hMFormula : c.M = 2 * k - 2 + c.multiplicityCount 1 := by
    omega
  exact odd_numerical_reduction_of_map_component f
    hkOdd hk haOne hMFormula hm hfirst hminors hdifferential i hfinite
      hintersection Complex.I (by simp)

/-- In the even case, the point basis identities and the polar inequality
supply every numerical hypothesis of the map level branch reduction. -/
theorem even_numerical_alternatives_of_pointBasis
    (f : PointedMapGerm 2 3) {N k m : ℕ}
    (c : PointBasisCertificate N)
    (hd : c.d = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hk : 3 ≤ k)
    (hkCount : k = 2 * c.multiplicityCount 2)
    (htransverse : c.S ≤ m)
    (hpolar : 2 * (m - 1) ≤
      6 * c.multiplicityCount 2 + c.multiplicityCount 1 - 2)
    (hfirst : f.1.component (0 : Fin 3) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ k)
    (hminors : ∀ i : Fin 2,
      Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
        Germ.jacobian (f.1.component (0 : Fin 3))
          (f.1.component i.succ))
    (hdifferential : f.differential = 0)
    (i : Fin 2)
    (hfinite : HasFiniteIntersection (f.1.component (0 : Fin 3))
      (f.1.component i.succ))
    (hintersection : intersectionMultiplicity
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite = c.M) :
    (c.multiplicityCount 1 = 0 ∧ m = k) ∨
      (c.multiplicityCount 1 = k ∧ m = 2 * k) := by
  have haTwo : 1 ≤ c.multiplicityCount 2 := by omega
  have hS := c.S_eq_two_mul_count_two_add_count_one hd hpositive
  have hM := c.M_eq_four_mul_count_two_add_count_one hd hpositive
  have haOne : c.multiplicityCount 1 ≤
      2 * c.multiplicityCount 2 := by
    omega
  have hm : 2 * c.multiplicityCount 2 +
      c.multiplicityCount 1 ≤ m := by
    omega
  have hfirstEven : f.1.component (0 : Fin 3) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^
          (2 * c.multiplicityCount 2) := by
    simpa only [hkCount] using hfirst
  have hintersectionEven : intersectionMultiplicity
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite =
        4 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
    rw [hintersection, hM]
  have halternatives := even_numerical_alternatives_of_map_component f
    haTwo haOne hm hpolar hfirstEven hminors hdifferential i hfinite
      hintersectionEven Complex.I (by simp)
  rcases halternatives with hremaining | hextreme
  · left
    omega
  · right
    omega

/-- The curve parity formulas and their corresponding polar bounds reduce
the map to the odd numerical endpoint or one of the two even endpoints. -/
theorem numerical_alternatives_of_pointBasis
    (f : PointedMapGerm 2 3) {N k m : ℕ}
    (c : PointBasisCertificate N)
    (hd : c.d = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hk : 3 ≤ k)
    (htransverse : c.S ≤ m)
    (hparity :
      (Odd k ∧ k = 2 * c.multiplicityCount 2 + 1 ∧
        2 * (m - 1) ≤
          6 * c.multiplicityCount 2 + c.multiplicityCount 1 - 1) ∨
      (Even k ∧ k = 2 * c.multiplicityCount 2 ∧
        2 * (m - 1) ≤
          6 * c.multiplicityCount 2 + c.multiplicityCount 1 - 2))
    (hfirst : f.1.component (0 : Fin 3) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ k)
    (hminors : ∀ i : Fin 2,
      Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
        Germ.jacobian (f.1.component (0 : Fin 3))
          (f.1.component i.succ))
    (hdifferential : f.differential = 0)
    (i : Fin 2)
    (hfinite : HasFiniteIntersection (f.1.component (0 : Fin 3))
      (f.1.component i.succ))
    (hintersection : intersectionMultiplicity
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite = c.M) :
    (Odd k ∧ c.multiplicityCount 1 = 0 ∧ m = k - 1) ∨
      (Even k ∧
        ((c.multiplicityCount 1 = 0 ∧ m = k) ∨
          (c.multiplicityCount 1 = k ∧ m = 2 * k))) := by
  rcases hparity with hodd | heven
  · left
    refine ⟨hodd.1, ?_⟩
    exact odd_numerical_reduction_of_pointBasis f c hd hpositive hodd.1 hk
      hodd.2.1 htransverse hodd.2.2 hfirst hminors hdifferential i
        hfinite hintersection
  · right
    refine ⟨heven.1, ?_⟩
    exact even_numerical_alternatives_of_pointBasis f c hd hpositive hk
      heven.2.1 htransverse heven.2.2 hfirst hminors hdifferential i
        hfinite hintersection

/-- The point basis genus identity and one polar inequality determine the
parity formulas used in the numerical reduction. -/
theorem numerical_alternatives_of_pointBasis_curveInvariants
    (f : PointedMapGerm 2 3) {N k m : ℕ}
    (c : PointBasisCertificate N)
    (hd : c.d = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hk : 3 ≤ k)
    (hgenus : 2 * c.multiplicityCount 2 + 2 =
      k + Nat.gcd 2 k)
    (htransverse : c.S ≤ m)
    (hpolar : 2 * (m - 1) + Nat.gcd 2 k ≤
      6 * c.multiplicityCount 2 + c.multiplicityCount 1)
    (hfirst : f.1.component (0 : Fin 3) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ k)
    (hminors : ∀ i : Fin 2,
      Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
        Germ.jacobian (f.1.component (0 : Fin 3))
          (f.1.component i.succ))
    (hdifferential : f.differential = 0)
    (i : Fin 2)
    (hfinite : HasFiniteIntersection (f.1.component (0 : Fin 3))
      (f.1.component i.succ))
    (hintersection : intersectionMultiplicity
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite = c.M) :
    (Odd k ∧ c.multiplicityCount 1 = 0 ∧ m = k - 1) ∨
      (Even k ∧
        ((c.multiplicityCount 1 = 0 ∧ m = k) ∨
          (c.multiplicityCount 1 = k ∧ m = 2 * k))) := by
  rcases k.even_or_odd with heven | hodd
  · have hgcd : Nat.gcd 2 k = 2 :=
      Nat.gcd_eq_left_iff_dvd.mpr heven.two_dvd
    have hkCount : k = 2 * c.multiplicityCount 2 := by omega
    have hpolarEven : 2 * (m - 1) ≤
        6 * c.multiplicityCount 2 + c.multiplicityCount 1 - 2 := by
      omega
    right
    refine ⟨heven, ?_⟩
    exact even_numerical_alternatives_of_pointBasis f c hd hpositive hk
      hkCount htransverse hpolarEven hfirst hminors hdifferential i
        hfinite hintersection
  · have hgcd : Nat.gcd 2 k = 1 :=
      hodd.coprime_two_left.gcd_eq_one
    have hkCount : k = 2 * c.multiplicityCount 2 + 1 := by omega
    have hpolarOdd : 2 * (m - 1) ≤
        6 * c.multiplicityCount 2 + c.multiplicityCount 1 - 1 := by
      omega
    left
    refine ⟨hodd, ?_⟩
    exact odd_numerical_reduction_of_pointBasis f c hd hpositive hodd hk
      hkCount htransverse hpolarOdd hfirst hminors hdifferential i
        hfinite hintersection

end PointedMapGerm

end OnLeConjecture.DTwo
