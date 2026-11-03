/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.PointBasisNumericalAssembly
public import OnLeConjecture.Numerical.ProximityReduction

/-!
# Proximity input for the order two numerical reduction

Connected proximity data canonically determine the point basis certificate
used by the order two map reduction. A decreasing generation function gives
the required connectivity.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.Numerical
open OnLeConjecture.PlaneCurve

namespace PointedMapGerm

/-- Connected proximity data and the curve invariants give the odd endpoint
or one of the two even endpoints. -/
theorem numerical_alternatives_of_proximity_curveInvariants
    (f : PointedMapGerm 2 3) {N k m : ℕ}
    (c : ProximityCertificate (Fin N))
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hk : 3 ≤ k)
    (hgenus : 2 * c.multiplicityCount 2 + 2 =
      k + Nat.gcd 2 k)
    (htransverse : c.totalMultiplicity ≤ m)
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
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite =
        c.squareMultiplicity) :
    (Odd k ∧ c.multiplicityCount 1 = 0 ∧ m = k - 1) ∨
      (Even k ∧
        ((c.multiplicityCount 1 = 0 ∧ m = k) ∨
          (c.multiplicityCount 1 = k ∧ m = 2 * k))) := by
  let pointBasis := c.toPointBasisCertificate hconnected
  have hpointBasisOrder : pointBasis.d = 2 := by
    exact hroot
  have hpointBasisPositive : ∀ p,
      1 ≤ pointBasis.multiplicity p := by
    exact hpositive
  have hpointBasisGenus :
      2 * pointBasis.multiplicityCount 2 + 2 =
        k + Nat.gcd 2 k := by
    simpa only [pointBasis,
      ProximityCertificate.toPointBasisCertificate_multiplicityCount]
      using hgenus
  have hpointBasisTransverse : pointBasis.S ≤ m := by
    change (c.toPointBasisCertificate hconnected).S ≤ m
    rw [ProximityCertificate.toPointBasisCertificate_S]
    exact htransverse
  have hpointBasisPolar :
      2 * (m - 1) + Nat.gcd 2 k ≤
        6 * pointBasis.multiplicityCount 2 +
          pointBasis.multiplicityCount 1 := by
    simpa only [pointBasis,
      ProximityCertificate.toPointBasisCertificate_multiplicityCount]
      using hpolar
  have hpointBasisIntersection : intersectionMultiplicity
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite =
        pointBasis.M := by
    change intersectionMultiplicity
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite =
        (c.toPointBasisCertificate hconnected).M
    rw [ProximityCertificate.toPointBasisCertificate_M]
    exact hintersection
  have halternatives :=
    numerical_alternatives_of_pointBasis_curveInvariants f pointBasis
      hpointBasisOrder hpointBasisPositive hk hpointBasisGenus
        hpointBasisTransverse hpointBasisPolar hfirst hminors hdifferential
          i hfinite hpointBasisIntersection
  simpa only [pointBasis,
    ProximityCertificate.toPointBasisCertificate_multiplicityCount]
    using halternatives

/-- A generation function decreasing along parents supplies connectivity and
hence the complete order two numerical alternative. -/
theorem numerical_alternatives_of_proximity_generation
    (f : PointedMapGerm 2 3) {N k m : ℕ}
    (c : ProximityCertificate (Fin N))
    (generation : Fin N → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p →
      generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hk : 3 ≤ k)
    (hgenus : 2 * c.multiplicityCount 2 + 2 =
      k + Nat.gcd 2 k)
    (htransverse : c.totalMultiplicity ≤ m)
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
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite =
        c.squareMultiplicity) :
    (Odd k ∧ c.multiplicityCount 1 = 0 ∧ m = k - 1) ∨
      (Even k ∧
        ((c.multiplicityCount 1 = 0 ∧ m = k) ∨
          (c.multiplicityCount 1 = k ∧ m = 2 * k))) := by
  exact numerical_alternatives_of_proximity_curveInvariants f c
    (c.root_reachable_of_generation generation hdecrease) hroot hpositive
      hk hgenus htransverse hpolar hfirst hminors hdifferential i hfinite
        hintersection

end PointedMapGerm

end OnLeConjecture.DTwo
