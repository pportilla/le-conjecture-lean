/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.WeightedCurveCollision
public import OnLeConjecture.DTwo.RamifiedOrbitCurve
public import OnLeConjecture.DTwo.RamifiedOrbitPlaneMapBridge

/-!
# Analytic noninjectivity of the ramified orbit model

The conic collision is lifted as an analytic curve after ramifying its
parameter. The point off the ramification axis is eliminated by its
invertible plane derivative. The third difference retains positive
finite order, so the original analytic weighted tails also collide.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic DThree

theorem ramifiedOrbit_curve_orderTails_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a r : ℕ) (ha : 0 < a)
    (R : OrbitSourceForm) (hR : R.IsHomogeneous r)
    (htail : ∀ i, g.1.component i - Germ.coordinatePolynomialAlgHom 2
      (ramifiedOrbitPolynomials a R i) ∈
        Germ.weightedOrderIdeal a (ramifiedOrbitDegrees a r i + 1))
    (first : ℂ → ℂ × ℂ) (second : ℂ → Fin 2 → ℂ)
    (hfirst : AnalyticAt ℂ first 0) (hsecond : AnalyticAt ℂ second 0)
    (hseparate : first 0 ≠ orbitPointOfFinTwo (second 0))
    (hsecondY : second 0 1 ≠ 0)
    (m : ℕ) (u : ℂ → ℂ) (hm : 0 < m) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hcurve : ∀ᶠ s in nhds 0,
      orbitPairInitialDifference (weightedPolynomialMap (ramifiedOrbitPolynomials a R))
        (first s, orbitPointOfFinTwo (second s)) = ![0, 0, s ^ m * u s]) :
    ¬ g.HasInjectiveRepresentative := by
  let initial := weightedPolynomialMap (ramifiedOrbitPolynomials a R)
  let v : Fin 2 → ℂ := ![initial (first 0) 0, initial (first 0) 1]
  let e := ramifiedOrbitNegativePointDerivativeEquiv a ha (second 0 0) (second 0 1) hsecondY
  have hq : (![second 0 0, second 0 1] : Fin 2 → ℂ) = second 0 := by
    ext i
    fin_cases i <;> rfl
  have hfun : (fun q : Fin 2 → ℂ =>
      ![initial (first 0) 0 - initial (orbitPointOfFinTwo q) 0,
        initial (first 0) 1 - initial (orbitPointOfFinTwo q) 1]) =
      fun q => v - ramifiedOrbitPlaneMap a q := by
    funext q
    rw [ramifiedOrbitPlaneMap_eq_firstTwo_weightedPolynomialMap a R q]
    ext i
    fin_cases i <;> rfl
  have hd : HasStrictFDerivAt (fun q : Fin 2 → ℂ =>
      ![initial (first 0) 0 - initial (orbitPointOfFinTwo q) 0,
        initial (first 0) 1 - initial (orbitPointOfFinTwo q) 1])
      e.toContinuousLinearMap (second 0) := by
    rw [hfun, ← hq]
    exact hasStrictFDerivAt_const_sub_ramifiedOrbitPlaneMap_equiv
      a ha v (second 0 0) (second 0 1) hsecondY
  exact weighted_curve_orderTails_not_hasInjectiveRepresentative g a ha
    (ramifiedOrbitDegrees a r) (ramifiedOrbitPolynomials a R)
    (ramifiedOrbitPolynomials_homogeneous a r R hR) htail first second hfirst hsecond
    hseparate m u hm hu hu0 hcurve e.toContinuousLinearMap hd
    ContinuousLinearMap.isInvertible_equiv

/-- Every homogeneous residual outside the orbit algebra and divisible by
the fourth power of the second variable gives an analytic collision after
the finite power substitution. All curve lifts and persistence data are
constructed from these polynomial hypotheses. -/
theorem ramifiedOrbit_orderTails_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a r : ℕ) (ha : 0 < a) (hr : 4 ≤ r)
    (R : OrbitSourceForm) (hR : R.IsHomogeneous r)
    (hdiv : orbitPolynomialLambda ℂ ^ 4 ∣ R)
    (hnotBase : R ∉ Set.range (orbitBaseToSource ℂ))
    (htail : ∀ i, g.1.component i - Germ.coordinatePolynomialAlgHom 2
      (ramifiedOrbitPolynomials a R i) ∈
        Germ.weightedOrderIdeal a (ramifiedOrbitDegrees a r i + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨_, delta, hdelta, hcertificate⟩ :=
    hasOrbitCollision_and_exists_certificate hR hr hdiv hnotBase
  obtain ⟨data⟩ := exists_orbitFiniteChartCollisionData hdelta hR hcertificate
  obtain ⟨first, second, m, u, hfirst, hsecond, hm, hu, hu0, hseparate, hsecondY, hcurve⟩ :=
    exists_ramifiedOrbitFiniteChartPair_finiteOrder_transverse a ha hdelta data
  exact ramifiedOrbit_curve_orderTails_not_hasInjectiveRepresentative g a r ha R hR
    htail first second hfirst hsecond hseparate hsecondY m u hm hu hu0 hcurve

end OnLeConjecture.DTwo
