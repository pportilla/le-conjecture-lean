/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ConstructedCubicSharpPair
public import OnLeConjecture.DThree.PreparedAnalyticExclusion
public import OnLeConjecture.Analytic.SecondCoordinatePolynomialSubtraction
public import OnLeConjecture.Analytic.PlaneFiniteFiberCriterion

/-!
# Cubic analytic exclusion from a matched point basis

The Newton weight, the exact quartic second order, and the polynomial
target correction are constructed from the prepared cubic and the matched
point basis. The invertible correction preserves the finite pair and all
three Jacobian divisors, so the analytic cubic-quartic exclusion applies.

The hypotheses retain the prepared equation in the straightened coordinates,
the matched analytic proximity data, and the intersection point-basis
identity. Their construction from an arbitrary map germ is a separate task.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A prepared cubic with a matched point basis, the numerical reduction
inequality, and the three Jacobian divisors excludes injectivity. Neither
a Newton weight nor a normalized second or third initial form is assumed. -/
theorem PointedMapGerm.not_hasInjectiveRepresentative_of_cubic_matched_point_basis
    (g : PointedMapGerm 2 3)
    {N : ℕ} (c : AnalyticPointBasis N) (d : AnalyticProximityData c)
    (hcoordinates : DFour.TopOrderChartCompatibility d) (hroot : c.multiplicity c.root = 3)
    (P : _root_.Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = 3)
    (hdepressed : P.coeff 2 = 0) (U : Germ 2) (hU : IsUnit U)
    (hfirst : g.1.component 0 = U * Germ.firstCoordinatePolynomialEvaluation P)
    (hprepared : d.topOrderChain.straightenedGerm 0 =
      Germ.firstCoordinatePolynomialEvaluation P * U)
    (hsquarefree : Squarefree (g.1.component 0))
    (hsecondOrdinary : g.1.component 1 ∈ Germ.maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hintersection : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (t : ℕ)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (t - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (t - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (t - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  have hfiniteP : PlaneCurve.HasFiniteIntersection
      (U * Germ.firstCoordinatePolynomialEvaluation P) (g.1.component 1) := by
    simpa only [hfirst] using hfinite
  obtain ⟨_hnoTwo, _hM, ht, _hi, hcoeffOne, hcoeffZero, hsharp,
      p, hp, hquartic, hquarticExact, hideal, _hjacobian⟩ :=
    Germ.exists_cubic_sharp_correction_of_matched_point_basis c d hcoordinates hroot
      P hP hPm hdepressed U (g.1.component 1) hU hprepared
      (by simpa only [hfirst] using hsquarefree) hsecondOrdinary hfiniteP
      (by simpa only [hfirst] using hintersection) t
      (by simpa only [hfirst] using hnumber) (by simpa only [hfirst] using hdivZeroOne)
  obtain ⟨h, hequivalent, hzero, hone, htwo⟩ :=
    g.exists_target_secondPolynomialSubtraction p hp
  have hfiniteH : h.firstTwo.IsFiniteAtOrigin := by
    apply PointedMapGerm.finiteFiberCriterionAtOrigin_two 2 h.firstTwo
    change Module.Finite ℂ (Germ 2 ⧸ h.firstTwo.1.coordinateIdeal)
    rw [PlaneCurve.coordinateIdeal_eq_pairIdeal, PointedMapGerm.firstTwo_component,
      PointedMapGerm.firstTwo_component]
    change PlaneCurve.HasFiniteIntersection (h.1.component 0) (h.1.component 1)
    rw [hzero, hone, hfirst]
    exact hfiniteP.of_pairIdeal_eq hideal.symm
  have hfirstH : h.1.component 0 =
      (Germ.coordinate (0 : Fin 2) ^ 3 +
        Germ.planeCoefficientExtension (P.coeff 1) * Germ.coordinate (0 : Fin 2) +
        Germ.planeCoefficientExtension (P.coeff 0)) * U := by
    calc
      h.1.component 0 = Germ.firstCoordinatePolynomialEvaluation P * U :=
        hzero.trans (hfirst.trans (mul_comm _ _))
      _ = _ := by
        rw [Germ.polynomialEvaluation_depressed_cubic P hP hPm hdepressed]
        rfl
  have hdivs := (PointedMapGerm.dvd_minors_of_secondPolynomialSubtraction_iff
    g h p hzero hone htwo (Germ.coordinate (1 : Fin 2) ^ (t - 1))).mpr
      ⟨hdivZeroOne, hdivZeroTwo, hdivOneTwo⟩
  rw [ht] at hdivs
  intro hg
  exact PointedMapGerm.preparedWeightedAnalyticTriple_not_hasInjectiveRepresentative
    h hfiniteH d.topOrderChain.length d.topOrderChain.length_pos (P.coeff 1) (P.coeff 0)
    U hfirstH hU hcoeffOne hcoeffZero hsharp
    (by simpa only [hone, hfirst] using hquartic)
    (by simpa only [hone, hfirst] using hquarticExact)
    hdivs.1 hdivs.2.1 hdivs.2.2 (hequivalent.hasInjectiveRepresentative hg)

end OnLeConjecture.DThree
