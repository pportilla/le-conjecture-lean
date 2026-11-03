/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.ExtremeIdealPreservingElimination
public import OnLeConjecture.DTwo.ExtremeResidualDescent
public import OnLeConjecture.DTwo.RamifiedOrbitNoninjectivity

/-!
# Exclusion of the extreme prepared analytic form

Finite elimination and analytic rotation collisions produce the Fourier
decomposition of the residual. Its weighted degree gives two alternatives:
descent to the cubic orbit polynomial, or a pure second-coordinate power.
Both alternatives yield collisions of the original analytic germ.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem ramifiedOrbit_not_base_of_extreme_initial_not_base
    (a : ℕ) (S R : OrbitSourceForm) (hSR : ramifiedOrbitSubstitution a S = R)
    (hnot : R ∉ Set.range (MvPolynomial.aeval (extremeInitialPair a) :
      OrbitSourceForm →ₐ[ℂ] OrbitSourceForm)) :
    S ∉ Set.range (orbitBaseToSource ℂ) := by
  let q : OrbitBaseRing ℂ →ₐ[ℂ] OrbitSourceForm := MvPolynomial.aeval fun
    | OrbitBaseCoordinate.phi => MvPolynomial.X 0
    | OrbitBaseCoordinate.psi => MvPolynomial.X 1
  have hcomp : (MvPolynomial.aeval (extremeInitialPair a)).comp q =
      ramifiedOrbitBaseHom a := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [q, ramifiedOrbitBaseHom, orbitBaseToSource, extremeInitialPair,
      ramifiedOrbitSubstitution_phi, ramifiedOrbitSubstitution_psi]
  rintro ⟨P, hP⟩
  apply hnot
  refine ⟨q P, ?_⟩
  change ((MvPolynomial.aeval (extremeInitialPair a)).comp q) P = R
  rw [hcomp]
  change ramifiedOrbitSubstitution a (orbitBaseToSource ℂ P) = R
  rwa [hP]

/-- The extreme prepared form cannot be locally injective. The analytic
coefficients are arbitrary. Finiteness is the property of the original pair. -/
theorem extreme_prepared_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (hfinite : g.firstTwo.IsFiniteAtOrigin)
    (a : ℕ) (ha : 0 < a) (C₂ C₃ : Germ 2)
    (hP : g.1.component 0 = cyclicFirst (2 * a))
    (hQ : g.1.component 1 = extremeTheta (2 * a) + coordinate 1 ^ (4 * a) * C₂)
    (hZ : g.1.component 2 = coordinate 1 ^ (4 * a) * C₃) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  obtain ⟨f, D, R, _, hgf, _, _, _, hD, hRne, hR, hRdiv, hRbase, htail⟩ :=
    exists_extreme_ideal_preserving_residual g hg hfinite a ha C₂ C₃ hP hQ hZ
  have hf := hgf.hasInjectiveRepresentative hg
  obtain ⟨U, c, hU, hUhom, hRU⟩ := extremeResidual_fourier_of_injective f hf a D ha R hR htail
  by_cases hdegree : a ∣ D
  · obtain ⟨S, hS, hSdiv, hSR⟩ :=
      extreme_residual_homogeneous_descent a D ha R U c hR hU hRU hdegree hRdiv
    have hSbase := ramifiedOrbit_not_base_of_extreme_initial_not_base a S R hSR hRbase
    have hdegreeEq : a * (D / a) = D := Nat.mul_div_cancel' hdegree
    have hr : 4 ≤ D / a := (Nat.le_div_iff_mul_le ha).mpr hD
    have hmaps : ramifiedOrbitPolynomials a S = extremeResidualPolynomialMap a R := by
      funext i
      fin_cases i
      · simpa [ramifiedOrbitPolynomials, orbitInitialPolynomialMap,
          extremeResidualPolynomialMap] using ramifiedOrbitSubstitution_phi a
      · simpa [ramifiedOrbitPolynomials, orbitInitialPolynomialMap,
          extremeResidualPolynomialMap] using ramifiedOrbitSubstitution_psi a
      · exact hSR
    apply ramifiedOrbit_orderTails_not_hasInjectiveRepresentative f a (D / a) ha hr
      S hS hSdiv hSbase ?_ hf
    intro i
    rw [hmaps]
    simpa only [ramifiedOrbitDegrees, hdegreeEq] using htail i
  · have hmono := extreme_residual_eq_pure_power_of_degree_not_dvd
      a D R U c hU hUhom hRU hdegree
    have hc : c ≠ 0 := by
      intro hc
      apply hRne
      simp [hmono, hc]
    apply extremeMonomial_orderTails_not_hasInjectiveRepresentative f a D ha (by omega) c hc ?_ hf
    intro i
    simpa only [extremeMonomialPolynomials, extremeMonomialDegrees,
      extremeResidualPolynomialMap, hmono] using htail i

/-- The extreme common-Jacobian divisibility and actual intersection
number construct the prepared coordinates and hence exclude injectivity. -/
theorem extreme_jacobian_intersection_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a : ℕ) (ha : 0 < a)
    (hP : g.1.component 0 = cyclicFirst (2 * a))
    (hJQ : coordinate (1 : Fin 2) ^ (4 * a - 1) ∣
      jacobian (g.1.component 0) (g.1.component 1))
    (hJZ : coordinate (1 : Fin 2) ^ (4 * a - 1) ∣
      jacobian (g.1.component 0) (g.1.component 2))
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hinter : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite = 6 * a) :
    ¬ g.HasInjectiveRepresentative := by
  have hfour : 2 * (2 * a) = 4 * a := by omega
  have hsix : 3 * (2 * a) = 6 * a := by omega
  obtain ⟨f, C₂, C₃, hgf, hf0, hf1, hf2, hfinite', _⟩ :=
    exists_extreme_theta_preparation_with_finite_pair g (2 * a) (by omega) hP
      (by simpa only [hfour] using hJQ) (by simpa only [hfour] using hJZ)
      hfinite (by simpa only [hsix] using hinter)
  rw [hfour] at hf1 hf2
  intro hg
  exact extreme_prepared_not_hasInjectiveRepresentative f hfinite' a ha C₂ C₃ hf0 hf1 hf2
    (hgf.hasInjectiveRepresentative hg)

end OnLeConjecture.DTwo
