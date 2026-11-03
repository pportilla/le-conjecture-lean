/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RationalWeightedPairBounds
public import OnLeConjecture.Analytic.RamifiedWeightedIntersectionExact
public import OnLeConjecture.DThree.NewtonPolynomialCore

/-!
# The initial pair for a depressed cubic at a rational Newton weight

The initial forms are those constructed from the analytic prepared pair.
A lower coefficient attaining the Newton weight and the point-basis
inequalities force a nonzero constant Jacobian polynomial and second
chart degree four or five. No integrality of the Newton weight is used.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- A monic depressed polynomial of degree three has the stated cubic
expression. -/
theorem eq_cubic_of_monic_degree_three (p : ℂ[X])
    (hp : p.Monic) (hdegree : p.natDegree = 3) (hdepressed : p.coeff 2 = 0) :
    p = cubic (p.coeff 1) (p.coeff 0) := by
  ext j
  have htop : p.coeff 3 = 1 := by
    simpa only [hdegree] using hp.coeff_natDegree
  by_cases hj : j < 4
  · interval_cases j <;> simp [cubic, coeff_X_pow, hdepressed, htop]
  · have hlarge : 3 < j := by omega
    rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by simpa only [cubic_natDegree] using hlarge)]

end OnLeConjecture.DThree

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

/-- A nonzero constant weighted Jacobian polynomial excludes common roots
of the two chart polynomials. -/
theorem no_common_root_of_weightedPairOmega_constant
    (m : ℕ) (L r : ℂ) (p q : ℂ[X])
    (hne : weightedPairOmega m L r p q ≠ 0)
    (hdegree : (weightedPairOmega m L r p q).natDegree = 0) :
    ∀ z : ℂ, ¬ (p.eval z = 0 ∧ q.eval z = 0) := by
  intro z ⟨hp, hq⟩
  have hconstant := eq_C_of_natDegree_eq_zero hdegree
  have heval : (weightedPairOmega m L r p q).eval z = 0 := by
    simp [weightedPairOmega, hp, hq]
  rw [hconstant, eval_C] at heval
  exact hne (by rw [hconstant, heval, map_zero])

/-- A nonzero constant weighted Jacobian polynomial also excludes repeated
roots of its first chart polynomial. -/
theorem squarefree_of_weightedPairOmega_constant
    (m : ℕ) (L r : ℂ) (p q : ℂ[X])
    (hne : weightedPairOmega m L r p q ≠ 0)
    (hdegree : (weightedPairOmega m L r p q).natDegree = 0) :
    Squarefree p := by
  apply PerfectField.separable_iff_squarefree.mp
  apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ p p.derivative).mpr
  intro z
  by_cases hp : aeval z p = 0
  swap
  · exact Or.inl hp
  right
  have hp' : p.eval z = 0 := by simpa using hp
  intro hd
  have hd' : p.derivative.eval z = 0 := by simpa using hd
  have hconstant := eq_C_of_natDegree_eq_zero hdegree
  have heval : (weightedPairOmega m L r p q).eval z = 0 := by
    simp [weightedPairOmega, hp', hd']
  rw [hconstant, eval_C] at heval
  exact hne (by rw [hconstant, heval, map_zero])

end OnLeConjecture.Polynomial

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- A depressed cubic with an attained lower Newton coefficient has
nonzero Omega for the constructed, normalized second initial form. -/
theorem RationalPreparedWeightedPair.cubic_omega_ne_zero
    {s r t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r 3 t hs P U u hfinite)
    (hr : 0 < r) (hdepressed : P.coeff 2 = 0)
    (hattained : ∃ j, j < 3 ∧
      ((r * (3 - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j)) :
    OnLeConjecture.Polynomial.weightedPairOmega 3 (data.degree : ℂ) (r : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial) ≠ 0 := by
  let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial
  let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial
  have hp : p = DThree.cubic (p.coeff 1) (p.coeff 0) :=
    DThree.eq_cubic_of_monic_degree_three p data.first_chart_monic data.first_chart_degree
      (data.first_zero_coefficient 2 hdepressed)
  have hlower : p.coeff 1 ≠ 0 ∨ p.coeff 0 ≠ 0 := by
    by_contra h
    push Not at h
    have hnot := data.first_chart_ne_X_pow hattained
    apply hnot
    change p = X ^ 3
    rw [hp, h.1, h.2]
    simp [DThree.cubic]
  obtain ⟨z, _, hz⟩ := DThree.exists_simple_root_cubic (p.coeff 1) (p.coeff 0) hlower
  have hq : q ≠ 0 := OnLeConjecture.Polynomial.weighted_chart_ne_zero
    r data.degree data.secondInitial data.second_homogeneous data.second_ne
  intro hzero
  have hzero' : DThree.newtonOmega data.degree r (p.coeff 1) (p.coeff 0) q = 0 := by
    simpa only [OnLeConjecture.Polynomial.weightedPairOmega, DThree.newtonOmega,
      Nat.cast_ofNat, ← hp] using hzero
  obtain ⟨k, c, hk, hc, hdegree, hpower⟩ :=
    DThree.exists_eq_cubic_power_of_newtonOmega_eq_zero
      data.degree r (p.coeff 1) (p.coeff 0) q z data.degree_pos hr hq hz hzero'
  apply data.normalized k c hk hc
  apply OnLeConjecture.Polynomial.eq_of_weighted_chart_eq r data.degree
    data.secondInitial (MvPolynomial.C c * data.firstInitial ^ k) data.second_homogeneous
  · have hhom := (data.first_homogeneous.pow k).C_mul c
    have hweight : k • (r * 3) = data.degree := by
      rw [hdegree]
      simp only [smul_eq_mul]
      ring
    simpa only [hweight] using hhom
  · simpa only [map_mul, map_pow, MvPolynomial.aeval_C, algebraMap_eq, ← hp] using hpower

/-- The point-basis inequalities force constant nonzero Omega and chart
degree four or five before any Milnor or polar identity is used. -/
theorem RationalPreparedWeightedPair.cubic_initial_constraints
    {s r t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r 3 t hs P U u hfinite)
    (hr : 0 < r) (hdepressed : P.coeff 2 = 0)
    (hattained : ∃ j, j < 3 ∧
      ((r * (3 - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j))
    (M A : ℕ)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite + M ≤ 3 * t)
    (hpoint : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite ≤ 2 * M + 3 * A)
    (hA : s * A ≤ r) :
    let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial
    let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial
    let Ω := OnLeConjecture.Polynomial.weightedPairOmega 3 (data.degree : ℂ) (r : ℂ) p q
    Ω ≠ 0 ∧ Ω.natDegree = 0 ∧ (q.natDegree = 4 ∨ q.natDegree = 5) ∧
      data.degree = r * q.natDegree ∧
      (∀ z : ℂ, ¬ (p.eval z = 0 ∧ q.eval z = 0)) ∧ Squarefree p := by
  dsimp only
  have hne := data.cubic_omega_ne_zero hr hdepressed hattained
  obtain ⟨hj, ht, hweight, hk⟩ := data.nonzero_omega hne
  let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial
  let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial
  let Ω := OnLeConjecture.Polynomial.weightedPairOmega 3 (data.degree : ℂ) (r : ℂ) p q
  let i := PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite
  have hi : i ≤ 2 * t + A := by dsimp only [i]; omega
  have hiS := Nat.mul_le_mul_left s hi
  have hlower := data.lower_bound
  change Ω.natDegree ≤ 3 - 2 at hj
  change s * t ≤ data.degree + r * (3 - 1 - Ω.natDegree) at ht
  change data.degree = r * q.natDegree at hweight
  change 3 + 1 ≤ q.natDegree at hk
  have hsum : Ω.natDegree + (3 - 1 - Ω.natDegree) = 2 := by omega
  have hconstraint : q.natDegree + 2 * Ω.natDegree ≤ 5 := by
    by_contra hnot
    have hlarge : 6 ≤ q.natDegree + 2 * Ω.natDegree := by omega
    have hmul := Nat.mul_le_mul_left r hlarge
    rw [hweight] at ht hlower
    change s * i ≤ s * (2 * t + A) at hiS
    change 3 * (r * q.natDegree) ≤ s * i at hlower
    nlinarith [mul_nonneg (show 0 ≤ r by omega) (show 0 ≤ Ω.natDegree by omega)]
  have hconstant : Ω.natDegree = 0 := by omega
  refine ⟨hne, hconstant, ?_, hweight, ?_, ?_⟩
  · change q.natDegree = 4 ∨ q.natDegree = 5
    omega
  · exact OnLeConjecture.Polynomial.no_common_root_of_weightedPairOmega_constant
      3 data.degree r p q hne hconstant
  · exact OnLeConjecture.Polynomial.squarefree_of_weightedPairOmega_constant
      3 data.degree r p q hne hconstant

/-- Coprimality and squarefreeness of the constructed initial charts give
both exact analytic intersection formulas on the original, unramified
surface. Only a constant, not the preparation unit, is removed from the
first germ when applying the initial-form formulas. -/
theorem RationalPreparedWeightedPair.cubic_intersection_equalities
    {s r t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r 3 t hs P U u hfinite)
    (hr : 0 < r) (hP : P.Monic) (hPm : P.natDegree = 3)
    (hdist : ∀ j, j < 3 → P.coeff j ∈ maximalIdeal 1)
    (horder : ∀ j, j < 3 →
      ((r * (3 - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j))
    (hU : IsUnit U) (hdepressed : P.coeff 2 = 0)
    (hattained : ∃ j, j < 3 ∧
      ((r * (3 - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j))
    (M A : ℕ)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite + M ≤ 3 * t)
    (hpoint : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite ≤ 2 * M + 3 * A)
    (hA : s * A ≤ r) :
    let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial
    s * PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite =
        3 * r * q.natDegree ∧
      ∃ hpolar : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P)
          (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)),
        s * PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P)
          (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)) hpolar =
            6 * r := by
  obtain ⟨_, _, _, hweight, hno, hsquarefree⟩ :=
    data.cubic_initial_constraints hr hdepressed hattained M A hnumber hpoint hA
  let f := U * firstCoordinatePolynomialEvaluation P
  let g := u - Polynomial.aeval f data.correction
  let V := constRingHom 2 data.scalar * U
  have hc : IsUnit (constRingHom 2 data.scalar) :=
    (isUnit_iff_ne_zero.mpr data.scalar_ne).map (constRingHom 2)
  have hV : IsUnit V := hc.mul hU
  have hVf : V * firstCoordinatePolynomialEvaluation P = constRingHom 2 data.scalar * f := by
    simp only [V, f, mul_assoc]
  have htail : (secondCoordinatePowerGerm s hs).pullbackRingHom
      (V * firstCoordinatePolynomialEvaluation P) - coordinatePolynomialAlgHom 2 data.firstInitial ∈
        weightedOrderIdeal r (r * 3 + 1) := by
    simpa only [V, map_mul, PointedMapGerm.pullback_constRingHom, mul_assoc] using data.first_tail
  have hno' : ∀ z : ℂ, ¬ (MvPolynomial.eval ![z, 1] data.firstInitial = 0 ∧
      MvPolynomial.eval ![z, 1] data.secondInitial = 0) := by
    intro z
    simpa only [OnLeConjecture.Polynomial.eval_weighted_chart] using hno z
  obtain ⟨hfiniteV, hinterV⟩ := rational_weighted_intersection_eq_of_no_common_initial_root
    s r data.degree 3 hs hr (by omega) P hP hPm hdist horder V g hV
    data.firstInitial data.secondInitial data.first_homogeneous data.first_ne
    data.second_homogeneous htail data.second_tail hno'
  obtain ⟨hfiniteG, hinterG⟩ := data.original_intersection
  have hideal : PlaneCurve.pairIdeal (V * firstCoordinatePolynomialEvaluation P) g =
      PlaneCurve.pairIdeal f g := by
    rw [hVf, PlaneCurve.pairIdeal_unit_mul_left _ _ _ hc]
  have hinterSame : PlaneCurve.intersectionMultiplicity
      (V * firstCoordinatePolynomialEvaluation P) g hfiniteV =
        PlaneCurve.intersectionMultiplicity f g hfiniteG := by
    change Module.finrank ℂ _ = Module.finrank ℂ _
    rw [hideal]
  rw [hinterSame, hinterG] at hinterV
  refine ⟨?_, ?_⟩
  · rw [hinterV, hweight]
    ring
  · obtain ⟨hpolarV, hpolarEq⟩ :=
      rational_weighted_intersection_first_derivative_eq_of_squarefree_chart
        s r 3 hs hr (by omega) P hP hPm hdist horder V hV data.firstInitial
        data.first_homogeneous data.first_ne htail hsquarefree
    have hpolarIdeal : PlaneCurve.pairIdeal (V * firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (V * firstCoordinatePolynomialEvaluation P)) =
          PlaneCurve.pairIdeal f (partialDerivative (0 : Fin 2) f) := by
      rw [hVf, partialDerivative_mul, partialDerivative_const, zero_mul, zero_add,
        PlaneCurve.pairIdeal_unit_mul_left _ _ _ hc, PlaneCurve.pairIdeal_comm,
        PlaneCurve.pairIdeal_unit_mul_left _ _ _ hc, PlaneCurve.pairIdeal_comm]
    have hpolar : PlaneCurve.HasFiniteIntersection f (partialDerivative (0 : Fin 2) f) := by
      rw [PlaneCurve.HasFiniteIntersection, ← hpolarIdeal]
      exact hpolarV
    refine ⟨hpolar, ?_⟩
    have hpolarSame : PlaneCurve.intersectionMultiplicity
        (V * firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (V * firstCoordinatePolynomialEvaluation P)) hpolarV =
          PlaneCurve.intersectionMultiplicity f (partialDerivative (0 : Fin 2) f) hpolar := by
      change Module.finrank ℂ _ = Module.finrank ℂ _
      rw [hpolarIdeal]
    rw [hpolarSame] at hpolarEq
    change s * PlaneCurve.intersectionMultiplicity f (partialDerivative 0 f) hpolar = 6 * r
    rw [hpolarEq]
    omega

/-- Conclusions for the constructed cubic initial forms. The two local
intersection numbers refer to the original analytic germs, and their
formulas use the rational weight `r/s`. -/
structure RationalCubicInitialProperties
    {s r t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r 3 t hs P U u hfinite) : Prop where
  omega_ne : OnLeConjecture.Polynomial.weightedPairOmega 3 (data.degree : ℂ) (r : ℂ)
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial) ≠ 0
  omega_degree : (OnLeConjecture.Polynomial.weightedPairOmega 3 (data.degree : ℂ) (r : ℂ)
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial)).natDegree = 0
  chart_degree : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree = 4 ∨
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree = 5
  weight_eq : data.degree =
    r * (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree
  no_common_root : ∀ z : ℂ, ¬ (MvPolynomial.eval ![z, 1] data.firstInitial = 0 ∧
    MvPolynomial.eval ![z, 1] data.secondInitial = 0)
  first_squarefree : Squarefree (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
  intersection_eq :
    (PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite : ℚ) =
      3 * ((MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree : ℚ) *
        ((r : ℚ) / s)
  polar_eq : ∃ hpolar : PlaneCurve.HasFiniteIntersection
      (U * firstCoordinatePolynomialEvaluation P)
      (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)),
    (PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P)
      (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)) hpolar : ℚ) =
        6 * ((r : ℚ) / s)

/-- The conclusions use rational division of the proved ramified
intersection identities, without any integrality assumption on `r/s`. -/
theorem RationalPreparedWeightedPair.cubic_properties
    {s r t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r 3 t hs P U u hfinite)
    (hr : 0 < r) (hP : P.Monic) (hPm : P.natDegree = 3)
    (hdist : ∀ j, j < 3 → P.coeff j ∈ maximalIdeal 1)
    (horder : ∀ j, j < 3 →
      ((r * (3 - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j))
    (hU : IsUnit U) (hdepressed : P.coeff 2 = 0)
    (hattained : ∃ j, j < 3 ∧
      ((r * (3 - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j))
    (M A : ℕ)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite + M ≤ 3 * t)
    (hpoint : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite ≤ 2 * M + 3 * A)
    (hA : s * A ≤ r) : RationalCubicInitialProperties data := by
  obtain ⟨hne, hconstant, hk, hweight, hno, hsquarefree⟩ :=
    data.cubic_initial_constraints hr hdepressed hattained M A hnumber hpoint hA
  obtain ⟨hinter, hpolar, hpolarEq⟩ := data.cubic_intersection_equalities
    hr hP hPm hdist horder hU hdepressed hattained M A hnumber hpoint hA
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  refine ⟨hne, hconstant, hk, hweight, ?_, hsquarefree, ?_, hpolar, ?_⟩
  · intro z
    simpa only [OnLeConjecture.Polynomial.eval_weighted_chart] using hno z
  · have hcast : (s : ℚ) * PlaneCurve.intersectionMultiplicity
        (U * firstCoordinatePolynomialEvaluation P) u hfinite =
      3 * (r : ℚ) *
        (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree := by
      exact_mod_cast hinter
    field_simp
    nlinarith
  · have hcast : (s : ℚ) * PlaneCurve.intersectionMultiplicity
        (U * firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)) hpolar =
          6 * (r : ℚ) := by exact_mod_cast hpolarEq
    field_simp
    nlinarith

/-- Original coefficient bounds, squarefreeness, the two point-basis
inequalities, and the analytic Jacobian divisor construct the cubic
initial-pair conclusions. The initial forms, Newton numerator, and target
correction are outputs rather than assumptions. -/
theorem exists_rational_cubic_initial_pair
    (A M t : ℕ) (hA : 0 < A) (hM : 0 < M)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = 3)
    (hcoeff : ∀ j, j < 3 → P.coeff j ∈ maximalIdeal 1 ^ (A * (3 - j)))
    (hdepressed : P.coeff 2 = 0) (U u : Germ 2) (hU : IsUnit U)
    (hsquarefree : Squarefree (U * firstCoordinatePolynomialEvaluation P))
    (huOrdinary : u ∈ maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite + M ≤ 3 * t)
    (hpoint : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite ≤ 2 * M + 3 * A)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (U * firstCoordinatePolynomialEvaluation P) u) :
    ∃ s r : ℕ, ∃ hs : 0 < s, s = 6 ∧ 0 < r ∧ s * A ≤ r ∧
      ∃ data : RationalPreparedWeightedPair s r 3 t hs P U u hfinite,
        RationalCubicInitialProperties data := by
  obtain ⟨s, r, hs, hsEq, hr, hAr, horder, hsharp, ⟨data⟩⟩ :=
    exists_newton_prepared_weighted_pair_of_squarefree 3 A M t (by omega) hA hM
      P hP hPm hcoeff U u hU hsquarefree huOrdinary hfinite hnumber hdiv
  refine ⟨s, r, hs, by simpa only [show Nat.factorial 3 = 6 by decide] using hsEq,
    hr, hAr, data, ?_⟩
  apply data.cubic_properties hr hP hPm
    (coeff_mem_maximalIdeal_of_weighted_bounds A 3 hA P hcoeff) horder hU hdepressed
    _ M A hnumber hpoint hAr
  obtain ⟨j, hj, _, heq⟩ := hsharp
  exact ⟨j, hj, heq⟩

end OnLeConjecture.Analytic.Germ
