/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RamifiedPreparedPairTransport
public import OnLeConjecture.Analytic.WeierstrassNewtonWeight

/-!
# The prepared initial-pair lemma at a rational Newton weight

The substitution `(x,y) ↦ (x,y^s)` transports the actual analytic pair,
its intersection number, and its Jacobian divisor. The correction in the
ramified pair descends to a polynomial in the original first germ. The
bounds are written with denominators cleared: the rational weights are
`alpha = r/s` and `ell = L/s`.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Constructed initial forms and a descending target correction for a
prepared pair after ramification. Every numerical bound uses the original
intersection number and the specified ramification denominator. -/
structure RationalPreparedWeightedPair
    (s r m t : ℕ) (hs : 0 < s) (P : Polynomial (Germ 1)) (U u : Germ 2)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u) where
  correction : ℂ[X]
  degree : ℕ
  firstInitial : MvPolynomial (Fin 2) ℂ
  secondInitial : MvPolynomial (Fin 2) ℂ
  scalar : ℂ
  scalar_eq : scalar = (valueRingHom 2 U)⁻¹
  scalar_ne : scalar ≠ 0
  correction_zero : correction.coeff 0 = 0
  degree_pos : 0 < degree
  first_ne : firstInitial ≠ 0
  first_homogeneous : firstInitial.IsWeightedHomogeneous ![r, 1] (r * m)
  first_chart_monic : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) firstInitial).Monic
  first_chart_degree :
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) firstInitial).natDegree = m
  first_tail : constRingHom 2 scalar * (secondCoordinatePowerGerm s hs).pullbackRingHom
      (U * firstCoordinatePolynomialEvaluation P) - coordinatePolynomialAlgHom 2 firstInitial ∈
        weightedOrderIdeal r (r * m + 1)
  first_zero_coefficient : ∀ j, P.coeff j = 0 →
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) firstInitial).coeff j = 0
  first_sharp_coefficient : ∀ j,
    s • vanishingOrder (P.coeff j) = ((r * (m - j) : ℕ) : ℕ∞) →
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) firstInitial).coeff j ≠ 0
  second_ne : secondInitial ≠ 0
  second_homogeneous : secondInitial.IsWeightedHomogeneous ![r, 1] degree
  original_order : u - Polynomial.aeval (U * firstCoordinatePolynomialEvaluation P) correction ∈
    maximalIdeal 2 ^ m
  second_order : (secondCoordinatePowerGerm s hs).pullbackRingHom
      (u - Polynomial.aeval (U * firstCoordinatePolynomialEvaluation P) correction) ∈
        weightedOrderIdeal r degree
  second_not_next : (secondCoordinatePowerGerm s hs).pullbackRingHom
      (u - Polynomial.aeval (U * firstCoordinatePolynomialEvaluation P) correction) ∉
        weightedOrderIdeal r (degree + 1)
  second_tail : (secondCoordinatePowerGerm s hs).pullbackRingHom
      (u - Polynomial.aeval (U * firstCoordinatePolynomialEvaluation P) correction) -
        coordinatePolynomialAlgHom 2 secondInitial ∈ weightedOrderIdeal r (degree + 1)
  normalized : ∀ (k : ℕ) (c : ℂ), 0 < k → c ≠ 0 →
    secondInitial ≠ MvPolynomial.C c * firstInitial ^ k
  original_ideal :
    PlaneCurve.pairIdeal (U * firstCoordinatePolynomialEvaluation P)
      (u - Polynomial.aeval (U * firstCoordinatePolynomialEvaluation P) correction) =
    PlaneCurve.pairIdeal (U * firstCoordinatePolynomialEvaluation P) u
  original_jacobian :
    jacobian (U * firstCoordinatePolynomialEvaluation P)
      (u - Polynomial.aeval (U * firstCoordinatePolynomialEvaluation P) correction) =
    jacobian (U * firstCoordinatePolynomialEvaluation P) u
  original_intersection :
    ∃ hfinite' : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P)
        (u - Polynomial.aeval (U * firstCoordinatePolynomialEvaluation P) correction),
      PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P)
        (u - Polynomial.aeval (U * firstCoordinatePolynomialEvaluation P) correction) hfinite' =
      PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite
  lower_bound : m * degree ≤
    s * PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u hfinite
  nonzero_omega :
    let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) firstInitial
    let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) secondInitial
    let Ω := OnLeConjecture.Polynomial.weightedPairOmega m (degree : ℂ) (r : ℂ) p q
    Ω ≠ 0 → Ω.natDegree ≤ m - 2 ∧ s * t ≤ degree + r * (m - 1 - Ω.natDegree) ∧
      degree = r * q.natDegree ∧ m + 1 ≤ q.natDegree
  zero_omega :
    let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) firstInitial
    let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) secondInitial
    let Ω := OnLeConjecture.Polynomial.weightedPairOmega m (degree : ℂ) (r : ℂ) p q
    Ω = 0 → degree = r * q.natDegree ∧
      (∃ c : ℂ, c ≠ 0 ∧ q ^ m = C c * p ^ q.natDegree) ∧
      m * degree < s * PlaneCurve.intersectionMultiplicity
        (U * firstCoordinatePolynomialEvaluation P) u hfinite

/-- Rational Newton coefficient bounds produce the actual ramified
initial-pair dichotomy. The target correction descends to the original
pair, whose ordinary order, ideal, Jacobian, and intersection are retained. -/
theorem exists_rational_prepared_weighted_pair
    (s r m M t : ℕ) (hs : 0 < s) (hr : 0 < r) (hm : 3 ≤ m) (hM : 0 < M)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hdist : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1)
    (horder : ∀ j, j < m →
      ((r * (m - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j))
    (U u : Germ 2) (hU : IsUnit U)
    (hfOrdinary : U * firstCoordinatePolynomialEvaluation P ∈ maximalIdeal 2 ^ m)
    (huOrdinary : u ∈ maximalIdeal 2 ^ m)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite + M ≤ 3 * t)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (U * firstCoordinatePolynomialEvaluation P) u) :
    Nonempty (RationalPreparedWeightedPair s r m t hs P U u hfinite) := by
  let φ := (secondCoordinatePowerGerm s hs).pullbackRingHom
  let ψ := (oneVariablePowerMapGerm s hs).pullbackRingHom
  let PR := P.map ψ
  let f := U * firstCoordinatePolynomialEvaluation P
  have hpoly : φ (firstCoordinatePolynomialEvaluation P) =
      firstCoordinatePolynomialEvaluation PR := secondCoordinatePowerGerm_pullback_polynomial s hs P
  have hf : φ f = φ U * firstCoordinatePolynomialEvaluation PR := by
    rw [map_mul, hpoly]
  have hPR : PR.Monic := hP.map ψ
  have hPRm : PR.natDegree = m := (hP.natDegree_map ψ).trans hPm
  have hPRcoeff := coefficient_mem_maximalIdeal_pow_after_ramification s r m hs P horder
  have hUR : IsUnit (φ U) := hU.map φ
  have huR : φ u ∈ maximalIdeal 2 ^ m :=
    PointedMapGerm.pullback_mem_maximalIdeal_pow (secondCoordinatePowerGerm s hs) huOrdinary
  obtain ⟨hfiniteR, hinterR⟩ := exists_finite_ramified_unit_intersection_eq
    s m hs (by omega) P hP hPm hdist U u hU hfinite
  have hfinitePR : PlaneCurve.HasFiniteIntersection (φ U * firstCoordinatePolynomialEvaluation PR)
      (φ u) := by rwa [hf] at hfiniteR
  have hinterPR : PlaneCurve.intersectionMultiplicity
      (φ U * firstCoordinatePolynomialEvaluation PR) (φ u) hfinitePR =
      s * PlaneCurve.intersectionMultiplicity f u hfinite := by
    convert hinterR using 1
    change Module.finrank ℂ _ = Module.finrank ℂ _
    rw [hf]
  have hnumberR : PlaneCurve.intersectionMultiplicity
      (φ U * firstCoordinatePolynomialEvaluation PR) (φ u) hfinitePR + s * M ≤ 3 * (s * t) := by
    rw [hinterPR]
    have hmul := Nat.mul_le_mul_left s hnumber
    nlinarith
  have ht : 0 < t := by omega
  have hdivR : coordinate (1 : Fin 2) ^ (s * t - 1) ∣
      jacobian (φ U * firstCoordinatePolynomialEvaluation PR) (φ u) := by
    rw [← hf]
    exact secondCoordinatePowerGerm_jacobian_divisor s t hs ht f u hdiv
  obtain ⟨c, V, p, L, P₀, Q₀, hcEq, hc, hVeq, hV, hVvalue, hP₀ne, hP₀,
      hPchart, hPdegree, _hbareTail, hFTail, hzero, hexact, hp, hL, hQ₀ne, hQ₀,
      _hgOrdinaryR, hgWeighted, hgNext, hgTail, hnormalized, _hidealR, _hidealMixed,
      _hJacR, _hJacMixed, _hinterG, hweak, hnonzero, hzeroOmega⟩ :=
    exists_prepared_weighted_initial_pair_dichotomy r m (s * M) (s * t) hr hm
      (Nat.mul_pos hs hM) PR hPR hPRm hPRcoeff (φ U) (φ u) hUR huR hfinitePR hnumberR hdivR
  let q := p.comp (C c * X)
  have hq : q.coeff 0 = 0 := polynomial_correction_constant_rescaling_zero p c hp
  have hF : V * firstCoordinatePolynomialEvaluation PR = constRingHom 2 c * φ f := by
    rw [hVeq, hf]
    ring
  have hdescent : φ (u - Polynomial.aeval f q) =
      φ u - Polynomial.aeval (V * firstCoordinatePolynomialEvaluation PR) p := by
    rw [map_sub, pointed_pullback_polynomial_aeval,
      polynomial_correction_constant_rescaling, hF]
  have hqOrdinary : Polynomial.aeval f q ∈ maximalIdeal 2 ^ m :=
    (show Ideal.span {f} ≤ maximalIdeal 2 ^ m from
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfOrdinary))
        (polynomial_aeval_mem_span_singleton f q hq)
  have hgOrdinary : u - Polynomial.aeval f q ∈ maximalIdeal 2 ^ m :=
    (maximalIdeal 2 ^ m).sub_mem huOrdinary hqOrdinary
  have hideal : PlaneCurve.pairIdeal f (u - Polynomial.aeval f q) = PlaneCurve.pairIdeal f u :=
    span_pair_sub_polynomial_aeval f u q hq
  have hfiniteG := hfinite.of_pairIdeal_eq hideal.symm
  have hinterG := PlaneCurve.intersectionMultiplicity_eq_of_pairIdeal_eq hfiniteG hfinite hideal
  refine ⟨{
    correction := q
    degree := L
    firstInitial := P₀
    secondInitial := Q₀
    scalar := c
    scalar_eq := ?_
    scalar_ne := hc
    correction_zero := hq
    degree_pos := hL
    first_ne := hP₀ne
    first_homogeneous := hP₀
    first_chart_monic := hPchart
    first_chart_degree := hPdegree
    first_tail := ?_
    first_zero_coefficient := ?_
    first_sharp_coefficient := ?_
    second_ne := hQ₀ne
    second_homogeneous := hQ₀
    original_order := hgOrdinary
    second_order := ?_
    second_not_next := ?_
    second_tail := ?_
    normalized := hnormalized
    original_ideal := hideal
    original_jacobian := jacobian_sub_polynomial_aeval f u q
    original_intersection := ⟨hfiniteG, hinterG⟩
    lower_bound := ?_
    nonzero_omega := hnonzero
    zero_omega := ?_ }⟩
  · simpa only [φ, PointedMapGerm.valueRingHom_pullback] using hcEq
  · rw [← hF]
    exact hFTail
  · intro j hj
    apply hzero j
    simp only [PR, Polynomial.coeff_map, hj, map_zero]
  · intro j hj
    exact hexact j (coefficient_vanishingOrder_after_ramification s r m j hs P hj)
  · rw [hdescent]
    exact hgWeighted
  · rw [hdescent]
    exact hgNext
  · rw [hdescent]
    exact hgTail
  · rwa [hinterPR] at hweak
  · dsimp only
    intro hOmega
    obtain ⟨hweight, hidentity, hstrict⟩ := hzeroOmega hOmega
    refine ⟨hweight, hidentity, ?_⟩
    rwa [hinterPR] at hstrict

/-- An attained lower-coefficient Newton bound prevents the constructed
first chart from being a pure power. -/
theorem RationalPreparedWeightedPair.first_chart_ne_X_pow
    {s r m t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r m t hs P U u hfinite)
    (hsharp : ∃ j, j < m ∧
      ((r * (m - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j)) :
    MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial ≠ X ^ m := by
  intro hpower
  obtain ⟨j, hj, horder⟩ := hsharp
  have hnonzero := data.first_sharp_coefficient j horder.symm
  rw [hpower, coeff_X_pow, if_neg (by omega : j ≠ m)] at hnonzero
  exact hnonzero rfl

/-- The minimum Newton slope is selected from the original analytic
coefficients, and the rational initial-pair lemma is proved for that
selected slope. No ramification exponent or initial form is assumed. -/
theorem exists_newton_prepared_weighted_pair
    (m A M t : ℕ) (hm : 3 ≤ m) (hA : 0 < A) (hM : 0 < M)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1 ^ (A * (m - j)))
    (hnonzero : ∃ j, j < m ∧ P.coeff j ≠ 0)
    (U u : Germ 2) (hU : IsUnit U) (huOrdinary : u ∈ maximalIdeal 2 ^ m)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite + M ≤ 3 * t)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (U * firstCoordinatePolynomialEvaluation P) u) :
    ∃ s r : ℕ, ∃ hs : 0 < s,
      s = m.factorial ∧ 0 < r ∧ s * A ≤ r ∧
      (∀ j, j < m → ((r * (m - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j)) ∧
      (∃ j, j < m ∧ P.coeff j ≠ 0 ∧
        ((r * (m - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j)) ∧
      Nonempty (RationalPreparedWeightedPair s r m t hs P U u hfinite) := by
  obtain ⟨s, r, hsEq, hs, hr, hAr, horder, hsharp⟩ :=
    exists_integer_newton_weight m A (by omega) hA P hcoeff hnonzero
  refine ⟨s, r, hs, hsEq, hr, hAr, horder, hsharp, ?_⟩
  have hcoeffAll : ∀ j, P.coeff j ∈ maximalIdeal 1 ^ (A * (m - j)) := by
    intro j
    by_cases hj : j < m
    · exact hcoeff j hj
    · simp [Nat.sub_eq_zero_of_le (by omega : m ≤ j)]
  have hPweighted := firstCoordinatePolynomialEvaluation_mem_weightedOrderIdeal A (A * m) hA P
    (by intro j; simpa only [Nat.mul_sub_left_distrib] using hcoeffAll j)
  have hPordinary : firstCoordinatePolynomialEvaluation P ∈ maximalIdeal 2 ^ m :=
    weightedOrderIdeal_mul_le_maximalIdeal_pow A m hA hPweighted
  have hfOrdinary : U * firstCoordinatePolynomialEvaluation P ∈ maximalIdeal 2 ^ m :=
    Ideal.mul_mem_left _ U hPordinary
  exact exists_rational_prepared_weighted_pair s r m M t hs hr hm hM P hP hPm
    (coeff_mem_maximalIdeal_of_weighted_bounds A m hA P hcoeff) horder
    U u hU hfOrdinary huOrdinary hfinite hnumber hdiv

/-- Squarefreeness of the prepared first germ supplies a nonzero lower
coefficient, so the Newton weight and the complete rational dichotomy are
constructed without that additional coefficient hypothesis. -/
theorem exists_newton_prepared_weighted_pair_of_squarefree
    (m A M t : ℕ) (hm : 3 ≤ m) (hA : 0 < A) (hM : 0 < M)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1 ^ (A * (m - j)))
    (U u : Germ 2) (hU : IsUnit U)
    (hsquarefree : Squarefree (U * firstCoordinatePolynomialEvaluation P))
    (huOrdinary : u ∈ maximalIdeal 2 ^ m)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite + M ≤ 3 * t)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (U * firstCoordinatePolynomialEvaluation P) u) :
    ∃ s r : ℕ, ∃ hs : 0 < s,
      s = m.factorial ∧ 0 < r ∧ s * A ≤ r ∧
      (∀ j, j < m → ((r * (m - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j)) ∧
      (∃ j, j < m ∧ P.coeff j ≠ 0 ∧
        ((r * (m - j) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff j)) ∧
      Nonempty (RationalPreparedWeightedPair s r m t hs P U u hfinite) := by
  exact exists_newton_prepared_weighted_pair m A M t hm hA hM P hP hPm hcoeff
    (exists_nonzero_lower_coefficient_of_squarefree_preparation
      m (by omega) P hP hPm U hsquarefree)
    U u hU huOrdinary hfinite hnumber hdiv

end OnLeConjecture.Analytic.Germ
