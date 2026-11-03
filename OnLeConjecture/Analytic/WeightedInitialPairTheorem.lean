/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedIntersectionStrictAnyOrder
public import OnLeConjecture.Analytic.WeightedJacobianBound
public import OnLeConjecture.Analytic.UnitIntersection
public import OnLeConjecture.Polynomial.WeightedChartInjectivity

/-!
# The weighted initial-pair dichotomy for integral weights

Analytic weighted intersection estimates and the analytic Jacobian divisor
bound the chart polynomial of the initial Jacobian. Its leading coefficient,
ordinary analytic order, and target normalization then yield the degree
constraints. A vanishing initial Jacobian yields a power identity and a
strict intersection estimate.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

/-- A positive power identity with a nonconstant complex polynomial
provides a common root. -/
theorem exists_common_root_of_power_identity
    (P Q : ℂ[X]) (m k : ℕ) (hk : 0 < k) (hPdegree : 0 < P.natDegree)
    (c : ℂ) (hidentity : Q ^ m = C c * P ^ k) :
    ∃ z : ℂ, P.IsRoot z ∧ Q.IsRoot z := by
  obtain ⟨z, hz⟩ := Complex.exists_root (natDegree_pos_iff_degree_pos.mp hPdegree)
  refine ⟨z, hz, ?_⟩
  have heval := congrArg (fun R : ℂ[X] ↦ R.eval z) hidentity
  have hpower : Q.eval z ^ m = 0 := by
    simpa only [eval_pow, eval_mul, eval_C, hz.eq_zero, zero_pow hk.ne', mul_zero] using heval
  exact eq_zero_of_pow_eq_zero hpower

end OnLeConjecture.Polynomial

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

private theorem weighted_initial_pair_dichotomy_of_intersection_bounds
    (r L m M t : ℕ) (hr : 0 < r) (hL : 0 < L) (hm : 3 ≤ m) (hM : 0 < M)
    (f g : Germ 2) (hgOrdinary : g ∈ maximalIdeal 2 ^ m)
    (P₀ Q₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m))
    (hQ₀ : Q₀.IsWeightedHomogeneous ![r, 1] L) (hQ₀ne : Q₀ ≠ 0)
    (hPchart : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).Monic)
    (hPchartDegree : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).natDegree = m)
    (hPtail : f - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hgTail : g - coordinatePolynomialAlgHom 2 Q₀ ∈ weightedOrderIdeal r (L + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection f g)
    (hnormalized : ∀ (s : ℕ) (c : ℂ), 0 < s → c ≠ 0 →
      Q₀ ≠ MvPolynomial.C c * P₀ ^ s)
    (hweak : m * L ≤ PlaneCurve.intersectionMultiplicity f g hfinite)
    (hstrict : ∀ z : ℂ, MvPolynomial.eval ![z, 1] P₀ = 0 →
      MvPolynomial.eval ![z, 1] Q₀ = 0 →
      m * L < PlaneCurve.intersectionMultiplicity f g hfinite)
    (hnumber : PlaneCurve.intersectionMultiplicity f g hfinite + M ≤ 3 * t)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣ jacobian f g) :
    let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀
    let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q₀
    let Ω := OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (r : ℂ) p q
    let i := PlaneCurve.intersectionMultiplicity f g hfinite
    m * L ≤ i ∧
      (Ω ≠ 0 → Ω.natDegree ≤ m - 2 ∧
        t ≤ L + r * (m - 1 - Ω.natDegree) ∧ L = r * q.natDegree ∧ m + 1 ≤ q.natDegree) ∧
      (Ω = 0 → L = r * q.natDegree ∧
        (∃ c : ℂ, c ≠ 0 ∧ q ^ m = C c * p ^ q.natDegree) ∧ m * L < i) := by
  dsimp only
  let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀
  let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q₀
  let Ω := OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (r : ℂ) p q
  let i := PlaneCurve.intersectionMultiplicity f g hfinite
  change m * L ≤ i ∧ (Ω ≠ 0 → _) ∧ (Ω = 0 → _)
  have hq : q ≠ 0 :=
    OnLeConjecture.Polynomial.weighted_chart_ne_zero r L Q₀ hQ₀ hQ₀ne
  change m * L ≤ i at hweak
  have ht : 0 < t := by omega
  have hOmegaBound (hOmega : Ω ≠ 0) : r * Ω.natDegree + t + r ≤ r * m + L := by
    have hbound := weightedPairOmega_degree_bound_unrestricted r m L (t - 1)
      hr (by omega) P₀ Q₀ hP₀ hQ₀ hPchartDegree
      f g hPtail hgTail hdiv hOmega
    change r * Ω.natDegree + (t - 1) ≤ r * m + L - r - 1 at hbound
    have hlarge : r + 1 ≤ r * m + L := by nlinarith
    omega
  have hdegree : Ω.natDegree ≤ m - 2 := by
    by_cases hzero : Ω = 0
    · simp only [hzero, natDegree_zero]
      omega
    · have hbound := hOmegaBound hzero
      by_contra hnot
      have hdeg : m - 1 ≤ Ω.natDegree := by omega
      have hproduct := Nat.mul_le_mul_left r hdeg
      have hmPred : r * (m - 1) + r = r * m := by
        nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ m)]
      have htL : t ≤ L := by nlinarith
      change i + M ≤ 3 * t at hnumber
      nlinarith
  have hweightComplex :=
    OnLeConjecture.Polynomial.ell_eq_alpha_mul_natDegree_of_weightedPairOmega_degree
      m (L : ℂ) (r : ℂ) p q (by omega) hPchart hPchartDegree hq hdegree
  have hweight : L = r * q.natDegree := by exact_mod_cast hweightComplex
  have hqLower : m ≤ q.natDegree := maximalIdeal_order_le_weighted_chart_degree
    r m q.natDegree hr g hgOrdinary Q₀ (by simpa only [hweight] using hQ₀) hQ₀ne rfl
      (by simpa only [hweight] using hgTail)
  have hnormalizedChart : ∀ c : ℂ, q ≠ C c * p := by
    intro c heq
    have hc : c ≠ 0 := by
      intro hzero
      apply hq
      simpa only [hzero, map_zero, zero_mul] using heq
    have hqDegree : q.natDegree = m := by
      rw [heq, natDegree_C_mul hc]
      exact hPchartDegree
    have hweights : L = r * m := by rw [hweight, hqDegree]
    apply hnormalized 1 c (by omega) hc
    simpa only [pow_one] using
      OnLeConjecture.Polynomial.eq_of_weighted_chart_eq r (r * m)
        Q₀ (MvPolynomial.C c * P₀) (by simpa only [hweights] using hQ₀)
        (hP₀.C_mul c) (by simpa only [map_mul, MvPolynomial.aeval_C, p, q,
          Polynomial.algebraMap_eq] using heq)
  have hqStrict : m + 1 ≤ q.natDegree :=
    (OnLeConjecture.Polynomial.weighted_initial_pair_degree_constraints
      m (L : ℂ) (r : ℂ) p q (by omega) (by exact_mod_cast hr.ne')
      hPchart hPchartDegree hqLower hdegree hnormalizedChart).2
  refine ⟨hweak, ?_, ?_⟩
  · intro hOmega
    refine ⟨hdegree, ?_, hweight, hqStrict⟩
    have hbound := hOmegaBound hOmega
    have heq : r * (m - 1 - Ω.natDegree) + r * Ω.natDegree + r = r * m := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (by omega : Ω.natDegree ≤ m - 1)]
      nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ m)]
    change t ≤ L + r * (m - 1 - Ω.natDegree)
    omega
  · intro hOmega
    obtain ⟨c, hc, hidentity⟩ :=
      OnLeConjecture.Polynomial.exists_power_identity_of_weightedPairOmega_eq_zero
        m (L : ℂ) (r : ℂ) p q (by omega) (by exact_mod_cast hr.ne')
        hPchart hPchartDegree hq hOmega
    refine ⟨hweight, ⟨c, hc, hidentity⟩, ?_⟩
    obtain ⟨z, hpRoot, hqRoot⟩ := OnLeConjecture.Polynomial.exists_common_root_of_power_identity
      p q m q.natDegree (by omega) (by rw [hPchartDegree]; omega) c hidentity
    apply hstrict z
    · exact (OnLeConjecture.Polynomial.eval_weighted_chart P₀ z).symm.trans hpRoot
    · exact (OnLeConjecture.Polynomial.eval_weighted_chart Q₀ z).symm.trans hqRoot

/-- The integral-weight initial-pair dichotomy from prepared analytic
data, ordinary order, target normalization, and the numerical and Jacobian
constraints. The analytic intersection estimates are derived, not assumed. -/
theorem weighted_initial_pair_dichotomy
    (r L m M t : ℕ) (hr : 0 < r) (hL : 0 < L) (hm : 3 ≤ m) (hM : 0 < M)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (g : Germ 2) (hgOrdinary : g ∈ maximalIdeal 2 ^ m)
    (P₀ Q₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m))
    (hQ₀ : Q₀.IsWeightedHomogeneous ![r, 1] L) (hQ₀ne : Q₀ ≠ 0)
    (hPchart : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).Monic)
    (hPchartDegree : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).natDegree = m)
    (hPtail : firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hgTail : g - coordinatePolynomialAlgHom 2 Q₀ ∈ weightedOrderIdeal r (L + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) g)
    (hnormalized : ∀ (s : ℕ) (c : ℂ), 0 < s → c ≠ 0 →
      Q₀ ≠ MvPolynomial.C c * P₀ ^ s)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (firstCoordinatePolynomialEvaluation P) g hfinite + M ≤ 3 * t)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (firstCoordinatePolynomialEvaluation P) g) :
    let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀
    let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q₀
    let Ω := OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (r : ℂ) p q
    let i := PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P) g hfinite
    m * L ≤ i ∧
      (Ω ≠ 0 → Ω.natDegree ≤ m - 2 ∧
        t ≤ L + r * (m - 1 - Ω.natDegree) ∧ L = r * q.natDegree ∧ m + 1 ≤ q.natDegree) ∧
      (Ω = 0 → L = r * q.natDegree ∧
        (∃ c : ℂ, c ≠ 0 ∧ q ^ m = C c * p ^ q.natDegree) ∧ m * L < i) := by
  have hg : g ∈ weightedOrderIdeal r L := by
    have hsum := (weightedOrderIdeal r L).add_mem
      (weightedOrderIdeal_antitone r L (L + 1) hr (by omega) hgTail)
      (coordinatePolynomial_mem_weightedOrderIdeal r L hr hQ₀)
    simpa only [sub_add_cancel] using hsum
  have hP₀ne : P₀ ≠ 0 := by
    intro hzero
    apply hPchart.ne_zero
    simp [hzero]
  apply weighted_initial_pair_dichotomy_of_intersection_bounds
    r L m M t hr hL hm hM (firstCoordinatePolynomialEvaluation P) g hgOrdinary
    P₀ Q₀ hP₀ hQ₀ hQ₀ne hPchart hPchartDegree hPtail hgTail hfinite hnormalized
  · exact weighted_intersection_lower_bound_any_order
      r L m hr (by omega) P hP hPm hcoeff g hg hfinite
  · intro z hpRoot hqRoot
    exact weighted_intersection_strict_lower_bound_any_order
      r L m hr (by omega) P hP hPm hcoeff g P₀ Q₀ hP₀ hP₀ne hQ₀
      hPtail hgTail hfinite z hpRoot hqRoot
  · exact hnumber
  · exact hdiv

/-- The initial-pair dichotomy retains the analytic preparation unit.
The monic chart normalization concerns the actual first initial form, and
the Jacobian divisor remains a hypothesis on the actual first germ. -/
theorem weighted_initial_pair_unit_dichotomy
    (r L m M t : ℕ) (hr : 0 < r) (hL : 0 < L) (hm : 3 ≤ m) (hM : 0 < M)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (U g : Germ 2) (hU : IsUnit U) (hgOrdinary : g ∈ maximalIdeal 2 ^ m)
    (P₀ Q₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m))
    (hQ₀ : Q₀.IsWeightedHomogeneous ![r, 1] L) (hQ₀ne : Q₀ ≠ 0)
    (hPchart : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).Monic)
    (hPchartDegree : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).natDegree = m)
    (hPtail : U * firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hgTail : g - coordinatePolynomialAlgHom 2 Q₀ ∈ weightedOrderIdeal r (L + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) g)
    (hnormalized : ∀ (s : ℕ) (c : ℂ), 0 < s → c ≠ 0 →
      Q₀ ≠ MvPolynomial.C c * P₀ ^ s)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) g hfinite + M ≤ 3 * t)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (U * firstCoordinatePolynomialEvaluation P) g) :
    let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀
    let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q₀
    let Ω := OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (r : ℂ) p q
    let i := PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) g hfinite
    m * L ≤ i ∧
      (Ω ≠ 0 → Ω.natDegree ≤ m - 2 ∧
        t ≤ L + r * (m - 1 - Ω.natDegree) ∧ L = r * q.natDegree ∧ m + 1 ≤ q.natDegree) ∧
      (Ω = 0 → L = r * q.natDegree ∧
        (∃ c : ℂ, c ≠ 0 ∧ q ^ m = C c * p ^ q.natDegree) ∧ m * L < i) := by
  have hg : g ∈ weightedOrderIdeal r L := by
    have hsum := (weightedOrderIdeal r L).add_mem
      (weightedOrderIdeal_antitone r L (L + 1) hr (by omega) hgTail)
      (coordinatePolynomial_mem_weightedOrderIdeal r L hr hQ₀)
    simpa only [sub_add_cancel] using hsum
  have hP₀ne : P₀ ≠ 0 := by
    intro hzero
    apply hPchart.ne_zero
    simp [hzero]
  apply weighted_initial_pair_dichotomy_of_intersection_bounds
    r L m M t hr hL hm hM (U * firstCoordinatePolynomialEvaluation P) g hgOrdinary
    P₀ Q₀ hP₀ hQ₀ hQ₀ne hPchart hPchartDegree hPtail hgTail hfinite hnormalized
  · exact weighted_intersection_unit_lower_bound_any_order
      r L m hr (by omega) P hP hPm hcoeff U g hU hg hfinite
  · intro z hpRoot hqRoot
    exact weighted_intersection_unit_strict_lower_bound_any_order
      r L m hr (by omega) P hP hPm hcoeff U g hU P₀ Q₀ hP₀ hP₀ne hQ₀
      hPtail hgTail hfinite z hpRoot hqRoot
  · exact hnumber
  · exact hdiv

end OnLeConjecture.Analytic.Germ
