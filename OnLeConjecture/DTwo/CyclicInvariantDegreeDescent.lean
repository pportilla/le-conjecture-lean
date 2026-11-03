/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPreparedResidual
public import OnLeConjecture.DTwo.CyclicInvariantAnalyticPreparation
public import OnLeConjecture.Analytic.TwoWeightPolynomialSeparation

/-!
# Degree descent and positivity in the invariant cyclic branch

Membership in `ℂ[x,yᵏ]` gives the invariant polynomial, and coefficient
recovery determines its homogeneous degree. The maximal ideal condition
on the analytic residual factor makes this degree positive.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic MvPolynomial

/-- A nonzero invariant homogeneous polynomial has degree divisible by
`k`, and its invariant polynomial has the descended weights `(1,p)`. -/
theorem exists_cyclicInvariant_homogeneous_descent
    (k p E : ℕ) (hk : 0 < k) (Λ : MvPolynomial (Fin 2) ℂ)
    (hΛzero : Λ ≠ 0) (hΛ : Λ.IsWeightedHomogeneous ![k, p] E)
    (hinvariant : Λ ∈ cyclicInvariantAlgebra k) :
    ∃ N : ℕ, ∃ L : MvPolynomial (Fin 2) ℂ,
      L ≠ 0 ∧ L.IsWeightedHomogeneous ![1, p] N ∧ E = k * N ∧
      Λ = cyclicInvariantLift k L := by
  obtain ⟨L, hL⟩ := hinvariant
  change cyclicInvariantLift k L = Λ at hL
  have hLzero : L ≠ 0 := by
    intro h
    exact hΛzero (by simpa [cyclicInvariantLift, h] using hL.symm)
  have hweight (d : Fin 2 →₀ ℕ) (hd : coeff d L ≠ 0) :
      k * (d 0 + p * d 1) = E := by
    have hcoeff : coeff (Finsupp.single 0 (d 0) + Finsupp.single 1 (k * d 1)) Λ ≠ 0 := by
      rw [← hL]
      exact (OnLeConjecture.Polynomial.coeff_second_power_substitution k hk L d).trans_ne hd
    have hdegree := hΛ hcoeff
    have hdegree' : k * d 0 + p * (k * d 1) = E := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hdegree
    calc
      k * (d 0 + p * d 1) = k * d 0 + p * (k * d 1) := by ring
      _ = E := hdegree'
  obtain ⟨d, hd⟩ : ∃ d, coeff d L ≠ 0 := by
    by_contra! h
    apply hLzero
    ext e
    simpa using h e
  refine ⟨d 0 + p * d 1, L, hLzero, ?_, (hweight d hd).symm, hL.symm⟩
  intro e he
  have hdegree : e 0 + p * e 1 = d 0 + p * d 1 := by
    apply Nat.eq_of_mul_eq_mul_left hk
    exact (hweight e he).trans (hweight d hd).symm
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hdegree

/-- The initial weighted degree of `yᵏh`, for `h` in the maximal ideal,
is strictly larger than `pk`. -/
theorem cyclicResidual_initial_degree_gt
    (k p D : ℕ) (hk : 0 < k) (hp : 0 < p)
    (h : Germ 2) (hh : h ∈ Germ.maximalIdeal 2)
    (R : MvPolynomial (Fin 2) ℂ) (hRzero : R ≠ 0)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (htail : Germ.coordinate 1 ^ k * h - Germ.coordinatePolynomialAlgHom 2 R ∈
      Germ.twoWeightOrderIdeal k p (D + 1)) : p * k < D := by
  have hy : Germ.coordinate (1 : Fin 2) ^ k ∈ Germ.twoWeightOrderIdeal k p (p * k) := by
    simpa using Germ.monomial_mem_twoWeightOrderIdeal_of_threshold
      k p (p * k) 0 k hk hp (by simp)
  have hhweight : h ∈ Germ.twoWeightOrderIdeal k p 1 := by
    rwa [Germ.twoWeightOrderIdeal_one_eq_maximalIdeal k p hk hp]
  have hproduct := Germ.twoWeightOrderIdeal_mul_mem k p (p * k) 1 hk hp hy hhweight
  by_contra h
  have hle : D + 1 ≤ p * k + 1 := by omega
  have hlow := Germ.twoWeightOrderIdeal_antitone k p (D + 1) (p * k + 1) hk hp hle hproduct
  have hRmem : Germ.coordinatePolynomialAlgHom 2 R ∈ Germ.twoWeightOrderIdeal k p (D + 1) := by
    simpa only [sub_sub_cancel] using
      (Germ.twoWeightOrderIdeal k p (D + 1)).sub_mem hlow htail
  exact hRzero (Germ.eq_zero_of_isTwoWeightHomogeneous_coordinatePolynomial_mem_succ
    k p D hk hp hR hRmem)

/-- The invariant polynomial extracted from an analytic residual factor
has positive degree, without a separate degree hypothesis. -/
theorem exists_positive_cyclicInvariant_descent
    (k p D : ℕ) (hk : 0 < k) (hp : 0 < p)
    (h : Germ 2) (hh : h ∈ Germ.maximalIdeal 2)
    (R Λ : MvPolynomial (Fin 2) ℂ) (hRzero : R ≠ 0)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (htail : Germ.coordinate 1 ^ k * h - Germ.coordinatePolynomialAlgHom 2 R ∈
      Germ.twoWeightOrderIdeal k p (D + 1))
    (hfactor : R = X 1 ^ k * Λ) (hinvariant : Λ ∈ cyclicInvariantAlgebra k) :
    ∃ N₀ : ℕ, ∃ L : MvPolynomial (Fin 2) ℂ,
      0 < N₀ ∧ L ≠ 0 ∧ L.IsWeightedHomogeneous ![1, p] N₀ ∧
      D = k * (N₀ + p) ∧ Λ = cyclicInvariantLift k L ∧
      R = cyclicInvariantLift k (X 1 * L) := by
  have hD := cyclicResidual_initial_degree_gt k p D hk hp h hh R hRzero hR htail
  have hΛ := cyclicResidual_factor_homogeneous k p D R Λ hRzero hR hfactor
  obtain ⟨N₀, L, hLzero, hL, hdegree, hLeq⟩ :=
    exists_cyclicInvariant_homogeneous_descent k p (D - p * k) hk Λ hΛ.1 hΛ.2.2 hinvariant
  have hN₀ : 0 < N₀ := by
    by_contra h
    have hNzero : N₀ = 0 := by omega
    simp only [hNzero, mul_zero] at hdegree
    omega
  have hDdegree : D = k * (N₀ + p) := by
    have hDsum : D = p * k + k * N₀ := by omega
    rw [hDsum]
    ring
  refine ⟨N₀, L, hN₀, hLzero, hL, hDdegree, hLeq, ?_⟩
  rw [hfactor, hLeq]
  simp [cyclicInvariantLift]

/-- The pure odd analytic preparation follows from an invariant residual
initial form and the maximal ideal condition, with no descended polynomial
or positive degree supplied as a hypothesis. -/
theorem cyclicInvariant_analytic_preparation_of_residual
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p D : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (h : Germ 2) (hh : h ∈ Germ.maximalIdeal 2)
    (hH : g.1.component 2 = Germ.coordinate 1 ^ k * h)
    (R Λ : MvPolynomial (Fin 2) ℂ) (hRzero : R ≠ 0)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (htail : Germ.coordinate 1 ^ k * h - Germ.coordinatePolynomialAlgHom 2 R ∈
      Germ.twoWeightOrderIdeal k p (D + 1))
    (hbase : R ∉ Set.range (aeval (cyclicInitialPair k p (Germ.valueRingHom 2 β)) :
      MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ))
    (hfactor : R = X 1 ^ k * Λ) (hinvariant : Λ ∈ cyclicInvariantAlgebra k) :
    ∃ g' : PointedMapGerm 2 3, ∃ κ : ℂ, ∃ q₀ : ℕ,
      g.RightLeftEquivalent g' ∧ g'.HasInjectiveRepresentative ∧
      g'.1.component 0 = g.1.component 0 ∧ g'.1.component 1 = g.1.component 1 ∧
      κ ≠ 0 ∧ 0 < q₀ ∧
      g'.1.component 2 - Germ.coordinatePolynomialAlgHom 2
        (C κ * X 0 ^ (p + 2 * q₀)) ∈
          Germ.twoWeightOrderIdeal k p (k * (p + 2 * q₀) + 1) := by
  obtain ⟨N₀, L, hN₀, _, hL, hD, _, hRL⟩ :=
    exists_positive_cyclicInvariant_descent k p D hk (by omega) h hh
      R Λ hRzero hR htail hfactor hinvariant
  have hpairtail := cyclic_pair_strict_tails g.firstTwo k p hk hp β
    (by simpa using hP) (by simpa using hQ)
  have htriple : ∀ i, g.1.component i - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p (Germ.valueRingHom 2 β)
        (cyclicInvariantLift k (X 1 * L)) i) ∈
          Germ.twoWeightOrderIdeal k p (![2 * k, p * k, k * (N₀ + p)] i + 1) := by
    intro i
    fin_cases i
    · simpa [cyclicResidualPolynomialMap] using hpairtail 0
    · simpa [cyclicResidualPolynomialMap] using hpairtail 1
    · change g.1.component 2 - Germ.coordinatePolynomialAlgHom 2
        (cyclicInvariantLift k (X 1 * L)) ∈
          Germ.twoWeightOrderIdeal k p (k * (N₀ + p) + 1)
      rw [hH, ← hRL, ← hD]
      exact htail
  obtain ⟨g', κ, q₀, hequiv, hg', hzero, hone, hκ, hq₀, _, hthird⟩ :=
    cyclicInvariant_analytic_pure_odd_preparation g hg k p N₀ hk hodd hN₀
      (Germ.valueRingHom 2 β) hβ L hL (by rwa [← hRL]) htriple
  exact ⟨g', κ, q₀, hequiv, hg', hzero, hone, hκ, hq₀, hthird⟩

end OnLeConjecture.DTwo
