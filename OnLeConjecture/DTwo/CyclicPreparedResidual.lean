/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicResidualCollision
public import OnLeConjecture.DTwo.IdealPreservingCyclicElimination

/-!
# The cyclic residual polynomial after ideal preserving elimination

Analytic target subtraction preserves injectivity. Factoring the initial
remainder as `yᵏΛ` transfers the rotation differences to `Λ`, so the analytic
collision theorem yields the invariant-or-one-monomial alternative.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic

/-- Removing a coordinate power from a homogeneous polynomial subtracts
its degree. The original degree is at least the degree removed. -/
theorem cyclicResidual_factor_homogeneous (k p D : ℕ)
    (R Λ : MvPolynomial (Fin 2) ℂ) (hRzero : R ≠ 0)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hfactor : R = MvPolynomial.X 1 ^ k * Λ) :
    Λ ≠ 0 ∧ p * k ≤ D ∧ Λ.IsWeightedHomogeneous ![k, p] (D - p * k) := by
  have hΛ : Λ ≠ 0 := by
    intro hzero
    apply hRzero
    simp [hfactor, hzero]
  have hdegree (d : Fin 2 →₀ ℕ) (hd : MvPolynomial.coeff d Λ ≠ 0) :
      p * k + Finsupp.weight ![k, p] d = D := by
    have hc : MvPolynomial.coeff (Finsupp.single 1 k + d) R ≠ 0 := by
      simpa [hfactor, MvPolynomial.X_pow_eq_monomial] using hd
    simpa only [map_add, Finsupp.weight_single, Matrix.cons_val_one,
      Matrix.cons_val_zero, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm k p] using hR hc
  have hex : ∃ d, MvPolynomial.coeff d Λ ≠ 0 := by
    by_contra! hcoeff
    apply hΛ
    ext d
    simpa using hcoeff d
  obtain ⟨d, hd⟩ := hex
  refine ⟨hΛ, ?_, ?_⟩
  · have := hdegree d hd
    omega
  · intro e he
    have := hdegree e he
    omega

/-- On a `k`th root of unity, the factor `yᵏ` does not change the rotation
difference polynomial. -/
theorem cyclicRotationDifference_second_pow_mul
    (k : ℕ) (ζ : ℂ) (hζ : ζ ^ k = 1) (Λ : MvPolynomial (Fin 2) ℂ) :
    cyclicRotationDifference (MvPolynomial.X 1 ^ k * Λ) ζ =
      cyclicRotationDifference Λ ζ := by
  simp only [cyclicRotationDifference, map_mul, map_pow, MvPolynomial.aeval_X,
    Matrix.cons_val_one, Matrix.cons_val_zero, one_pow, one_mul]
  rw [← Polynomial.C_pow, hζ, Polynomial.C_1, one_mul]

/-- The quotient residual polynomial satisfies the Fourier alternative
when the analytic triple is injective. -/
theorem cyclicResidual_quotient_fourier_dichotomy_of_injective
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p D : ℕ) (hk : 0 < k) (hp : 0 < p) (c : ℂ) (hc : c ≠ 0)
    (R Λ : MvPolynomial (Fin 2) ℂ) (hRzero : R ≠ 0)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hfactor : R = MvPolynomial.X 1 ^ k * Λ)
    (htail : ∀ i, g.1.component i -
      Germ.coordinatePolynomialAlgHom 2 (cyclicResidualPolynomialMap k p c R i) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] i + 1)) :
    Λ ∈ cyclicInvariantAlgebra k ∨
      ∃ Λinv : MvPolynomial (Fin 2) ℂ, ∃ i j : ℕ, ∃ γ : ℂ,
        Λinv ∈ cyclicInvariantAlgebra k ∧
        Λinv.IsWeightedHomogeneous ![k, p] (D - p * k) ∧
        γ ≠ 0 ∧ ¬ k ∣ j ∧ k * i + p * j = D - p * k ∧
        Λ = Λinv + MvPolynomial.C γ * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j := by
  have hΛ := (cyclicResidual_factor_homogeneous k p D R Λ hRzero hR hfactor).2.2
  by_cases hinv : Λ ∈ cyclicInvariantAlgebra k
  · exact Or.inl hinv
  · apply Or.inr
    apply cyclic_residual_fourier_classification_of_no_nonzero_roots
      k p k (D - p * k) hp hk Λ hΛ hinv
    intro ζ hζ hnonzero s hs
    have heq : cyclicRotationDifference R ζ = cyclicRotationDifference Λ ζ := by
      rw [hfactor, cyclicRotationDifference_second_pow_mul k ζ hζ]
    exact cyclicResidual_no_nonzero_roots_of_injective g hg k p D hk hp c hc R hR htail
      ζ hζ (by rwa [heq]) s (by rwa [heq])

/-- Ideal preserving analytic elimination and repeated-root collision
persistence produce the precise Fourier alternative for the quotient `Λ`.
The nonmembership conclusion concerns the pair algebra, not the larger
invariant algebra. -/
theorem cyclic_injective_triple_prepared_residual
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (h : Germ 2) (hh : h ∈ Germ.maximalIdeal 2)
    (hH : g.1.component 2 = Germ.coordinate 1 ^ k * h) :
    ∃ D : ℕ, ∃ Ψ h' : Germ 2, ∃ R Λ : MvPolynomial (Fin 2) ℂ,
      Ψ ∈ Germ.maximalIdeal 2 ∧ h' ∈ Germ.maximalIdeal 2 ∧ h' ≠ 0 ∧
      g.1.component 2 - g.firstTwo.pullbackRingHom Ψ = Germ.coordinate 1 ^ k * h' ∧
      R ≠ 0 ∧ R.IsWeightedHomogeneous ![k, p] D ∧
      Germ.coordinate 1 ^ k * h' ∈ Germ.twoWeightOrderIdeal k p D ∧
      Germ.coordinate 1 ^ k * h' - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1) ∧
      R ∉ Set.range (MvPolynomial.aeval (cyclicInitialPair k p (Germ.valueRingHom 2 β)) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) ∧
      Λ ≠ 0 ∧ p * k ≤ D ∧ Λ.IsWeightedHomogeneous ![k, p] (D - p * k) ∧
      R = MvPolynomial.X 1 ^ k * Λ ∧
      (Λ ∈ cyclicInvariantAlgebra k ∨
        ∃ Λinv : MvPolynomial (Fin 2) ℂ, ∃ i j : ℕ, ∃ γ : ℂ,
          Λinv ∈ cyclicInvariantAlgebra k ∧
          Λinv.IsWeightedHomogeneous ![k, p] (D - p * k) ∧
          γ ≠ 0 ∧ ¬ k ∣ j ∧ k * i + p * j = D - p * k ∧
          Λ = Λinv + MvPolynomial.C γ * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j) := by
  obtain ⟨D, Ψ, h', R, hΨ, hh', hh'zero, heq, hRzero, hR, horder, htail, hdiv, hbase⟩ :=
    cyclic_injective_triple_ideal_preserving_initial_remainder
      g hg k p hk hp hodd β hβ hP hQ h hh hH
  obtain ⟨Λ, hfactor⟩ := hdiv
  obtain ⟨hΛzero, hD, hΛ⟩ := cyclicResidual_factor_homogeneous k p D R Λ hRzero hR hfactor
  obtain ⟨g', hequivalent, hzero, hone, htwo⟩ := g.exists_target_subtraction Ψ hΨ
  have hg' := hequivalent.hasInjectiveRepresentative hg
  have hpair : ∀ i, g'.firstTwo.1.component i - Germ.coordinatePolynomialAlgHom 2
      (cyclicInitialPair k p (Germ.valueRingHom 2 β) i) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k] i + 1) :=
    cyclic_pair_strict_tails g'.firstTwo k p hk hp β
      (by simpa using hzero.trans hP) (by simpa using hone.trans hQ)
  have htriple : ∀ i, g'.1.component i - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p (Germ.valueRingHom 2 β) R i) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] i + 1) := by
    intro i
    fin_cases i
    · simpa [cyclicResidualPolynomialMap] using hpair 0
    · simpa [cyclicResidualPolynomialMap] using hpair 1
    · change g'.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1)
      rw [htwo, heq]
      exact htail
  exact ⟨D, Ψ, h', R, Λ, hΨ, hh', hh'zero, heq, hRzero, hR, horder, htail, hbase,
    hΛzero, hD, hΛ, hfactor,
    cyclicResidual_quotient_fourier_dichotomy_of_injective g' hg' k p D hk (by omega)
      (Germ.valueRingHom 2 β) hβ R Λ hRzero hR hfactor htriple⟩

end OnLeConjecture.DTwo
