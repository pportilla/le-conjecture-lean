/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.PreparedPrimitiveChartIdentity
public import OnLeConjecture.Analytic.PairRepresentative

/-!
# Residual exclusion from the actual weighted germ ideals

The weighted tails themselves suffice for the analytic collision theorem.
No separate coefficient divisibility or representative is required.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ DThree

theorem residual_half_order_dvd_weight
    (a k j : ℕ) (hk : k = 2 * a) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ k) (hcharacter : ζ ^ j = -1) : a ∣ k + j := by
  have hpower : ζ ^ (j * 2) = 1 := by
    rw [pow_mul, hcharacter, neg_one_sq]
  have hdiv : k ∣ 2 * j := by
    apply hζ.dvd_of_pow_eq_one (2 * j)
    simpa only [mul_comm] using hpower
  rw [hk] at hdiv
  have haj : a ∣ j := by
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ (by decide : (2 : ℕ) ≠ 0)
    simpa only [mul_assoc] using hq
  exact dvd_add (hk ▸ dvd_mul_left a 2) haj

/-- The model, primitive component identity, and actual weighted tails
exclude injectivity of a pointed analytic germ. The character, subgroup
divisibility, collision, and radial expansion are derived. -/
theorem residualGermOrderTails_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3)
    (a k j N : ℕ) (ha : 2 ≤ a) (hk : k = 2 * a) (hN : 3 ≤ N)
    (ζ c T cD : ℂ) (hζ : IsPrimitiveRoot ζ k) (hcharacter : ζ ^ j ≠ 1)
    (hc : c ≠ 0) (hT : T ≠ 0)
    (Ψ : PreparedOddFamily N) (model : Ψ.BivariateModel)
    (hidentity : PreparedPrimitiveComponentIdentity N (ζ ^ j) cD
      (preparedCoefficient N model.polynomial))
    (htail : ∀ i : Fin 3,
      g.1.component i - coordinatePolynomialAlgHom 2
        (residualWeightedInitialPolynomials k (k + j) c T Ψ model i) ∈
          twoWeightOrderIdeal (k + j) 2 (residualWeightedDegrees k (k + j) N i + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  have hchar := Ψ.primitivePower_eq_neg_one_of_componentIdentity hN model hcharacter hidentity
  have hdiv := residual_half_order_dvd_weight a k j hk ζ hζ hchar
  obtain ⟨certificate⟩ := exists_initialCollisionCertificate a k (k + j) N c T Ψ
    ha hk hdiv hN hc hT
  obtain ⟨G, hG, hG0, rfl⟩ := g.exists_ofPairFunction
  apply residualWeightedModelOrderTails_not_hasInjectiveRepresentative
    model certificate G hG hG0 _ (by omega)
  intro i
  convert htail i using 1
  congr 1

end OnLeConjecture.DTwo
