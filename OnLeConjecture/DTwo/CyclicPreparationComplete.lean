/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicNormLifting
public import OnLeConjecture.DTwo.CyclicMixedOddCollision

/-!
# Pure odd preparation of the prepared cyclic pair

Every mixed residual is excluded by analytic collisions. Positive first
exponents use the isolated quadratic crossing. Zero first exponent uses
an affine norm root count and compatible power lifting. Thus the original
prepared analytic germ admits pure odd preparation.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic MvPolynomial

/-- The zero-first-exponent mixed alternative is incompatible with
injectivity, for every descended degree. -/
theorem cyclicMixedZero_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (k p j d D : ℕ)
    (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j) (hdegree : p * j = k * d)
    (c γ : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (L R : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hfactor : R = X 1 ^ k * (cyclicInvariantLift k L + C γ * X 1 ^ j))
    (htail : ∀ index, g.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c R index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨s, Y, hs, _, _, hcurve, hroot⟩ := exists_cyclicMixedZero_initial_collision
    k p j d hk hp hj hdegree c γ hc hγ L R hL hfactor
  exact cyclicMixedZero_collision_not_hasInjectiveRepresentative g k p j d D hk hp hj hdegree
    c γ s Y hc hγ hs hcurve L R hL hR hfactor hroot htail

/-- The mixed zero-exponent data retained by analytic elimination cannot
occur for the original prepared pair. -/
theorem not_cyclicMixedZeroResidual_of_prepared_pair
    (g : PointedMapGerm 2 3) (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p)
    (β : Germ 2) (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β) :
    ¬ CyclicMixedZeroResidual g k p (Germ.valueRingHom 2 β) := by
  rintro ⟨g', D, h, R, Λ, Λinv, j, γ, _, hg', hzero, hone,
    _, _, hthird, _, _, hR, _, htail, _, _, _, hfactor,
    hinv, hinvHom, hγ, hj, hdegree, hΛeq, hinvZero⟩
  obtain ⟨d, L, _, hL, hE, hΛinv⟩ :=
    exists_cyclicInvariant_homogeneous_descent k p (D - p * k) hk Λinv
      hinvZero hinvHom hinv
  have hpairtail := cyclic_pair_strict_tails g'.firstTwo k p hk hp β
    (by simpa using hzero.trans hP) (by simpa using hone.trans hQ)
  have htriple : ∀ index, g'.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p (Germ.valueRingHom 2 β) R index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1) := by
    intro index
    fin_cases index
    · simpa [cyclicResidualPolynomialMap] using hpairtail 0
    · simpa [cyclicResidualPolynomialMap] using hpairtail 1
    · change g'.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1)
      rw [hthird]
      exact htail
  exact cyclicMixedZero_not_hasInjectiveRepresentative g' k p j d D hk hodd hj
    (hdegree.trans hE) (Germ.valueRingHom 2 β) γ hβ hγ L R hL hR
    (by rw [hfactor, hΛeq, hΛinv]) htriple hg'

/-- The prepared injective analytic germ admits pure odd preparation.
All mixed alternatives are excluded, with no polynomial collision,
Fermat intersection, or weighted persistence hypothesis. -/
theorem cyclic_preparation_pure_odd
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (h : Germ 2) (hh : h ∈ Germ.maximalIdeal 2)
    (hH : g.1.component 2 = Germ.coordinate 1 ^ k * h) :
    CyclicPureOddPreparation g k p := by
  rcases cyclic_preparation_pure_odd_or_mixed_zero g hg k p hk hp hodd β hβ hP hQ h hh hH with
    hpure | hmixed
  · exact hpure
  · exact (not_cyclicMixedZeroResidual_of_prepared_pair g k p hk hp hodd β hβ hP hQ hmixed).elim

end OnLeConjecture.DTwo
