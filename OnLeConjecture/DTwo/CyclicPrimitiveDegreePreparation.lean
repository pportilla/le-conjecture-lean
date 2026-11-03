/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicWeightedTriplePreparation
public import OnLeConjecture.DTwo.HomogeneousEqualizerPolynomialDescent

/-!
# The exact primitive weighted degree

The polynomial equalizer theorem excludes every degree strictly below
the branch-difference order. Finite elimination therefore gives degree
`(k+j)N` and the nonzero primitive comparison for an actual equivalent
analytic triple.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem exists_cyclic_primitive_degree_preparation
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p N : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (hN : Odd N)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 =
      cyclicSecond k p (hyperplaneExtension 1 (cyclicCoefficientGerm β hβ)))
    (htail : g.1.component 2 - coordinate (0 : Fin 2) ^ N ∈
      twoWeightOrderIdeal k p (k * N + 1))
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k) (hζ1 : ζ ≠ 1) :
    ∃ j : ℕ, 0 < j ∧ ζ ^ j ≠ 1 ∧ ∃ b : ℂ, b ≠ 0 ∧
      ∃ cD : ℂ, cD ≠ 0 ∧ ∃ P : MvPolynomial (Fin 2) ℂ,
        P ≠ 0 ∧ P.IsWeightedHomogeneous ![k + j, 2] ((k + j) * N) ∧
        ∃ g' : PointedMapGerm 2 3, g.RightLeftEquivalent g' ∧
          (∀ i : Fin 2, g'.firstTwo.1.component i - coordinatePolynomialAlgHom 2
            (cyclicAverageInitialPair k j (β 0) b i) ∈
              twoWeightOrderIdeal (k + j) 2 (![2 * k, 2 * (k + j)] i + 1)) ∧
          g'.1.component 2 - coordinatePolynomialAlgHom 2 P ∈
            twoWeightOrderIdeal (k + j) 2 ((k + j) * N + 1) ∧
          ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (-(b / β 0) * (1 - ζ ^ j)) →
            MvPolynomial.eval (![s, 1]) P - MvPolynomial.eval (![S, ζ]) P =
              cD * (s - S) ^ N := by
  obtain ⟨j, hj, hchar, b, hb, cD, hcD, d, _hd0, hd, P, hP0, hhom,
      houtside, g', hequiv, hfirst, hthird, hcomparison⟩ :=
    exists_cyclic_weighted_triple_preparation g hg k p N hk hp hodd hN
      β hβ hc hP hQ htail ζ hζ hζ1
  have heq : d = (k + j) * N := by
    apply le_antisymm hd
    apply le_of_not_gt
    intro hlt
    obtain ⟨R, hR⟩ := exists_initial_pair_polynomial_of_weighted_chart hk hb hc
      hζ hchar P hhom (by
        intro s S hS hpoint
        exact (hcomparison s S hS (by simpa only [neg_div] using hpoint)).1 hlt)
    apply houtside
    refine ⟨R, ?_⟩
    simpa only [cyclicAverageInitialPair, neg_mul] using hR
  subst d
  refine ⟨j, hj, hchar, b, hb, cD, hcD, P, hP0, hhom, g', hequiv, hfirst, hthird, ?_⟩
  intro s S hS hpoint
  exact (hcomparison s S hS hpoint).2 rfl

end OnLeConjecture.DTwo
