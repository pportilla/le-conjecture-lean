/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicWeightedElimination
public import OnLeConjecture.Analytic.PointedWeightedSubtraction
public import OnLeConjecture.Analytic.SecondCoordinateAnalyticSubtraction

/-!
# The actual cyclic triple after weighted elimination

Both analytic target corrections are realized by pointed equivalences.
The first two weighted initial forms and the nonzero third remainder
therefore belong to a single analytic triple equivalent to the original.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem exists_cyclic_weighted_triple_preparation
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
      ∃ cD : ℂ, cD ≠ 0 ∧ ∃ d : ℕ, 0 < d ∧ d ≤ (k + j) * N ∧
        ∃ P : MvPolynomial (Fin 2) ℂ, P ≠ 0 ∧ P.IsWeightedHomogeneous ![k + j, 2] d ∧
          P ∉ Set.range (MvPolynomial.aeval (cyclicAverageInitialPair k j (β 0) b) :
            MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) ∧
          ∃ g' : PointedMapGerm 2 3, g.RightLeftEquivalent g' ∧
            (∀ i : Fin 2, g'.firstTwo.1.component i - coordinatePolynomialAlgHom 2
              (cyclicAverageInitialPair k j (β 0) b i) ∈
                twoWeightOrderIdeal (k + j) 2 (![2 * k, 2 * (k + j)] i + 1)) ∧
            g'.1.component 2 - coordinatePolynomialAlgHom 2 P ∈
              twoWeightOrderIdeal (k + j) 2 (d + 1) ∧
            ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (-(b / β 0) * (1 - ζ ^ j)) →
              (d < (k + j) * N →
                MvPolynomial.eval (![s, 1]) P - MvPolynomial.eval (![S, ζ]) P = 0) ∧
              (d = (k + j) * N →
                MvPolynomial.eval (![s, 1]) P - MvPolynomial.eval (![S, ζ]) P =
                  cD * (s - S) ^ N) := by
  obtain ⟨j, hj, hchar, b, hb, J, hJ, hJb, hprevious, cD, hcD,
      d, hd, Ψ, P, hP0, hhom, hPtail, houtside, hcomparison⟩ :=
    exists_cyclic_weighted_elimination g hg k p N hk hp hodd hN β hβ hc
      hP hQ htail ζ hζ hζ1
  have hd0 := twoWeight_degree_pos_of_not_mem_pair_algebra (k + j) 2 d
    (by omega) (by decide) P hhom _ houtside
  have hΨ := target_correction_mem_maximalIdeal_of_twoWeight_tail g.firstTwo
    (g.1.component 2) Ψ (g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal 2))
    (k + j) 2 d (by omega) (by decide) hd0 P hhom hPtail
  obtain ⟨gZ, hequivZ, hZ0, hZ1, hZ2⟩ := g.exists_target_subtraction Ψ hΨ
  obtain ⟨a, f, _, _, _, _, _, hf0, hf1, hinitial⟩ :=
    exists_cyclicAverage_target_correction k j p hk hj hp ζ hζ
      (cyclicCoefficientGerm β hβ) J hJ hprevious hchar (hJb ▸ hb) g.firstTwo
      (by simpa [cyclicFirst] using hP) (by simpa [cyclicSecond] using hQ)
  obtain ⟨g', hequiv, hg'0, hg'1, hg'2⟩ :=
    gZ.exists_target_secondAnalyticSubtraction (coordinate (0 : Fin 1) * a)
      (Ideal.mul_mem_right _ _ (coordinate_mem_maximalIdeal (0 : Fin 1)))
  have hproj : gZ.firstCoordinateTriple = cyclicPowerSumMap 2 k (by omega) hk := by
    apply PointedMapGerm.ext_components
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [PointedMapGerm.firstCoordinateTriple_component, hZ0, hP,
      ← PointedMapGerm.pullback_coordinate, cyclicPowerSumMap_pullback_coordinate]
    rfl
  have hfirst : g'.firstTwo = f := by
    apply PointedMapGerm.ext_components
    intro i
    fin_cases i
    · rw [PointedMapGerm.firstTwo_component]
      change g'.1.component 0 = f.1.component 0
      rw [hg'0, hZ0, hf0]
      simp
    · rw [PointedMapGerm.firstTwo_component]
      change g'.1.component 1 = f.1.component 1
      rw [hg'1, hZ1, hQ, hproj, map_mul, cyclicPowerSumMap_pullback_coordinate, hf1]
      rfl
  refine ⟨j, hj, hchar, b, hb, cD, hcD, d, hd0, hd, P, hP0, hhom,
    houtside, g', hequivZ.trans hequiv, ?_, ?_, hcomparison⟩
  · intro i
    rw [hfirst]
    have hβc : valueRingHom 1 (cyclicCoefficientGerm β hβ) = β 0 := rfl
    simpa only [hJb, hβc] using (hinitial i).2.2
  · rw [hg'2, hZ2]
    exact hPtail

end OnLeConjecture.DTwo
