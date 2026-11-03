/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicWeightedInitialComparison
public import OnLeConjecture.DTwo.PreparedCyclicCollision

/-!
# The weighted cyclic comparison for analytic germs

The comparison is independent of representatives and applies to every
analytic expression in the original first two target coordinates.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem cyclicFirstTwo_ofFunction
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hpair : AnalyticAt ℂ (fun q => ![G q 0, G q 1]) 0)
    (hpair0 : (![G 0 0, G 0 1] : Source 2) = 0) :
    (PointedMapGerm.ofFunction G hG hG0).firstTwo =
      PointedMapGerm.ofFunction (fun q => ![G q 0, G q 1]) hpair hpair0 := by
  apply PointedMapGerm.ext_components
  intro i
  rw [PointedMapGerm.firstTwo_component]
  apply Subtype.ext
  fin_cases i <;> rfl

/-- The same jet supplies both the branch comparison and the invariance
of every preceding coefficient. All target subtractions remain arbitrary. -/
theorem exists_cyclic_weighted_germ_comparison
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p N : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hN : Odd N)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 =
      cyclicSecond k p (hyperplaneExtension 1 (cyclicCoefficientGerm β hβ)))
    (htail : g.1.component 2 - coordinate (0 : Fin 2) ^ N ∈
      twoWeightOrderIdeal k p (k * N + 1))
    (ζ : ℂ) (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) :
    ∃ j : ℕ, 0 < j ∧ ζ ^ j ≠ 1 ∧
      ∃ J : MvPolynomial (Fin 1) ℂ,
        cyclicCoefficientGerm β hβ - coordinatePolynomialAlgHom 1 J ∈
          maximalIdeal 1 ^ (j + 1) ∧
        J.coeff (Finsupp.single 0 j) ≠ 0 ∧
        (∀ i < j, J.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1) ∧
        ∃ cD : ℂ, cD ≠ 0 ∧
          ∀ Ψ : Germ 2, ∀ d : ℕ, ∀ P : MvPolynomial (Fin 2) ℂ,
            P.IsWeightedHomogeneous ![k + j, 2] d →
            g.1.component 2 - g.firstTwo.pullbackRingHom Ψ -
              coordinatePolynomialAlgHom 2 P ∈ twoWeightOrderIdeal (k + j) 2 (d + 1) →
            ∀ s S : ℂ, S ≠ 0 →
              S ^ 2 = s ^ 2 + (-(J.coeff (Finsupp.single 0 j) / β 0) * (1 - ζ ^ j)) →
              d ≤ (k + j) * N ∧
                (d < (k + j) * N →
                  MvPolynomial.eval (![s, 1]) P - MvPolynomial.eval (![S, ζ]) P = 0) ∧
                (d = (k + j) * N →
                  MvPolynomial.eval (![s, 1]) P - MvPolynomial.eval (![S, ζ]) P =
                    cD * (s - S) ^ N) := by
  obtain ⟨G, hG, hG0, rfl, hinjective⟩ := hg
  have hP' : ∀ᶠ q in 𝓝 (0 : Source 2), G q 0 = q 0 ^ 2 + q 1 ^ k :=
    Filter.Germ.coe_eq.mp (congrArg Subtype.val hP)
  have hQ' : ∀ᶠ q in 𝓝 (0 : Source 2),
      G q 1 = q 0 ^ p + q 1 ^ k * β (q 1) :=
    Filter.Germ.coe_eq.mp (congrArg Subtype.val hQ)
  have hthird : (PointedMapGerm.ofFunction G hG hG0).1.component 2 =
      ofFunction (fun q => G q 2) (analyticAt_pi_iff.mp hG 2) := by
    apply Subtype.ext
    rfl
  rw [hthird] at htail ⊢
  obtain ⟨j, hj, hchar, J, hJ, hJc, hprevious, cD, hcD, hcomparison⟩ :=
    exists_cyclic_weighted_initial_comparison G hG hinjective k p N hk hp hN
      β hβ hc hP' hQ' htail ζ hζ hζ0 hζ1
  refine ⟨j, hj, hchar, J, hJ, hJc, hprevious, cD, hcD, ?_⟩
  intro Ψ d P hhom hnewtail
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFunction Ψ
  have hpair : AnalyticAt ℂ (fun q => ![G q 0, G q 1]) 0 := by
    apply AnalyticAt.pi
    intro i
    fin_cases i <;> exact analyticAt_pi_iff.mp hG _
  have hpair0 : (![G 0 0, G 0 1] : Source 2) = 0 := by
    rw [hG0]
    ext i
    fin_cases i <;> rfl
  have hψpair : AnalyticAt ℂ (fun q => ψ (![G q 0, G q 1])) 0 :=
    hψ.comp_of_eq hpair hpair0
  let F : Source 2 → ℂ := fun q => G q 2 - ψ (![G q 0, G q 1])
  have hF : AnalyticAt ℂ F 0 := (analyticAt_pi_iff.mp hG 2).sub hψpair
  have hFgerm : ofFunction F hF =
      ofFunction (fun q => G q 2) (analyticAt_pi_iff.mp hG 2) -
        (PointedMapGerm.ofFunction G hG hG0).firstTwo.pullbackRingHom (ofFunction ψ hψ) := by
    rw [cyclicFirstTwo_ofFunction G hG hG0 hpair hpair0,
      PointedMapGerm.pullbackRingHom_apply, compPointed_ofFunction]
    apply Subtype.ext
    rfl
  apply hcomparison F hF ψ (Filter.Eventually.of_forall (fun _ => rfl)) d P hhom
  rwa [hFgerm]

end OnLeConjecture.DTwo
