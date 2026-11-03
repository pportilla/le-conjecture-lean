/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicWeightedGermComparison
public import OnLeConjecture.DTwo.CyclicAverageTargetCorrection

/-!
# Finite elimination at the first noninvariant cyclic weight

The coefficient jet selected by the actual branch comparison also defines
the convergent target correction. Finiteness and nonmembership in the
analytic image ring supply a nonzero initial remainder outside the
polynomial algebra of the corrected initial pair.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- Construct the weighted remainder and its component comparison from
the original injective analytic germ. No initial-pair algebra or limiting
component identity is assumed. -/
theorem exists_cyclic_weighted_elimination
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
      ∃ J : MvPolynomial (Fin 1) ℂ,
        cyclicCoefficientGerm β hβ - coordinatePolynomialAlgHom 1 J ∈
          maximalIdeal 1 ^ (j + 1) ∧
        J.coeff (Finsupp.single 0 j) = b ∧
        (∀ i < j, J.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1) ∧
      ∃ cD : ℂ, cD ≠ 0 ∧ ∃ d : ℕ, d ≤ (k + j) * N ∧
        ∃ Ψ : Germ 2, ∃ P : MvPolynomial (Fin 2) ℂ,
          P ≠ 0 ∧ P.IsWeightedHomogeneous ![k + j, 2] d ∧
          g.1.component 2 - g.firstTwo.pullbackRingHom Ψ -
            coordinatePolynomialAlgHom 2 P ∈ twoWeightOrderIdeal (k + j) 2 (d + 1) ∧
          P ∉ Set.range (MvPolynomial.aeval (cyclicAverageInitialPair k j (β 0) b) :
            MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) ∧
          ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (-(b / β 0) * (1 - ζ ^ j)) →
            (d < (k + j) * N →
              MvPolynomial.eval (![s, 1]) P - MvPolynomial.eval (![S, ζ]) P = 0) ∧
            (d = (k + j) * N →
              MvPolynomial.eval (![s, 1]) P - MvPolynomial.eval (![S, ζ]) P =
                cD * (s - S) ^ N) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hk.ne'
  obtain ⟨j, hj, hchar, J, hJ, hJc, hprevious, cD, hcD, hcomparison⟩ :=
    exists_cyclic_weighted_germ_comparison g hg k p N hk hp hN β hβ hc
      hP hQ htail ζ hζ.pow_eq_one hζ0 hζ1
  obtain ⟨a, f, _, _, _, himage, _, _, _, hinitial⟩ :=
    exists_cyclicAverage_target_correction k j p hk hj hp ζ hζ
      (cyclicCoefficientGerm β hβ) J hJ hprevious hchar hJc g.firstTwo
      (by simpa [cyclicFirst] using hP)
      (by simpa [cyclicSecond] using hQ)
  have hβvalue : valueRingHom 2
      (hyperplaneExtension 1 (cyclicCoefficientGerm β hβ)) ≠ 0 := hc
  have hfinite : f.IsFiniteAtOrigin := by
    rw [PointedMapGerm.IsFiniteAtOrigin, himage]
    exact cyclic_isFiniteAtOrigin g.firstTwo k p hp _ hβvalue
      (by simpa using hP)
      (by simpa using hQ)
  have hnotimage : g.1.component 2 ∉ f.ImageRing := by
    rw [himage]
    exact cyclic_third_not_mem_imageRing g hg k p hk hp hodd _ hβvalue hP hQ
  obtain ⟨d, Φ, P, hP0, hhom, _, hPtail, hPoutside⟩ :=
    f.exists_twoWeight_initial_form_outside_pair_algebra hfinite (k + j) 2
      (by omega) (by decide) ![2 * k, 2 * (k + j)]
      (cyclicAverageInitialPair k j (valueRingHom 1 (cyclicCoefficientGerm β hβ))
        (J.coeff (Finsupp.single 0 j)))
      (fun i => (hinitial i).1) (fun i => (hinitial i).2.2) _ hnotimage
  have hΦimage : f.pullbackRingHom Φ ∈ g.firstTwo.ImageRing := by
    rw [← himage]
    exact ⟨Φ, rfl⟩
  obtain ⟨Ψ, hΨ⟩ := hΦimage
  rw [← hΨ] at hPtail
  have hcomp := hcomparison Ψ d P hhom hPtail
  have hC : -(J.coeff (Finsupp.single 0 j) / β 0) * (1 - ζ ^ j) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (div_ne_zero hJc hc))
      (sub_ne_zero.mpr (Ne.symm hchar))
  obtain ⟨S, hS⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(J.coeff (Finsupp.single 0 j) / β 0) * (1 - ζ ^ j)) (by decide : 0 < (2 : ℕ))
  have hS0 : S ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hS
    exact hC hS.symm
  have hd := (hcomp 0 S hS0 (by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_add] using hS)).1
  refine ⟨j, hj, hchar, J.coeff (Finsupp.single 0 j), hJc, J, hJ, rfl, hprevious, cD, hcD,
    d, hd, Ψ, P, hP0, hhom, hPtail, hPoutside, ?_⟩
  intro s S hS hpoint
  exact (hcomp s S hS hpoint).2

end OnLeConjecture.DTwo
