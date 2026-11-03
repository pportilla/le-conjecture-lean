/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPrimitiveDegreePreparation
public import OnLeConjecture.DTwo.CyclicOddInitialPolynomial
public import OnLeConjecture.DTwo.ResidualGermOrderExclusion
public import OnLeConjecture.DTwo.ResidualPrimitiveNoninjectivityAssembly
public import OnLeConjecture.Analytic.WeightedThirdInitialReplacement

/-!
# Noninjectivity of the cyclic prepared analytic map

Starting with the actual prepared map and its odd monomial initial term,
the proof constructs the noninvariant coefficient, weighted equivalent
triple, polynomial model, pointed target corrections, and final analytic
collision. No weighted component identity, elimination result, or
polynomial model is assumed.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

private theorem residualInitialPair_eq_cyclicAverageInitialPair
    (k j N : ℕ) (c b : ℂ) (hc : c ≠ 0)
    (Ψ : PreparedOddFamily N) (model : Ψ.BivariateModel) (i : Fin 2) :
    residualWeightedInitialPolynomials k (k + j) c (-b / c) Ψ model
      (i.castLE (by omega)) = cyclicAverageInitialPair k j c b i := by
  fin_cases i
  · rfl
  · change MvPolynomial.C (-c) *
        (MvPolynomial.X 0 ^ 2 + MvPolynomial.C (-b / c) * MvPolynomial.X 1 ^ (k + j)) =
      -(MvPolynomial.C c * MvPolynomial.X 0 ^ 2) +
        MvPolynomial.C b * MvPolynomial.X 1 ^ (k + j)
    have hscalar : (MvPolynomial.C (-c) * MvPolynomial.C (-b / c) :
        MvPolynomial (Fin 2) ℂ) = MvPolynomial.C b := by
      rw [← map_mul]
      congr 1
      field_simp
    rw [mul_add, ← mul_assoc, hscalar, map_neg, neg_mul]

theorem cyclic_prepared_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3)
    (a k p N : ℕ) (ha : 2 ≤ a) (hk : k = 2 * a)
    (hp : 3 ≤ p) (hodd : Odd p) (hN : 3 ≤ N) (hNodd : Odd N)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 =
      cyclicSecond k p (hyperplaneExtension 1 (cyclicCoefficientGerm β hβ)))
    (htail : g.1.component 2 - coordinate (0 : Fin 2) ^ N ∈
      twoWeightOrderIdeal k p (k * N + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  have hk0 : 0 < k := by omega
  let ζ := residualPrimitiveRoot k
  have hζ := residualPrimitiveRoot_isPrimitiveRoot hk0
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  obtain ⟨j, hj, hchar, b, hb, cD, hcD, P, _hP0, hhom, f, hequiv, hfirst, hthird, hchart⟩ :=
    exists_cyclic_primitive_degree_preparation g hg k p N hk0 hp hodd hNodd
      β hβ hc hP hQ htail ζ hζ hζ1
  obtain ⟨_hminus, s, hs, Ψ, model, hquotient, hidentity⟩ :=
    exists_cyclic_prepared_model_of_primitive_weighted_chart hk0 hN hNodd hb hc hcD
      hζ hchar P hhom (by
        intro x X hX hpoint
        exact hchart x X hX (by simpa only [neg_div] using hpoint))
  let H := residualWeightedInitialPolynomials k (k + j) (β 0) (-b / β 0) Ψ model 2
  have hH : H.IsWeightedHomogeneous ![k + j, 2] ((k + j) * N) := by
    simpa [H, residualWeightedDegrees, mul_comm] using
      residualWeightedInitialPolynomials_isWeightedHomogeneous k (k + j) (β 0) (-b / β 0) Ψ model 2
  have hquotient' : P - MvPolynomial.C s * H ∈
      Set.range (MvPolynomial.aeval (cyclicAverageInitialPair k j (β 0) b) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) := by
    simpa [H, residualWeightedInitialPolynomials, MvPolynomial.aeval_eq_bind₁,
      residualParameterPolynomialSubstitution, cyclicAverageInitialPair, neg_mul] using hquotient
  obtain ⟨g', hequiv', hg'0, hg'1, hg'2⟩ :=
    f.exists_weighted_third_initial_replacement (k + j) 2 ((k + j) * N)
      (by omega) (by decide) (Nat.mul_pos (by omega) (by omega))
      ![2 * k, 2 * (k + j)] (cyclicAverageInitialPair k j (β 0) b)
      (cyclicAverageInitialPair_homogeneous k j _ _) hfirst P H hhom hH s hs hthird hquotient'
  apply residualGermOrderTails_not_hasInjectiveRepresentative g' a k j N ha hk hN
    ζ (β 0) (-b / β 0) (s⁻¹ * cD) hζ hchar hc
    (div_ne_zero (neg_ne_zero.mpr hb) hc) Ψ model hidentity _
      ((hequiv.trans hequiv').hasInjectiveRepresentative hg)
  intro i
  fin_cases i
  · change g'.1.component 0 - coordinatePolynomialAlgHom 2
        (residualWeightedInitialPolynomials k (k + j) (β 0) (-b / β 0) Ψ model 0) ∈
      twoWeightOrderIdeal (k + j) 2 (2 * k + 1)
    have hpoly : residualWeightedInitialPolynomials k (k + j) (β 0) (-b / β 0) Ψ model 0 =
        cyclicAverageInitialPair k j (β 0) b 0 := by
      simpa using residualInitialPair_eq_cyclicAverageInitialPair k j N (β 0) b hc Ψ model 0
    rw [hg'0, hpoly]
    simpa using hfirst 0
  · change g'.1.component 1 - coordinatePolynomialAlgHom 2
        (residualWeightedInitialPolynomials k (k + j) (β 0) (-b / β 0) Ψ model 1) ∈
      twoWeightOrderIdeal (k + j) 2 (2 * (k + j) + 1)
    have hpoly : residualWeightedInitialPolynomials k (k + j) (β 0) (-b / β 0) Ψ model 1 =
        cyclicAverageInitialPair k j (β 0) b 1 := by
      simpa using residualInitialPair_eq_cyclicAverageInitialPair k j N (β 0) b hc Ψ model 1
    rw [hg'1, hpoly]
    simpa using hfirst 1
  · simpa [H, residualWeightedDegrees, mul_comm] using hg'2

end OnLeConjecture.DTwo
