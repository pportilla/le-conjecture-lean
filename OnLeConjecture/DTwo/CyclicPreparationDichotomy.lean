/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicInvariantDegreeDescent
public import OnLeConjecture.Analytic.RightLeftRelation

/-!
# The cyclic preparation dichotomy from the original prepared germ

Finite analytic elimination and collision persistence give either a pure
odd initial third coordinate after target changes, or a residual initial
form with exactly one noninvariant monomial. The latter alternative is
retained and is not asserted to be impossible in this module.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic MvPolynomial

/-- Pure odd preparation by target changes preserving the first pair. -/
@[expose] def CyclicPureOddPreparation (g : PointedMapGerm 2 3) (k p : ℕ) : Prop :=
  ∃ g' : PointedMapGerm 2 3, ∃ κ : ℂ, ∃ q₀ : ℕ,
    g.RightLeftEquivalent g' ∧ g'.HasInjectiveRepresentative ∧
    g'.1.component 0 = g.1.component 0 ∧ g'.1.component 1 = g.1.component 1 ∧
    κ ≠ 0 ∧ 0 < q₀ ∧
    g'.1.component 2 - Germ.coordinatePolynomialAlgHom 2 (C κ * X 0 ^ (p + 2 * q₀)) ∈
      Germ.twoWeightOrderIdeal k p (k * (p + 2 * q₀) + 1)

/-- The remaining noninvariant alternative, with its actual analytic
remainder, polynomial initial form, and pair algebra exclusion. -/
@[expose] def CyclicNoninvariantResidual (g : PointedMapGerm 2 3) (k p : ℕ) (c : ℂ) : Prop :=
  ∃ g' : PointedMapGerm 2 3, ∃ D : ℕ, ∃ h : Germ 2,
    ∃ R Λ Λinv : MvPolynomial (Fin 2) ℂ, ∃ i j : ℕ, ∃ γ : ℂ,
      g.RightLeftEquivalent g' ∧ g'.HasInjectiveRepresentative ∧
      g'.1.component 0 = g.1.component 0 ∧ g'.1.component 1 = g.1.component 1 ∧
      h ∈ Germ.maximalIdeal 2 ∧ h ≠ 0 ∧
      g'.1.component 2 = Germ.coordinate 1 ^ k * h ∧
      p * k < D ∧ R ≠ 0 ∧ R.IsWeightedHomogeneous ![k, p] D ∧
      Germ.coordinate 1 ^ k * h ∈ Germ.twoWeightOrderIdeal k p D ∧
      Germ.coordinate 1 ^ k * h - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1) ∧
      R ∉ Set.range (aeval (cyclicInitialPair k p c) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) ∧
      Λ ≠ 0 ∧ Λ.IsWeightedHomogeneous ![k, p] (D - p * k) ∧ R = X 1 ^ k * Λ ∧
      Λinv ∈ cyclicInvariantAlgebra k ∧ Λinv.IsWeightedHomogeneous ![k, p] (D - p * k) ∧
      γ ≠ 0 ∧ ¬ k ∣ j ∧ k * i + p * j = D - p * k ∧
      Λ = Λinv + C γ * X 0 ^ i * X 1 ^ j

/-- The prepared analytic germ yields the two alternatives without an
assumed initial remainder, invariant polynomial, positive descended degree,
or no-root condition. -/
theorem cyclic_preparation_dichotomy
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (h : Germ 2) (hh : h ∈ Germ.maximalIdeal 2)
    (hH : g.1.component 2 = Germ.coordinate 1 ^ k * h) :
    CyclicPureOddPreparation g k p ∨
      CyclicNoninvariantResidual g k p (Germ.valueRingHom 2 β) := by
  obtain ⟨D, Ψ, h', R, Λ, hΨ, hh', hh'zero, heq, hRzero, hR, horder, htail, hbase,
      hΛzero, _, hΛ, hfactor, halternative⟩ :=
    cyclic_injective_triple_prepared_residual g hg k p hk hp hodd β hβ hP hQ h hh hH
  obtain ⟨g', hequivalent, hzero, hone, htwo⟩ := g.exists_target_subtraction Ψ hΨ
  have hg' := hequivalent.hasInjectiveRepresentative hg
  have hthird : g'.1.component 2 = Germ.coordinate 1 ^ k * h' := htwo.trans heq
  have hD := cyclicResidual_initial_degree_gt k p D hk (by omega) h' hh' R hRzero hR htail
  rcases halternative with hinvariant | hmixed
  · obtain ⟨g'', κ, q₀, hequivalent', hg'', hzero', hone', hκ, hq₀, hthird'⟩ :=
      cyclicInvariant_analytic_preparation_of_residual g' hg' k p D hk hp hodd β hβ
        (hzero.trans hP) (hone.trans hQ) h' hh' hthird
        R Λ hRzero hR htail hbase hfactor hinvariant
    exact Or.inl ⟨g'', κ, q₀, hequivalent.trans hequivalent', hg'',
      hzero'.trans hzero, hone'.trans hone, hκ, hq₀, hthird'⟩
  · obtain ⟨Λinv, i, j, γ, hinv, hinvHom, hγ, hj, hdegree, hΛeq⟩ := hmixed
    exact Or.inr ⟨g', D, h', R, Λ, Λinv, i, j, γ, hequivalent, hg', hzero, hone,
      hh', hh'zero, hthird, hD, hRzero, hR, horder, htail, hbase, hΛzero, hΛ, hfactor,
      hinv, hinvHom, hγ, hj, hdegree, hΛeq⟩

end OnLeConjecture.DTwo
