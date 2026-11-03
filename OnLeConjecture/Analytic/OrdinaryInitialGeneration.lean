/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrdinaryWeightedOrder
public import OnLeConjecture.Analytic.WeightedPrincipalClosure
public import Mathlib.RingTheory.Nakayama

/-!
# Generation from a full ordinary initial ideal

Nakayama's lemma upgrades generation modulo the next ordinary order to
containment of the entire power of the maximal ideal. In particular, germs
whose initial forms span that power have no common nonunit divisor.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Initial generation of a power of the maximal ideal is sufficient for
actual analytic ideal containment. -/
theorem maximalIdeal_pow_le_of_le_sup_succ
    (D : ℕ) (J : Ideal (Germ 2))
    (hJ : maximalIdeal 2 ^ D ≤ J ⊔ maximalIdeal 2 ^ (D + 1)) :
    maximalIdeal 2 ^ D ≤ J := by
  apply Submodule.le_of_le_smul_of_le_jacobson_bot
    (IsNoetherian.noetherian _) (I := maximalIdeal 2)
    (show maximalIdeal 2 ≤ Ideal.jacobson ⊥ from by
      rw [maximalIdeal_eq_isLocalRing]
      exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
  simpa only [Ideal.smul_eq_mul, pow_succ', Nat.succ_eq_add_one] using hJ

/-- Analytic perturbations of all degree-`D` binary monomials generate
an ideal containing the `D`th ordinary power. -/
theorem maximalIdeal_pow_le_of_monomial_initial_generators
    (D : ℕ) (J : Ideal (Germ 2)) (f : Fin (D + 1) → Germ 2)
    (hf : ∀ i, f i ∈ J)
    (htail : ∀ i, f i - weightedOrderGenerator 1 D i ∈ maximalIdeal 2 ^ (D + 1)) :
    maximalIdeal 2 ^ D ≤ J := by
  apply maximalIdeal_pow_le_of_le_sup_succ
  rw [← weightedOrderIdeal_one_eq_maximalIdeal_pow, weightedOrderIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change weightedOrderGenerator 1 D i ∈ J ⊔ maximalIdeal 2 ^ (D + 1)
  have hfi : f i ∈ J ⊔ maximalIdeal 2 ^ (D + 1) :=
    (show J ≤ J ⊔ maximalIdeal 2 ^ (D + 1) from le_sup_left) (hf i)
  have hti : f i - weightedOrderGenerator 1 D i ∈ J ⊔ maximalIdeal 2 ^ (D + 1) :=
    (show maximalIdeal 2 ^ (D + 1) ≤ J ⊔ maximalIdeal 2 ^ (D + 1) from
      le_sup_right) (htail i)
  simpa only [sub_sub_cancel] using (J ⊔ maximalIdeal 2 ^ (D + 1)).sub_mem hfi hti

/-- No analytic germ vanishing at the origin can divide a full collection
of perturbed ordinary monomials. -/
theorem no_common_nonunit_divisor_of_monomial_initial_generators
    (D : ℕ) (f : Fin (D + 1) → Germ 2)
    (htail : ∀ i, f i - weightedOrderGenerator 1 D i ∈ maximalIdeal 2 ^ (D + 1))
    (g : Germ 2) (hg : g ∈ maximalIdeal 2) :
    ¬ ∀ i, g ∣ f i := by
  intro hdiv
  apply not_maximalIdeal_pow_le_span_singleton g hg
  exact ⟨D, maximalIdeal_pow_le_of_monomial_initial_generators D (Ideal.span {g})
    f (fun i => Ideal.mem_span_singleton.mpr (hdiv i)) htail⟩

end OnLeConjecture.Analytic.Germ
