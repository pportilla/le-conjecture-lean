/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridOneVariableComplex

/-!
# Exact Maslov and Alexander coordinates over R[U]

For a term `U^k x`, the degree is `M_O(x)-2k` and the Alexander coordinate
is `A(x)-k`. These formulas are proved from the actual polynomial coefficients,
so neither grading nor filtration depends on the selected O variable used
for the coefficient inclusion.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti MvPolynomial

variable {n : ℕ} (R : Type*) [CommRing R]

/-- Including a univariate monomial gives the monomial in the selected O variable. -/
theorem oneVariableSection_monomial (a : Fin n) (k : ℕ) (r : R) :
    oneVariableSection R a (Polynomial.monomial k r) = monomial (Finsupp.single a k) r := by
  simp [oneVariableSection, Polynomial.aeval_monomial, C_mul_X_pow_eq_monomial]

/-- The coefficient inclusion preserves each univariate coefficient exactly. -/
theorem coeff_oneVariableSection_single (a : Fin n) (p : Polynomial R) (k : ℕ) :
    coeff (Finsupp.single a k) (oneVariableSection R a p) = p.coeff k := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, Polynomial.coeff_add, hp, hq]
  | monomial j r =>
    rw [oneVariableSection_monomial, coeff_monomial, Polynomial.coeff_monomial]
    simp only [(Finsupp.single_injective a).eq_iff]

/-- Every included coefficient has support only at powers of the selected variable. -/
theorem exists_support_oneVariableSection (a : Fin n) (p : Polynomial R)
    {e : Fin n →₀ ℕ} (he : e ∈ (oneVariableSection R a p).support) :
    ∃ k ∈ p.support, e = Finsupp.single a k := by
  classical
  have hp : oneVariableSection R a p =
      ∑ k ∈ p.support, monomial (Finsupp.single a k) (p.coeff k) := by
    conv_lhs => rw [← Polynomial.sum_monomial_eq p]
    simp only [Polynomial.sum, map_sum, oneVariableSection_monomial]
  rw [hp] at he
  obtain ⟨k, hk, hke⟩ := Finset.mem_biUnion.mp (support_sum he)
  refine ⟨k, hk, ?_⟩
  simpa only [support_monomial, if_neg (Polynomial.mem_support_iff.mp hk),
    Finset.mem_singleton] using hke

/-- Exact support characterization of the one-variable Maslov grading. -/
theorem mem_oneVariableMaslovPiece_iff (G : GridDiagram n) (a : Fin n)
    (m : ℤ) (c : OneVariableChain R n) :
    c ∈ oneVariableMaslovPiece R G a m ↔
      ∀ x k, k ∈ (c x).support → G.maslovOℤ x - 2 * (k : ℤ) = m := by
  change oneVariableChainSection R a c ∈ maslovPiece G R m ↔ _
  rw [mem_maslovPiece]
  constructor
  · intro hc x k hk
    have he : Finsupp.single a k ∈ (oneVariableSection R a (c x)).support := by
      rw [mem_support_iff, coeff_oneVariableSection_single]
      exact Polynomial.mem_support_iff.mp hk
    simpa [maslovDegree, exponentSize] using hc x (Finsupp.single a k) he
  · intro hc x e he
    obtain ⟨k, hk, rfl⟩ := exists_support_oneVariableSection R a (c x) he
    simpa [maslovDegree, exponentSize] using hc x k hk

variable [CharP R 2]

/-- Exact support characterization of the one-variable Alexander filtration. -/
theorem mem_oneVariableAlexanderFiltration_iff (G : GridDiagram n) (a : Fin n)
    (v : ℝ) (m : ℤ) (c : (oneVariableMaslovComplex R G a).X m) :
    c ∈ (oneVariableAlexanderFiltration R G a).level v m ↔
      ∀ x k, k ∈ (((show oneVariableMaslovPiece R G a m from c) : OneVariableChain R n) x).support →
        (G.alexander x : ℝ) - k ≤ v := by
  change oneVariableChainSection R a
    ((show oneVariableMaslovPiece R G a m from c) : OneVariableChain R n) ∈
      bifiltrationLevel G R 0 v ↔ _
  rw [mem_bifiltrationLevel_iff]
  constructor
  · intro hc x k hk
    have he : Finsupp.single a k ∈ (oneVariableSection R a
        (((show oneVariableMaslovPiece R G a m from c) : OneVariableChain R n) x)).support := by
      rw [mem_support_iff, coeff_oneVariableSection_single]
      exact Polynomial.mem_support_iff.mp hk
    simpa [exponentSize] using (hc x (Finsupp.single a k) he).2
  · intro hc x e he
    obtain ⟨k, hk, rfl⟩ := exists_support_oneVariableSection R a _ he
    constructor
    · simp [exponentSize]
    · simpa [exponentSize] using hc x k hk

end OnLeConjecture.KnotFloer.GridFull
