/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridVariableConeSplitting
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Division by the sum of two distinct grid variables

The elementary change of variables `V_b ↦ V_b + V_a` converts `V_a + V_b`
to `V_b` in characteristic two. Mathlib's coefficientwise monomial division
then gives an explicit linear left inverse to multiplication by `V_a + V_b`.
No restriction on the grid differential is used in this division.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti MvPolynomial

variable {n : ℕ} (R : Type*) [CommRing R]

/-- Divide every monomial divisible by the selected variable, discarding the others. -/
noncomputable def divideVariable (b : Fin n) :
    MvPolynomial (Fin n) R →ₗ[R] MvPolynomial (Fin n) R where
  toFun p := p.divMonomial (Finsupp.single b 1)
  map_add' p q := add_divMonomial p q _
  map_smul' a p := by
    ext e
    simp only [RingHom.id_apply, coeff_divMonomial, coeff_smul]

@[simp]
theorem divideVariable_X_mul (b : Fin n) (p : MvPolynomial (Fin n) R) :
    divideVariable R b (X b * p) = p := X_mul_divMonomial b p

/-- The elementary homogeneous variable substitution used for two-variable division. -/
noncomputable def variableSumSubstitution (a b : Fin n) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval fun i => if i = b then X b + X a else X i

@[simp]
theorem variableSumSubstitution_X (a b i : Fin n) :
    variableSumSubstitution R a b (X i) = if i = b then X b + X a else X i := aeval_X _ _

variable [CharP R 2]

/-- For distinct variables the substitution is its own inverse. -/
theorem variableSumSubstitution_involutive (a b : Fin n) (hab : a ≠ b) :
    Function.Involutive (variableSumSubstitution R a b) := by
  have h : (variableSumSubstitution R a b).comp (variableSumSubstitution R a b) =
      AlgHom.id R _ := by
    ext i
    by_cases hi : i = b
    · subst i
      simp [AlgHom.comp_apply, variableSumSubstitution_X, hab, add_assoc, CharTwo.add_self_eq_zero]
    · simp [AlgHom.comp_apply, variableSumSubstitution_X, hi]
  exact fun p => DFunLike.congr_fun h p

/-- The substitution sends the variable relation to a single variable. -/
theorem variableSumSubstitution_relation (a b : Fin n) (hab : a ≠ b) :
    variableSumSubstitution R a b (X a + X b) = X b := by
  simp only [map_add, variableSumSubstitution_X, if_neg hab, ite_true]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

/-- Explicit division by `V_a + V_b`, using only polynomial coefficients. -/
noncomputable def divideVariableSum (a b : Fin n) :
    MvPolynomial (Fin n) R →ₗ[R] MvPolynomial (Fin n) R :=
  (variableSumSubstitution R a b).toLinearMap.comp
    ((divideVariable R b).comp (variableSumSubstitution R a b).toLinearMap)

/-- Division is a left inverse to multiplication by the relation, even with zero divisors in R. -/
theorem divideVariableSum_relation_mul (a b : Fin n) (hab : a ≠ b)
    (p : MvPolynomial (Fin n) R) :
    divideVariableSum R a b ((X a + X b) * p) = p := by
  change variableSumSubstitution R a b
    (divideVariable R b (variableSumSubstitution R a b ((X a + X b) * p))) = p
  rw [map_mul, variableSumSubstitution_relation R a b hab, divideVariable_X_mul]
  exact variableSumSubstitution_involutive R a b hab p

/-- Apply the polynomial division to each coefficient of the actual grid-chain module. -/
noncomputable def variableSumChainDivision (a b : Fin n) :
    GridChainMinus R n →ₗ[R] GridChainMinus R n :=
  Finsupp.mapRange.linearMap (divideVariableSum R a b)

omit [CharP R 2] in
@[simp]
theorem variableSumChainDivision_apply (a b : Fin n) (c : GridChainMinus R n)
    (x : GridState n) :
    variableSumChainDivision R a b c x = divideVariableSum R a b (c x) := rfl

/-- The coefficientwise division splits multiplication by the relation on all grid chains. -/
theorem variableSumChainDivision_relation_smul (a b : Fin n) (hab : a ≠ b)
    (c : GridChainMinus R n) :
    variableSumChainDivision R a b ((X a + X b : MvPolynomial (Fin n) R) • c) = c := by
  apply Finsupp.ext
  intro x
  exact divideVariableSum_relation_mul R a b hab (c x)

/-- Multiplication by the two-variable relation is injective on the grid-chain module. -/
theorem variableSum_smul_injective (a b : Fin n) (hab : a ≠ b) :
    Function.Injective fun c : GridChainMinus R n =>
      (X a + X b : MvPolynomial (Fin n) R) • c :=
  Function.LeftInverse.injective (variableSumChainDivision_relation_smul R a b hab)

omit [CharP R 2] in
/-- The elementary substitution preserves the total degree of each homogeneous monomial. -/
theorem variableSumSubstitution_monomial_homogeneous (a b : Fin n) (e : Fin n →₀ ℕ) (r : R) :
    (variableSumSubstitution R a b (monomial e r)).IsHomogeneous (exponentSize e) := by
  have hm : (monomial e r).IsHomogeneous (exponentSize e) :=
    isHomogeneous_monomial r (Finsupp.degree_eq_sum e)
  have hg (i : Fin n) :
      (if i = b then X b + X a else X i : MvPolynomial (Fin n) R).IsHomogeneous 1 := by
    split
    · exact (isHomogeneous_X R b).add (isHomogeneous_X R a)
    · exact isHomogeneous_X R i
  simpa only [one_mul, variableSumSubstitution] using hm.aeval _ hg

omit [CharP R 2] in
/-- Every output monomial of the substitution comes from an input of the same total degree. -/
theorem exists_support_variableSumSubstitution (a b : Fin n) (p : MvPolynomial (Fin n) R)
    {f : Fin n →₀ ℕ} (hf : f ∈ (variableSumSubstitution R a b p).support) :
    ∃ e ∈ p.support, exponentSize e = exponentSize f := by
  classical
  have hp : variableSumSubstitution R a b p =
      ∑ e ∈ p.support, variableSumSubstitution R a b (monomial e (p.coeff e)) := by
    conv_lhs => rw [as_sum p]
    rw [map_sum]
  rw [hp] at hf
  obtain ⟨e, he, hef⟩ := Finset.mem_biUnion.mp (support_sum hf)
  have h := (variableSumSubstitution_monomial_homogeneous R a b e _).degree_eq_sum_deg_support hef
  exact ⟨e, he, h.trans (Finsupp.degree_eq_sum f)⟩

omit [CharP R 2] in
/-- Every nonzero term of division has input total degree exactly one higher. -/
theorem exists_support_divideVariableSum (a b : Fin n) (p : MvPolynomial (Fin n) R)
    {f : Fin n →₀ ℕ} (hf : f ∈ (divideVariableSum R a b p).support) :
    ∃ e ∈ p.support, exponentSize e = exponentSize f + 1 := by
  change f ∈ (variableSumSubstitution R a b
    (divideVariable R b (variableSumSubstitution R a b p))).support at hf
  obtain ⟨d, hd, hdf⟩ := exists_support_variableSumSubstitution R a b _ hf
  have hd' : Finsupp.single b 1 + d ∈ (variableSumSubstitution R a b p).support := by
    simpa only [mem_support_iff, divideVariable, LinearMap.coe_mk, AddHom.coe_mk,
      coeff_divMonomial] using hd
  obtain ⟨e, he, hed⟩ := exists_support_variableSumSubstitution R a b p hd'
  refine ⟨e, he, ?_⟩
  rw [hed, exponentSize_add, hdf]
  simp [exponentSize, add_comm]

omit [CharP R 2] in
/-- Division raises the actual chain Maslov degree by two. -/
theorem variableSumChainDivision_mem_maslovPiece (G : GridDiagram n) (a b : Fin n)
    {m : ℤ} {c : GridChainMinus R n} (hc : c ∈ maslovPiece G R m) :
    variableSumChainDivision R a b c ∈ maslovPiece G R (m + 2) := by
  rw [mem_maslovPiece] at hc ⊢
  intro x f hf
  obtain ⟨e, he, hef⟩ := exists_support_divideVariableSum R a b (c x) hf
  have h := hc x e he
  simp only [maslovDegree, hef, Nat.cast_add, Nat.cast_one] at h ⊢
  omega

omit [CharP R 2] in
/-- Division has the honest coordinate shift `(1, 1)` for total-exponent filtrations. -/
theorem variableSumChainDivision_mem_bifiltrationLevel (G : GridDiagram n) (a b : Fin n)
    {u v : ℝ} {c : GridChainMinus R n} (hc : c ∈ bifiltrationLevel G R u v) :
    variableSumChainDivision R a b c ∈ bifiltrationLevel G R (u + 1) (v + 1) := by
  rw [mem_bifiltrationLevel_iff] at hc ⊢
  intro x f hf
  obtain ⟨e, he, hef⟩ := exists_support_divideVariableSum R a b (c x) hf
  obtain ⟨h₁, h₂⟩ := hc x e he
  simp only [hef, Nat.cast_add, Nat.cast_one] at h₁ h₂
  constructor <;> linarith

end OnLeConjecture.KnotFloer.GridFull
