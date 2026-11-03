/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridVariableQuotientCone
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Explicit successive identifications of grid variables

The division-defined quotient representative is proved to be the polynomial
substitution `V_b ↦ V_a`. Identifying any finite set of variables with `V_a`
then gives commuting, idempotent coefficient projections. These statements
identify the concrete coefficient operations required for iterating the
single-relation normalization.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti MvPolynomial

variable {n : ℕ} (R : Type*) [CommRing R]

/-- Identify the variable in column b with the variable in column a. -/
noncomputable def identifyVariable (a b : Fin n) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  rename fun i => if i = b then a else i

@[simp]
theorem identifyVariable_X (a b i : Fin n) :
    identifyVariable R a b (X i) = X (if i = b then a else i) := rename_X _ _

/-- The eliminated variable does not occur in the substituted polynomial. -/
theorem notMem_vars_identifyVariable (a b : Fin n) (hab : a ≠ b)
    (p : MvPolynomial (Fin n) R) : b ∉ (identifyVariable R a b p).vars := by
  intro h
  obtain ⟨i, _, hi⟩ := mem_vars_rename _ p h
  by_cases hib : i = b
  · exact hab (by simpa [hib] using hi)
  · simp [hib] at hi

/-- Division by the eliminated variable vanishes after the identification. -/
theorem divideVariable_identifyVariable (a b : Fin n) (hab : a ≠ b)
    (p : MvPolynomial (Fin n) R) : divideVariable R b (identifyVariable R a b p) = 0 := by
  ext e
  change (identifyVariable R a b p).coeff (Finsupp.single b 1 + e) = 0
  rw [← notMem_support_iff]
  intro he
  apply notMem_vars_identifyVariable R a b hab p
  exact (mem_vars_iff_mem_support _).mpr ⟨Finsupp.single b 1 + e, he, by simp⟩

/-- The homogeneous change of variables fixes the identified polynomial. -/
theorem variableSumSubstitution_identifyVariable (a b : Fin n) (hab : a ≠ b)
    (p : MvPolynomial (Fin n) R) :
    variableSumSubstitution R a b (identifyVariable R a b p) = identifyVariable R a b p := by
  have h : (variableSumSubstitution R a b).comp (identifyVariable R a b) =
      identifyVariable R a b := by
    ext i : 1
    by_cases hi : i = b
    · simp [AlgHom.comp_apply, identifyVariable_X, hi, variableSumSubstitution_X, hab]
    · simp [AlgHom.comp_apply, identifyVariable_X, hi, variableSumSubstitution_X]
  exact DFunLike.congr_fun h p

/-- Division by the variable relation vanishes on the identified coefficients. -/
theorem divideVariableSum_identifyVariable (a b : Fin n) (hab : a ≠ b)
    (p : MvPolynomial (Fin n) R) : divideVariableSum R a b (identifyVariable R a b p) = 0 := by
  change variableSumSubstitution R a b
    (divideVariable R b (variableSumSubstitution R a b (identifyVariable R a b p))) = 0
  rw [variableSumSubstitution_identifyVariable R a b hab,
    divideVariable_identifyVariable R a b hab, map_zero]

variable [CharP R 2]

/-- A polynomial and its variable identification differ by a multiple of the relation. -/
theorem variableRelation_dvd_sub_identifyVariable (a b : Fin n) (p : MvPolynomial (Fin n) R) :
    X a + X b ∣ p - identifyVariable R a b p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [identifyVariable]
  | add p q hp hq =>
    rw [map_add, show p + q - (identifyVariable R a b p + identifyVariable R a b q) =
      (p - identifyVariable R a b p) + (q - identifyVariable R a b q) by ring]
    exact dvd_add hp hq
  | mul_X p i hp =>
    have hi : X a + X b ∣ X i - identifyVariable R a b (X i) := by
      by_cases hib : i = b
      · subst i
        simp [identifyVariable_X, CharTwo.sub_eq_add, add_comm]
      · simp [identifyVariable_X, hib]
    rw [map_mul, show p * X i - identifyVariable R a b p * identifyVariable R a b (X i) =
      (p - identifyVariable R a b p) * X i +
        identifyVariable R a b p * (X i - identifyVariable R a b (X i)) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hi _)

/-- The division-defined polynomial representative is exactly variable identification. -/
theorem polynomial_projection_eq_identifyVariable (a b : Fin n) (hab : a ≠ b)
    (p : MvPolynomial (Fin n) R) :
    p + (X a + X b) * divideVariableSum R a b p = identifyVariable R a b p := by
  obtain ⟨q, hq⟩ := variableRelation_dvd_sub_identifyVariable R a b p
  have hp : p = (X a + X b) * q + identifyVariable R a b p := sub_eq_iff_eq_add.mp hq
  have hdiv : divideVariableSum R a b p = q := by
    rw [hp, map_add, divideVariableSum_relation_mul R a b hab,
      divideVariableSum_identifyVariable R a b hab, add_zero]
  rw [hdiv]
  nth_rw 1 [hp]
  calc
    _ = ((X a + X b) * q + (X a + X b) * q) + identifyVariable R a b p := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- The actual grid-chain quotient projection is coefficientwise variable identification. -/
theorem variableQuotientProjection_apply_eq_identifyVariable (a b : Fin n) (hab : a ≠ b)
    (c : GridChainMinus R n) (x : GridState n) :
    variableQuotientProjection R a b c x = identifyVariable R a b (c x) :=
  polynomial_projection_eq_identifyVariable R a b hab (c x)

/-- Identify every variable in a finite set with one selected variable. -/
noncomputable def identifyVariables (a : Fin n) (s : Finset (Fin n)) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  rename fun i => if i ∈ s then a else i

omit [CharP R 2] in
@[simp]
theorem identifyVariables_X (a : Fin n) (s : Finset (Fin n)) (i : Fin n) :
    identifyVariables R a s (X i) = X (if i ∈ s then a else i) := rename_X _ _

omit [CharP R 2] in
/-- The selected variable is fixed by every stage of identification. -/
theorem identifyVariables_X_selected (a : Fin n) (s : Finset (Fin n)) :
    identifyVariables R a s (X a) = X a := by simp

omit [CharP R 2] in
/-- Successive identifications are exactly identification of the union of their variables. -/
theorem identifyVariables_comp (a : Fin n) (s t : Finset (Fin n)) :
    (identifyVariables R a s).comp (identifyVariables R a t) = identifyVariables R a (s ∪ t) := by
  ext i : 1
  by_cases hit : i ∈ t
  · simp [AlgHom.comp_apply, identifyVariables_X, hit]
  · by_cases his : i ∈ s <;>
      simp [AlgHom.comp_apply, identifyVariables_X, hit, his]

omit [CharP R 2] in
/-- The order of eliminating variables does not affect the coefficient projection. -/
theorem identifyVariables_commute (a : Fin n) (s t : Finset (Fin n)) :
    Function.Commute (identifyVariables R a s) (identifyVariables R a t) := by
  intro p
  have h := DFunLike.congr_fun (identifyVariables_comp R a s t) p
  have h' := DFunLike.congr_fun (identifyVariables_comp R a t s) p
  rw [Finset.union_comm t s] at h'
  exact h.trans h'.symm

omit [CharP R 2] in
/-- Every finite identification is a projection. -/
theorem identifyVariables_idempotent (a : Fin n) (s : Finset (Fin n)) (p : MvPolynomial (Fin n) R) :
    identifyVariables R a s (identifyVariables R a s p) = identifyVariables R a s p := by
  simpa only [Finset.union_self, AlgHom.comp_apply] using
    DFunLike.congr_fun (identifyVariables_comp R a s s) p

/-- The finite coefficient identification on the actual grid-state module. -/
noncomputable def identifyVariablesChain (a : Fin n) (s : Finset (Fin n)) :
    GridChainMinus R n →ₗ[R] GridChainMinus R n :=
  Finsupp.mapRange.linearMap (identifyVariables R a s).toLinearMap

omit [CharP R 2] in
@[simp]
theorem identifyVariablesChain_apply (a : Fin n) (s : Finset (Fin n))
    (c : GridChainMinus R n) (x : GridState n) :
    identifyVariablesChain R a s c x = identifyVariables R a s (c x) := rfl

omit [CharP R 2] in
/-- Consecutive coefficient projections identify the union of their columns on every chain. -/
theorem identifyVariablesChain_comp (a : Fin n) (s t : Finset (Fin n)) :
    (identifyVariablesChain R a s).comp (identifyVariablesChain R a t) =
      identifyVariablesChain R a (s ∪ t) := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro x
  exact DFunLike.congr_fun (identifyVariables_comp R a s t) (c x)

/-- The quotient projection agrees with identifying a singleton of columns. -/
theorem variableQuotientProjection_eq_identifyVariablesChain (a b : Fin n) :
    variableQuotientProjection R a b = identifyVariablesChain R a {b} := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro x
  by_cases hab : a = b
  · subst b
    have hid : (fun i : Fin n => if i = a then a else i) = id := by
      funext i
      split <;> simp_all
    simp [variableQuotientProjection_apply, CharTwo.add_self_eq_zero,
      identifyVariablesChain_apply, identifyVariables, hid]
  · rw [variableQuotientProjection_apply_eq_identifyVariable R a b hab]
    simp only [identifyVariablesChain_apply, identifyVariable, identifyVariables,
      Finset.mem_singleton]

/-- Apply the actual quotient projections successively in a specified order. -/
noncomputable def iteratedVariableProjection (a : Fin n) : List (Fin n) →
    (GridChainMinus R n →ₗ[R] GridChainMinus R n)
  | [] => LinearMap.id
  | b :: l => (variableQuotientProjection R a b).comp (iteratedVariableProjection a l)

/-- The actual succession of quotient projections depends only on the set of eliminated columns. -/
theorem iteratedVariableProjection_eq (a : Fin n) (l : List (Fin n)) :
    iteratedVariableProjection R a l = identifyVariablesChain R a l.toFinset := by
  induction l with
  | nil =>
    apply LinearMap.ext
    intro c
    apply Finsupp.ext
    intro x
    simp only [iteratedVariableProjection, LinearMap.id_apply, List.toFinset_nil,
      identifyVariablesChain_apply, identifyVariables, Finset.notMem_empty, ite_false]
    exact (rename_id_apply (c x)).symm
  | cons b l ih =>
    rw [iteratedVariableProjection, variableQuotientProjection_eq_identifyVariablesChain,
      ih, identifyVariablesChain_comp]
    simp only [List.toFinset_cons, Finset.singleton_union]

/-- Map every O variable to the single polynomial variable U. -/
noncomputable def collapseToOneVariable : MvPolynomial (Fin n) R →ₐ[R] Polynomial R :=
  aeval fun _ => Polynomial.X

/-- Embed the single-variable coefficient ring using the selected O variable. -/
noncomputable def oneVariableSection (a : Fin n) :
    Polynomial R →ₐ[R] MvPolynomial (Fin n) R := Polynomial.aeval (X a)

omit [CharP R 2] in
@[simp]
theorem collapseToOneVariable_X (i : Fin n) :
    collapseToOneVariable R (X i) = Polynomial.X := aeval_X _ _

omit [CharP R 2] in
/-- The selected-variable inclusion is a section of the coefficient collapse. -/
theorem collapseToOneVariable_section (a : Fin n) (p : Polynomial R) :
    collapseToOneVariable R (oneVariableSection R a p) = p := by
  have h : (collapseToOneVariable R).comp (oneVariableSection R a) = AlgHom.id R _ := by
    ext
    simp [oneVariableSection]
  exact DFunLike.congr_fun h p

omit [CharP R 2] in
/-- The final identification of every column is precisely collapse followed by its section. -/
theorem oneVariableSection_collapse (a : Fin n) (p : MvPolynomial (Fin n) R) :
    oneVariableSection R a (collapseToOneVariable R p) = identifyVariables R a Finset.univ p := by
  have h : (oneVariableSection R a).comp (collapseToOneVariable R) =
      identifyVariables R a Finset.univ := by
    ext i : 1
    simp [AlgHom.comp_apply, oneVariableSection]
  exact DFunLike.congr_fun h p

/-- All variable-identification relations, as an ideal of the actual coefficient ring. -/
noncomputable def variableIdentificationIdeal (a : Fin n) : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun b : Fin n => (X a + X b : MvPolynomial (Fin n) R))

/-- Every coefficient differs from its one-variable representative by the identification ideal. -/
theorem sub_oneVariableSection_collapse_mem (a : Fin n) (p : MvPolynomial (Fin n) R) :
    p - oneVariableSection R a (collapseToOneVariable R p) ∈ variableIdentificationIdeal R a := by
  let E := (oneVariableSection R a).comp (collapseToOneVariable R (n := n))
  change p - E p ∈ variableIdentificationIdeal R a
  induction p using MvPolynomial.induction_on with
  | C r => simp [E]
  | add p q hp hq =>
    rw [map_add, show p + q - (E p + E q) = (p - E p) + (q - E q) by ring]
    exact (variableIdentificationIdeal R a).add_mem hp hq
  | mul_X p i hp =>
    have hi : X i - E (X i) ∈ variableIdentificationIdeal R a := by
      have h := Ideal.subset_span (s := Set.range fun b : Fin n =>
        (X a + X b : MvPolynomial (Fin n) R)) ⟨i, rfl⟩
      simpa [E, oneVariableSection, CharTwo.sub_eq_add, add_comm,
        variableIdentificationIdeal] using h
    rw [map_mul, show p * X i - E p * E (X i) =
      (p - E p) * X i + E p * (X i - E (X i)) by ring]
    exact (variableIdentificationIdeal R a).add_mem
      (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hi)

/-- The kernel of collapse is exactly the ideal generated by all O-variable relations. -/
theorem ker_collapseToOneVariable (a : Fin n) :
    RingHom.ker (collapseToOneVariable R (n := n)).toRingHom = variableIdentificationIdeal R a := by
  apply le_antisymm
  · intro p hp
    have h := sub_oneVariableSection_collapse_mem R a p
    change collapseToOneVariable R p = 0 at hp
    simpa only [hp, map_zero, sub_zero] using h
  · apply Ideal.span_le.mpr
    rintro _ ⟨b, rfl⟩
    change collapseToOneVariable R (X a + X b) = 0
    simp [CharTwo.add_self_eq_zero]

/-- The genuine quotient coefficient ring after all identifications is R[U]. -/
noncomputable def oneVariableCoefficientQuotientEquiv (a : Fin n) :
    (MvPolynomial (Fin n) R ⧸ variableIdentificationIdeal R a) ≃ₐ[R] Polynomial R := by
  rw [← ker_collapseToOneVariable R a]
  exact Ideal.quotientKerAlgEquivOfSurjective
    (fun p => ⟨oneVariableSection R a p, collapseToOneVariable_section R a p⟩)

end OnLeConjecture.KnotFloer.GridFull
