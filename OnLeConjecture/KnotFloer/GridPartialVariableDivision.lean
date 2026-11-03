/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPartialVariableComplex

/-!
# Successive division by grid-variable relations

Division by a new relation commutes with every previous coefficient
identification. Thus the next quotient-to-cone comparison can use the same
explicit division on the partially identified complex.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti MvPolynomial

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- Earlier identifications fix the next variable relation. -/
theorem identifyVariables_relation (a b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s) :
    identifyVariables R a s (X a + X b) = X a + X b := by
  simp only [map_add, identifyVariables_X_selected, identifyVariables_X, if_neg hb]

/-- The next quotient projection commutes with all earlier identifications. -/
theorem variableQuotientProjection_identifyVariablesChain (a b : Fin n)
    (s : Finset (Fin n)) (c : GridChainMinus R n) :
    variableQuotientProjection R a b (identifyVariablesChain R a s c) =
      identifyVariablesChain R a s (variableQuotientProjection R a b c) := by
  rw [variableQuotientProjection_eq_identifyVariablesChain]
  have h := DFunLike.congr_fun (identifyVariablesChain_comp R a {b} s) c
  have h' := DFunLike.congr_fun (identifyVariablesChain_comp R a s {b}) c
  rw [Finset.union_comm s {b}] at h'
  exact h.trans h'.symm

/-- The next polynomial division commutes with previous variable identifications. -/
theorem variableSumChainDivision_identifyVariablesChain (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (c : GridChainMinus R n) :
    variableSumChainDivision R a b (identifyVariablesChain R a s c) =
      identifyVariablesChain R a s (variableSumChainDivision R a b c) := by
  apply variableSum_smul_injective R a b hab
  have h := variableQuotientProjection_identifyVariablesChain R a b s c
  rw [variableQuotientProjection_apply, variableQuotientProjection_apply, map_add,
    identifyVariablesChain_smul, identifyVariables_relation R a b s hb] at h
  exact add_left_cancel h

/-- Dividing by the next relation keeps all earlier coefficient identifications. -/
theorem variableSumChainDivision_mem_identifiedChains (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) {c : GridChainMinus R n}
    (hc : c ∈ identifiedChains R a s) :
    variableSumChainDivision R a b c ∈ identifiedChains R a s := by
  rw [mem_identifiedChains] at hc ⊢
  rw [← variableSumChainDivision_identifyVariablesChain R a b hab s hb, hc]

omit [CharP R 2] in
/-- The next relation acts within the earlier identified coefficient module. -/
theorem relation_smul_mem_identifiedChains (a b : Fin n) (s : Finset (Fin n))
    (hb : b ∉ s) {c : GridChainMinus R n} (hc : c ∈ identifiedChains R a s) :
    (X a + X b : MvPolynomial (Fin n) R) • c ∈ identifiedChains R a s := by
  rw [mem_identifiedChains] at hc ⊢
  rw [identifyVariablesChain_smul, identifyVariables_relation R a b s hb, hc]

omit [CharP R 2] in
/-- The identified rectangle differential commutes with multiplication by the next relation. -/
theorem identifiedDifferential_relation_smul (G : GridDiagram n) (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) (c : GridChainMinus R n) :
    identifiedDifferential R G a s ((X a + X b : MvPolynomial (Fin n) R) • c) =
      (X a + X b : MvPolynomial (Fin n) R) • identifiedDifferential R G a s c := by
  simp only [identifiedDifferential_apply, map_smul, identifyVariablesChain_smul,
    identifyVariables_relation R a b s hb]

/-- The next quotient projection applied after earlier identifications eliminates their union. -/
theorem quotientProjection_identifyVariablesChain_insert (a b : Fin n)
    (s : Finset (Fin n)) (c : GridChainMinus R n) :
    variableQuotientProjection R a b (identifyVariablesChain R a s c) =
      identifyVariablesChain R a (insert b s) c := by
  rw [variableQuotientProjection_eq_identifyVariablesChain]
  simpa only [Finset.singleton_union, LinearMap.comp_apply] using
    DFunLike.congr_fun (identifyVariablesChain_comp R a {b} s) c

/-- On already identified chains, the next projection lands in the enlarged identification. -/
theorem quotientProjection_mem_identifiedChains_insert (a b : Fin n)
    (s : Finset (Fin n)) {c : GridChainMinus R n} (hc : c ∈ identifiedChains R a s) :
    variableQuotientProjection R a b c ∈ identifiedChains R a (insert b s) := by
  rw [mem_identifiedChains] at hc
  rw [← hc, quotientProjection_identifyVariablesChain_insert]
  exact identifyVariablesChain_mem_identifiedChains R a (insert b s) c

omit [CharP R 2] in
/-- Projection onto a larger identified set absorbs every earlier projection. -/
theorem identifyVariablesChain_absorb (a : Fin n) {s t : Finset (Fin n)} (hst : s ⊆ t)
    (c : GridChainMinus R n) :
    identifyVariablesChain R a t (identifyVariablesChain R a s c) =
      identifyVariablesChain R a t c := by
  simpa only [Finset.union_eq_left.mpr hst, LinearMap.comp_apply] using
    DFunLike.congr_fun (identifyVariablesChain_comp R a t s) c

omit [CharP R 2] in
/-- A chain satisfying more identifications also satisfies every earlier one. -/
theorem identifiedChains_antitone (a : Fin n) {s t : Finset (Fin n)} (hst : s ⊆ t) :
    identifiedChains R a t ≤ identifiedChains R a s := by
  intro c hc
  rw [mem_identifiedChains] at hc ⊢
  have h := DFunLike.congr_fun (identifyVariablesChain_comp R a s t) c
  rw [Finset.union_eq_right.mpr hst] at h
  simpa only [LinearMap.comp_apply, hc] using h

omit [CharP R 2] in
/-- Enlarging the coefficient identification after any polynomial-linear map is well-defined. -/
theorem identifyVariablesChain_linear_absorb (a : Fin n) {s t : Finset (Fin n)}
    (hst : s ⊆ t)
    (T : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
    (c : GridChainMinus R n) :
    identifyVariablesChain R a t (T (identifyVariablesChain R a s c)) =
      identifyVariablesChain R a t (T c) := by
  calc
    _ = identifyVariablesChain R a t
        (T (identifyVariablesChain R a t (identifyVariablesChain R a s c))) :=
      (identifyVariablesChain_linear_projection R a t T _).symm
    _ = _ := by rw [identifyVariablesChain_absorb R a hst,
      identifyVariablesChain_linear_projection]

omit [CharP R 2] in
/-- Successive identified differentials agree with identifying their full union directly. -/
theorem identifyVariablesChain_identifiedDifferential (G : GridDiagram n) (a : Fin n)
    {s t : Finset (Fin n)} (hst : s ⊆ t) (c : GridChainMinus R n) :
    identifyVariablesChain R a t (identifiedDifferential R G a s c) =
      identifiedDifferential R G a t (identifyVariablesChain R a t c) := by
  simp only [identifiedDifferential_apply, identifyVariablesChain_absorb R a hst,
    identifyVariablesChain_linear_projection]

/-- The divided correction identity remains valid after any earlier coefficient identifications. -/
theorem division_identifiedDifferential_projection (G : GridDiagram n)
    (a b : Fin n) (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s)
    (c : GridChainMinus R n) :
    variableSumChainDivision R a b
      (identifiedDifferential R G a s (variableQuotientProjection R a b c)) =
      identifiedDifferential R G a s (variableSumChainDivision R a b c) +
        variableSumChainDivision R a b (identifiedDifferential R G a s c) := by
  rw [variableQuotientProjection_apply, map_add,
    identifiedDifferential_relation_smul R G a b s hb, map_add,
    variableSumChainDivision_relation_smul R a b hab, add_comm]

end OnLeConjecture.KnotFloer.GridFull
