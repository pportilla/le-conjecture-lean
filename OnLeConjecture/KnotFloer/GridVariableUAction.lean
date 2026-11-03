/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridOneVariableNormalizationFull

/-!
# Selected-variable linearity of the actual normalization maps

The coefficient projection and the explicit division by `V_a+V_b` commute
with every polynomial in the retained variable `V_a`. Hence the actual
quotient comparisons, geometric cone shear, and divided inverse homotopy
commute with its degree-minus-two U action.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti MvPolynomial

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- Every partial identification fixes polynomials in the retained variable. -/
theorem identifyVariables_oneVariableSection (a : Fin n) (s : Finset (Fin n))
    (p : Polynomial R) :
    identifyVariables R a s (oneVariableSection R a p) = oneVariableSection R a p := by
  have h : (identifyVariables R a s).comp (oneVariableSection R a) = oneVariableSection R a := by
    ext
    simp [oneVariableSection]
  exact DFunLike.congr_fun h p

omit [CharP R 2] in
/-- Each coefficient projection is linear over polynomials in the retained variable. -/
theorem identifyVariablesChain_selected_smul (a : Fin n) (s : Finset (Fin n))
    (p : Polynomial R) (c : GridChainMinus R n) :
    identifyVariablesChain R a s (oneVariableSection R a p • c) =
      oneVariableSection R a p • identifyVariablesChain R a s c := by
  rw [identifyVariablesChain_smul, identifyVariables_oneVariableSection]

/-- Division commutes with any scalar fixed by the next coefficient identification. -/
theorem variableSumChainDivision_smul_of_fixed (a b : Fin n) (hab : a ≠ b)
    (p : MvPolynomial (Fin n) R) (hp : identifyVariables R a {b} p = p)
    (c : GridChainMinus R n) :
    variableSumChainDivision R a b (p • c) = p • variableSumChainDivision R a b c := by
  apply variableSum_smul_injective R a b hab
  have h : variableQuotientProjection R a b (p • c) =
      p • variableQuotientProjection R a b c := by
    rw [variableQuotientProjection_eq_identifyVariablesChain, identifyVariablesChain_smul, hp]
  rw [variableQuotientProjection_apply, variableQuotientProjection_apply, smul_add,
    smul_comm p (X a + X b)] at h
  exact add_left_cancel h

/-- The actual division is linear over every polynomial in the retained variable. -/
theorem variableSumChainDivision_selected_smul (a b : Fin n) (hab : a ≠ b)
    (p : Polynomial R) (c : GridChainMinus R n) :
    variableSumChainDivision R a b (oneVariableSection R a p • c) =
      oneVariableSection R a p • variableSumChainDivision R a b c :=
  variableSumChainDivision_smul_of_fixed R a b hab _
    (identifyVariables_oneVariableSection R a {b} p) c

/-- The next quotient projection is linear over the retained-variable polynomial ring. -/
theorem variableQuotientProjection_selected_smul (a b : Fin n) (p : Polynomial R)
    (c : GridChainMinus R n) :
    variableQuotientProjection R a b (oneVariableSection R a p • c) =
      oneVariableSection R a p • variableQuotientProjection R a b c := by
  rw [variableQuotientProjection_eq_identifyVariablesChain,
    identifyVariablesChain_selected_smul]

omit [CharP R 2] in
/-- The partially identified rectangle differential is linear over the retained variable. -/
theorem identifiedDifferential_selected_smul (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) (p : Polynomial R) (c : GridChainMinus R n) :
    identifiedDifferential R G a s (oneVariableSection R a p • c) =
      oneVariableSection R a p • identifiedDifferential R G a s c := by
  rw [identifiedDifferential_apply, map_smul, identifyVariablesChain_selected_smul]
  rfl

omit [CharP R 2] in
/-- The projected geometric X-marking homotopy is linear over the retained variable. -/
theorem identifiedVariableHomotopy_selected_smul (G : GridDiagram n) (hG : G.IsKnot)
    (a b : Fin n) (s : Finset (Fin n)) (p : Polynomial R) (c : GridChainMinus R n) :
    identifiedVariableHomotopy R G hG a b s (oneVariableSection R a p • c) =
      oneVariableSection R a p • identifiedVariableHomotopy R G hG a b s c := by
  rw [identifiedVariableHomotopy_apply, map_smul, identifyVariablesChain_selected_smul]
  rfl

/-- The corrected next quotient inclusion is linear over the retained-variable polynomial ring. -/
theorem identifiedQuotientToCone_selected_smul (G : GridDiagram n) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (p : Polynomial R) (c : GridChainMinus R n) :
    identifiedQuotientToCone G R a b s (oneVariableSection R a p • c) =
      oneVariableSection R a p • identifiedQuotientToCone G R a b s c := by
  apply Prod.ext
  · rfl
  · change variableSumChainDivision R a b
      (identifiedDifferential R G a s (oneVariableSection R a p • c)) =
        oneVariableSection R a p •
          variableSumChainDivision R a b (identifiedDifferential R G a s c)
    rw [identifiedDifferential_selected_smul, variableSumChainDivision_selected_smul R a b hab]

/-- The next cone projection is linear over the retained-variable polynomial ring. -/
theorem identifiedConeToQuotient_selected_smul (a b : Fin n) (p : Polynomial R)
    (c : VariableConeChains R n) :
    identifiedConeToQuotient R a b (oneVariableSection R a p • c) =
      oneVariableSection R a p • identifiedConeToQuotient R a b c :=
  variableQuotientProjection_selected_smul R a b p c.1

/-- The explicit divided inverse homotopy is linear over the retained-variable polynomial ring. -/
theorem variableQuotientConeHomotopy_selected_smul (a b : Fin n) (hab : a ≠ b)
    (p : Polynomial R) (c : VariableConeChains R n) :
    variableQuotientConeHomotopy R a b (oneVariableSection R a p • c) =
      oneVariableSection R a p • variableQuotientConeHomotopy R a b c := by
  apply Prod.ext
  · exact (smul_zero _).symm
  · exact variableSumChainDivision_selected_smul R a b hab p c.1

omit [CharP R 2] in
/-- The geometric cone shear is linear over every polynomial in the retained variable. -/
theorem identifiedConeShear_selected_smul (G : GridDiagram n) (hG : G.IsKnot)
    (a b : Fin n) (s : Finset (Fin n)) (p : Polynomial R) (c : VariableConeChains R n) :
    identifiedConeShear G R hG a b s (oneVariableSection R a p • c) =
      oneVariableSection R a p • identifiedConeShear G R hG a b s c := by
  apply Prod.ext
  · change oneVariableSection R a p • c.1 +
      identifiedVariableHomotopy R G hG a b s (oneVariableSection R a p • c.2) =
        oneVariableSection R a p • (c.1 + identifiedVariableHomotopy R G hG a b s c.2)
    rw [identifiedVariableHomotopy_selected_smul, smul_add]
  · rfl

omit [CharP R 2] in
/-- The actual R[U] inclusion is semilinear for U mapped to the retained O variable. -/
theorem oneVariableChainSection_smul (a : Fin n) (p : Polynomial R) (c : OneVariableChain R n) :
    oneVariableChainSection R a (p • c) =
      oneVariableSection R a p • oneVariableChainSection R a c := by
  apply Finsupp.ext
  intro x
  exact map_mul (oneVariableSection R a) p (c x)

omit [CharP R 2] in
/-- The coefficient collapse intertwines every retained-variable scalar with the same U scalar. -/
theorem collapseOneVariableChain_selected_smul (a : Fin n) (p : Polynomial R)
    (c : GridChainMinus R n) :
    collapseOneVariableChain R (oneVariableSection R a p • c) =
      p • collapseOneVariableChain R c := by
  apply Finsupp.ext
  intro x
  change collapseToOneVariable R (oneVariableSection R a p * c x) =
    p * collapseToOneVariable R (c x)
  rw [map_mul, collapseToOneVariable_section]

end OnLeConjecture.KnotFloer.GridFull
