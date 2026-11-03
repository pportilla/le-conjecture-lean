/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridOneVariableComplex
public import OnLeConjecture.KnotFloer.GridIteratedVariableNormalization

/-!
# Identification of the one-U complex and its W factors

The actual free R[U] grid complex is isomorphic to the fully identified
coefficient complex. For a knot grid the verified variable eliminations
therefore give a Maslov-graded Alexander-filtered homotopy equivalence
with the uneliminated complex tensored with n−1 copies of W.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- Identifying the selected variable with itself has no effect on the final substitution. -/
theorem identifyVariables_univ_erase (a : Fin n) :
    identifyVariables R a Finset.univ = identifyVariables R a (Finset.univ.erase a) := by
  classical
  ext i : 1
  by_cases hi : i = a
  · subst i
    simp only [identifyVariables_X_selected]
  · simp [identifyVariables_X, hi]

omit [CharP R 2] in
/-- The fully identified representative eliminates exactly all columns except the selected one. -/
theorem oneVariableChainSection_collapse_erase (a : Fin n) (c : GridChainMinus R n) :
    oneVariableChainSection R a (collapseOneVariableChain R c) =
      identifyVariablesChain R a (Finset.univ.erase a) c := by
  rw [oneVariableChainSection_collapse]
  apply Finsupp.ext
  intro x
  exact DFunLike.congr_fun (identifyVariables_univ_erase R a) (c x)

omit [CharP R 2] in
/-- The R[U] coefficient inclusion satisfies every prescribed variable identification. -/
theorem oneVariableChainSection_mem_identified (a : Fin n) (c : OneVariableChain R n) :
    oneVariableChainSection R a c ∈ identifiedChains R a (Finset.univ.erase a) := by
  rw [mem_identifiedChains, ← oneVariableChainSection_collapse_erase,
    collapseOneVariableChain_section]

omit [CharP R 2] in
/-- Coefficient collapse is unchanged by the final representative projection. -/
theorem collapseOneVariableChain_identify (a : Fin n) (c : GridChainMinus R n) :
    collapseOneVariableChain R (identifyVariablesChain R a (Finset.univ.erase a) c) =
      collapseOneVariableChain R c := by
  rw [← oneVariableChainSection_collapse_erase, collapseOneVariableChain_section]

omit [CharP R 2] in
/-- The final identified differential is carried to the actual R[U] rectangle differential. -/
theorem collapseOneVariableChain_identifiedDifferential (a : Fin n) (c : GridChainMinus R n) :
    collapseOneVariableChain R (identifiedDifferential R G a (Finset.univ.erase a) c) =
      oneVariableDifferential R G (collapseOneVariableChain R c) := by
  rw [identifiedDifferential_apply, collapseOneVariableChain_identify,
    collapseOneVariableChain_differential]

/-- The final homogeneous representative module is the homogeneous R[U]-state module. -/
noncomputable def identifiedOneVariablePieceEquiv (a : Fin n) (m : ℤ) :
    identifiedMaslovPiece R G a (Finset.univ.erase a) m ≃ₗ[R]
      oneVariableMaslovPiece R G a m :=
  { toLinearMap := (collapseOneVariableChain R).restrict fun c hc => by
      change oneVariableChainSection R a (collapseOneVariableChain R c) ∈ maslovPiece G R m
      rw [oneVariableChainSection_collapse_erase, (mem_identifiedChains R a _ c).mp hc.2]
      exact hc.1
    invFun := fun c => ⟨oneVariableChainSection R a c, c.property,
      oneVariableChainSection_mem_identified R a c⟩
    left_inv := by
      intro c
      apply Subtype.ext
      change oneVariableChainSection R a (collapseOneVariableChain R c) = c
      rw [oneVariableChainSection_collapse_erase]
      exact (mem_identifiedChains R a _ _).mp c.property.2
    right_inv := fun c => Subtype.ext (collapseOneVariableChain_section R a c) }

/-- The actual one-U grid complex is isomorphic to the final identified coefficient complex. -/
noncomputable def identifiedOneVariableIso (a : Fin n) :
    identifiedMaslovComplex R G a (Finset.univ.erase a) ≅ oneVariableMaslovComplex R G a :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (identifiedOneVariablePieceEquiv G R a m).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      rw [identifiedMaslovComplex_d, oneVariableMaslovComplex_d]
      ext c : 2
      exact Subtype.ext (collapseOneVariableChain_identifiedDifferential G R a
        ((show identifiedMaslovPiece R G a (Finset.univ.erase a) (j + 1) from c) :
          GridChainMinus R n)).symm)

/-- The coefficient-collapse isomorphism preserves Alexander filtration. -/
theorem identifiedOneVariableIso_hom_preserves (a : Fin n) :
    (identifiedAlexanderFiltration G R a (Finset.univ.erase a)).Preserves
      (oneVariableAlexanderFiltration R G a) (identifiedOneVariableIso G R a).hom := by
  intro v m c hc
  change oneVariableChainSection R a (collapseOneVariableChain R
    ((show identifiedMaslovPiece R G a (Finset.univ.erase a) m from c) : GridChainMinus R n)) ∈
      bifiltrationLevel G R 0 v
  rw [oneVariableChainSection_collapse_erase,
    (mem_identifiedChains R a _ _).mp c.property.2]
  exact hc

/-- The selected-variable inverse inclusion preserves Alexander filtration. -/
theorem identifiedOneVariableIso_inv_preserves (a : Fin n) :
    (oneVariableAlexanderFiltration R G a).Preserves
      (identifiedAlexanderFiltration G R a (Finset.univ.erase a))
        (identifiedOneVariableIso G R a).inv := by
  intro v m c hc
  exact hc

/-- The actual R[U] rectangle complex has the proved n−1 shifted W factors. -/
noncomputable def oneVariableNormalizationEquiv (hG : G.IsKnot) (a : Fin n) :
    FilteredChainHomotopyEquiv (oneVariableAlexanderFiltration R G a)
      (iteratedShiftedDoubleFiltration (identifiedAlexanderFiltration G R a ∅) (n - 1)) :=
  (FilteredChainHomotopyEquiv.ofIso (identifiedOneVariableIso G R a).symm
    (identifiedOneVariableIso_inv_preserves G R a)
    (identifiedOneVariableIso_hom_preserves G R a)).trans
      (allVariableNormalizationEquiv G R hG a)

end OnLeConjecture.KnotFloer.GridFull
