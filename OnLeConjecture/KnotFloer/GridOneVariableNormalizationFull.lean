/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridOneVariableNormalization
public import OnLeConjecture.KnotFloer.GridOneVariableGrading
public import OnLeConjecture.KnotFloer.GridFullMaslovBifiltration

/-!
# The full one-variable grid normalization

For a knot grid, the actual full R[U] rectangle complex is Alexander-filtered
chain homotopy equivalent to the original full polynomial grid complex with
n−1 factors W. The latter has zero differential and shifts `(M,A)=(0,0),(-1,-1)`.
The maps and both inverse homotopies are constructed and filtration-preserving.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- Identifying an empty set leaves every original polynomial grid chain unchanged. -/
theorem identifyVariablesChain_empty (a : Fin n) (c : GridChainMinus R n) :
    identifyVariablesChain R a ∅ c = c := by
  apply Finsupp.ext
  intro x
  simp only [identifyVariablesChain_apply, identifyVariables, Finset.notMem_empty, ite_false]
  exact rename_id_apply _

omit [CharP R 2] in
/-- The differential without identifications is exactly the original rectangle differential. -/
theorem identifiedDifferential_empty (a : Fin n) (c : GridChainMinus R n) :
    identifiedDifferential R G a ∅ c = differential G R c :=
  identifyVariablesChain_empty R a _

/-- The uneliminated homogeneous representative module is the original homogeneous chain module. -/
noncomputable def emptyIdentifiedPieceEquiv (a : Fin n) (m : ℤ) :
    identifiedMaslovPiece R G a ∅ m ≃ₗ[R] maslovPiece G R m :=
  { toLinearMap := Submodule.inclusion inf_le_left
    invFun := fun c => ⟨c, c.property,
      (mem_identifiedChains R a ∅ c).mpr (identifyVariablesChain_empty R a c)⟩
    left_inv _ := rfl
    right_inv _ := rfl }

/-- The empty identified complex is isomorphic to the original full Maslov complex. -/
noncomputable def emptyIdentifiedIso (a : Fin n) :
    identifiedMaslovComplex R G a ∅ ≅ maslovComplex G R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => ((emptyIdentifiedPieceEquiv G R a m).trans
      (maslovChainEquiv G R m).symm).toModuleIso) (by
        intro i j hij
        rw [ComplexShape.down_Rel] at hij
        subst i
        rw [identifiedMaslovComplex_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro c
        apply (maslovChainEquiv G R j).injective
        apply Subtype.ext
        change (maslovChainEquiv G R j ((maslovComplex G R).d (j + 1) j
          ((maslovChainEquiv G R (j + 1)).symm (emptyIdentifiedPieceEquiv G R a (j + 1) c))) :
            GridChainMinus R n) = _
        rw [maslovChainEquiv_d, LinearEquiv.apply_symm_apply]
        exact (identifiedDifferential_empty G R a
          ((show identifiedMaslovPiece R G a ∅ (j + 1) from c) : GridChainMinus R n)).symm)

/-- The Alexander coordinate of the original full polynomial grid complex. -/
noncomputable def originalAlexanderFiltration : RealFiltration (maslovComplex G R) where
  level v m := (maslovBifiltration G R).level 0 v m
  mono m v v' hv := (maslovBifiltration G R).mono m 0 v 0 v' le_rfl hv
  differential_mem v i j c hc := (maslovBifiltration G R).differential_mem 0 v i j c hc

/-- Removing the empty identification preserves the original Alexander coordinate. -/
theorem emptyIdentifiedIso_hom_preserves (a : Fin n) :
    (identifiedAlexanderFiltration G R a ∅).Preserves
      (originalAlexanderFiltration G R) (emptyIdentifiedIso G R a).hom := by
  intro v m c hc
  change (maslovChainEquiv G R m ((maslovChainEquiv G R m).symm
    (emptyIdentifiedPieceEquiv G R a m c)) : GridChainMinus R n) ∈ bifiltrationLevel G R 0 v
  rw [LinearEquiv.apply_symm_apply]
  exact hc

/-- The inverse empty-identification isomorphism preserves the original Alexander coordinate. -/
theorem emptyIdentifiedIso_inv_preserves (a : Fin n) :
    (originalAlexanderFiltration G R).Preserves
      (identifiedAlexanderFiltration G R a ∅) (emptyIdentifiedIso G R a).inv := by
  intro v m c hc
  exact hc

/-- Full one-U normalization, with the genuine original rectangle complex and n−1 W factors. -/
noncomputable def oneVariableFullNormalizationEquiv (hG : G.IsKnot) (a : Fin n) :
    FilteredChainHomotopyEquiv (oneVariableAlexanderFiltration R G a)
      (iteratedShiftedDoubleFiltration (originalAlexanderFiltration G R) (n - 1)) :=
  (oneVariableNormalizationEquiv G R hG a).trans
    ((FilteredChainHomotopyEquiv.ofIso (emptyIdentifiedIso G R a)
      (emptyIdentifiedIso_hom_preserves G R a)
      (emptyIdentifiedIso_inv_preserves G R a)).iteratedShiftedDouble (n - 1))

end OnLeConjecture.KnotFloer.GridFull
