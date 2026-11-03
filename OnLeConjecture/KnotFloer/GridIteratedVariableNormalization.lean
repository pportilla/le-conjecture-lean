/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPartialVariableFiltration
public import OnLeConjecture.KnotFloer.FilteredChainHomotopyEquiv

/-!
# Iterated W factors from concrete grid-variable identifications

Every distinct eliminated column contributes one zero-differential factor W,
with shifts `(M,A)=(0,0),(-1,-1)`. The equivalences, their inverses, and their
inverse homotopies preserve Alexander filtration at every induction step.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- Separate the two homogeneous identified components of the split pair. -/
noncomputable def identifiedPairDoublePieceEquiv (a : Fin n) (s : Finset (Fin n)) (m : ℤ) :
    identifiedConeMaslovPiece G R a s m ≃ₗ[R]
      (identifiedMaslovPiece R G a s m × identifiedMaslovPiece R G a s (m + 1)) where
  toFun c := (⟨c.1.1, c.property.1.1, c.property.2.1⟩,
    ⟨c.1.2, c.property.1.2, c.property.2.2⟩)
  invFun c := ⟨(c.1.1, c.2.1), ⟨c.1.property.1, c.2.property.1⟩,
    c.1.property.2, c.2.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The native split cone is the complex and its degree-minus-one copy. -/
noncomputable def identifiedPairDoubleIso (a b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s) :
    identifiedPairComplex G R a b s hb false ≅ shiftedDouble (identifiedMaslovComplex R G a s) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (identifiedPairDoublePieceEquiv G R a s m).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      rw [identifiedPairComplex_d, shiftedDouble_d,
        identifiedMaslovComplex_d, identifiedMaslovComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Prod.ext <;> apply Subtype.ext <;> rfl)

/-- The split-pair identification preserves the specified shifted Alexander bounds. -/
theorem identifiedPairDoubleIso_hom_preserves (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    (identifiedPairAlexanderFiltration G R a b s hb false).Preserves
      (shiftedDoubleFiltration (identifiedAlexanderFiltration G R a s))
        (identifiedPairDoubleIso G R a b s hb).hom := by
  intro v m c hc
  exact hc

/-- Its inverse preserves the same shifted Alexander bounds. -/
theorem identifiedPairDoubleIso_inv_preserves (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    (shiftedDoubleFiltration (identifiedAlexanderFiltration G R a s)).Preserves
      (identifiedPairAlexanderFiltration G R a b s hb false)
        (identifiedPairDoubleIso G R a b s hb).inv := by
  intro v m c hc
  exact hc

/-- The concrete next identification, including both filtered inverse homotopies. -/
noncomputable def identifiedNormalizationFilteredEquiv (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    FilteredChainHomotopyEquiv (identifiedAlexanderFiltration G R a (insert b s))
      (identifiedPairAlexanderFiltration G R a b s hb false) where
  toHomotopyEquiv := identifiedNormalizationHomotopyEquiv G R hG a b hab s hb
  hom_preserves := identifiedNormalizationHomotopyEquiv_hom_preserves G R hG a b hab s hb
  inv_preserves := identifiedNormalizationHomotopyEquiv_inv_preserves G R hG a b hab s hb
  homotopyHomInvId_preserves := fun _ _ _ _ _ => Submodule.zero_mem _
  homotopyInvHomId_preserves := identifiedNormalizationSplitHomotopy_preserves G R hG a b hab s hb

/-- One new distinct variable relation contributes a fully Alexander-filtered W factor. -/
noncomputable def identifiedNormalizationWEquiv (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    FilteredChainHomotopyEquiv (identifiedAlexanderFiltration G R a (insert b s))
      (shiftedDoubleFiltration (identifiedAlexanderFiltration G R a s)) :=
  (identifiedNormalizationFilteredEquiv G R hG a b hab s hb).trans
    (.ofIso (identifiedPairDoubleIso G R a b s hb)
      (identifiedPairDoubleIso_hom_preserves G R a b s hb)
      (identifiedPairDoubleIso_inv_preserves G R a b s hb))

/-- Equal eliminated-column sets give the identity filtered equivalence. -/
noncomputable def identifiedFiltrationCongr (a : Fin n) {s t : Finset (Fin n)} (h : s = t) :
    FilteredChainHomotopyEquiv (identifiedAlexanderFiltration G R a s)
      (identifiedAlexanderFiltration G R a t) := by
  subst t
  exact .refl _

/-- Equal iteration counts give the identity filtered equivalence. -/
noncomputable def iteratedIdentifiedFiltrationCongr (a : Fin n) {k l : ℕ} (h : k = l) :
    FilteredChainHomotopyEquiv
      (iteratedShiftedDoubleFiltration (identifiedAlexanderFiltration G R a ∅) k)
      (iteratedShiftedDoubleFiltration (identifiedAlexanderFiltration G R a ∅) l) := by
  subst l
  exact .refl _

/-- Iterating distinct coefficient identifications gives the corresponding power of W. -/
noncomputable def iteratedVariableNormalizationEquiv (hG : G.IsKnot) (a : Fin n)
    (l : List (Fin n)) (hl : l.Nodup) (ha : a ∉ l) :
    FilteredChainHomotopyEquiv (identifiedAlexanderFiltration G R a l.toFinset)
      (iteratedShiftedDoubleFiltration (identifiedAlexanderFiltration G R a ∅) l.length) := by
  classical
  induction l with
  | nil => exact .refl _
  | cons b l ih =>
    have hab : a ≠ b := fun h => ha (by simp [h])
    have hb : b ∉ l.toFinset := by simpa using (List.nodup_cons.mp hl).1
    exact (identifiedFiltrationCongr G R a
      (show (b :: l).toFinset = insert b l.toFinset from List.toFinset_cons)).trans
      ((identifiedNormalizationWEquiv G R hG a b hab l.toFinset hb).trans
        ((ih (List.nodup_cons.mp hl).2 (fun h => ha (List.mem_cons_of_mem b h))).shiftedDouble))

/-- Eliminating every O variable except the selected one contributes exactly n−1 factors W. -/
noncomputable def allVariableNormalizationEquiv (hG : G.IsKnot) (a : Fin n) :
    FilteredChainHomotopyEquiv
      (identifiedAlexanderFiltration G R a (Finset.univ.erase a))
      (iteratedShiftedDoubleFiltration (identifiedAlexanderFiltration G R a ∅) (n - 1)) := by
  classical
  have h := iteratedVariableNormalizationEquiv G R hG a (Finset.univ.erase a).toList
    (Finset.nodup_toList _) (by simp)
  have hlen : (Finset.univ.erase a).toList.length = n - 1 := by
    simp only [Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
  exact (identifiedFiltrationCongr G R a (Finset.toList_toFinset _).symm).trans
    (h.trans (iteratedIdentifiedFiltrationCongr G R a hlen))

end OnLeConjecture.KnotFloer.GridFull
