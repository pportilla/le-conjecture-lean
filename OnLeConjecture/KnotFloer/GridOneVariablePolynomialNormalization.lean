/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridSelectedVariableNormalization
public import OnLeConjecture.KnotFloer.ModuleDoubleComplex

/-!
# The full normalization over R[U]

All n−1 variable identifications are iterated as polynomial-linear native
homotopy equivalences. The total two-copy factors retain the explicit maps
underlying the previously proved graded W factors. The latter determine
their Maslov and Alexander shifts, which are forgotten in this total complex.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2] (G : GridDiagram n)

/-- Split the fixed pair of chains into two fixed-chain modules, over R[U]. -/
noncomputable def selectedPairDoubleEquiv (a : Fin n) (s : Finset (Fin n)) :
    selectedIdentifiedPairModule R a s ≃ₗ[Polynomial R]
      (selectedIdentifiedModule R a s × selectedIdentifiedModule R a s) where
  toFun c := (⟨c.val.1, c.property.1⟩, ⟨c.val.2, c.property.2⟩)
  invFun c := ⟨(c.1.val, c.2.val), c.1.property, c.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The split differential is exactly two copies of the earlier identified differential. -/
noncomputable def selectedPairDoubleIso (a b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s) :
    selectedPairComplex R G a b s hb false ≅
      ((moduleDoubleFunctor (Polynomial R)).mapHomologicalComplex (ComplexShape.refl Unit)).obj
        (selectedIdentifiedComplex R G a s) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (selectedPairDoubleEquiv R a s).toModuleIso) (by
      intro _ _ _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      rfl)

/-- One distinct variable identification adds a two-copy factor over R[U]. -/
noncomputable def selectedNormalizationDoubleEquiv (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    HomotopyEquiv (selectedIdentifiedComplex R G a (insert b s))
      (((moduleDoubleFunctor (Polynomial R)).mapHomologicalComplex (ComplexShape.refl Unit)).obj
        (selectedIdentifiedComplex R G a s)) :=
  (selectedVariableNormalizationEquiv R G hG a b hab s hb).trans
    (.ofIso (selectedPairDoubleIso R G a b s hb))

/-- Reindex an identified total complex along equality of the eliminated sets. -/
noncomputable def selectedComplexCongr (a : Fin n) {s t : Finset (Fin n)} (h : s = t) :
    HomotopyEquiv (selectedIdentifiedComplex R G a s) (selectedIdentifiedComplex R G a t) := by
  subst t
  exact .refl _

/-- Reindex the number of total two-copy factors along equality. -/
noncomputable def selectedDoubleCountCongr (a : Fin n) {k l : ℕ} (h : k = l) :
    HomotopyEquiv (iteratedModuleDouble (selectedIdentifiedComplex R G a ∅) k)
      (iteratedModuleDouble (selectedIdentifiedComplex R G a ∅) l) := by
  subst l
  exact .refl _

/-- Each distinct eliminated O variable contributes one polynomial-linear two-copy factor. -/
noncomputable def iteratedSelectedNormalizationEquiv (hG : G.IsKnot) (a : Fin n)
    (l : List (Fin n)) (hl : l.Nodup) (ha : a ∉ l) :
    HomotopyEquiv (selectedIdentifiedComplex R G a l.toFinset)
      (iteratedModuleDouble (selectedIdentifiedComplex R G a ∅) l.length) := by
  classical
  induction l with
  | nil => exact .refl _
  | cons b l ih =>
    have hab : a ≠ b := fun h => ha (by simp [h])
    have hb : b ∉ l.toFinset := by simpa using (List.nodup_cons.mp hl).1
    exact (selectedComplexCongr R G a
      (show (b :: l).toFinset = insert b l.toFinset from List.toFinset_cons)).trans
      ((selectedNormalizationDoubleEquiv R G hG a b hab l.toFinset hb).trans
        ((moduleDoubleFunctor (Polynomial R)).mapHomotopyEquiv
          (ih (List.nodup_cons.mp hl).2 (fun h => ha (List.mem_cons_of_mem b h)))))

/-- The n−1 variable eliminations give an R[U]-linear native homotopy equivalence. -/
noncomputable def allSelectedNormalizationEquiv (hG : G.IsKnot) (a : Fin n) :
    HomotopyEquiv (selectedIdentifiedComplex R G a (Finset.univ.erase a))
      (iteratedModuleDouble (selectedIdentifiedComplex R G a ∅) (n - 1)) := by
  classical
  have h := iteratedSelectedNormalizationEquiv R G hG a (Finset.univ.erase a).toList
    (Finset.nodup_toList _) (by simp)
  have hlen : (Finset.univ.erase a).toList.length = n - 1 := by
    simp only [Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
  exact (selectedComplexCongr R G a (Finset.toList_toFinset _).symm).trans
    (h.trans (selectedDoubleCountCongr R G a hlen))

/-- The full R[U] rectangle differential as a total native complex. -/
noncomputable def oneVariableTotalComplex (a : Fin n) :
    HomologicalComplex (ModuleCat (Polynomial R)) (ComplexShape.refl Unit) where
  X _ := ModuleCat.of (Polynomial R) (OneVariableChain R n)
  d _ _ := ModuleCat.ofHom (oneVariableDifferential R G)
  shape i j h := by cases i; cases j; exact False.elim (h rfl)
  d_comp_d' _ _ _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact oneVariableDifferential_sq R G a c

/-- Final coefficient representatives are precisely the free R[U] state module. -/
noncomputable def selectedOneVariableEquiv (a : Fin n) :
    selectedIdentifiedModule R a (Finset.univ.erase a) ≃ₗ[Polynomial R] OneVariableChain R n where
  toFun c := collapseOneVariableChain R c.val
  invFun c := ⟨oneVariableChainSection R a c, oneVariableChainSection_mem_identified R a c⟩
  left_inv c := by
    apply Subtype.ext
    change oneVariableChainSection R a (collapseOneVariableChain R c.val) = c.val
    rw [oneVariableChainSection_collapse_erase]
    exact (mem_identifiedChains R a _ _).mp c.property
  right_inv c := collapseOneVariableChain_section R a c
  map_add' c d := map_add _ c.val d.val
  map_smul' p c := collapseOneVariableChain_selected_smul R a p c.val

/-- The fully identified total complex is the actual polynomial rectangle complex. -/
noncomputable def selectedOneVariableIso (a : Fin n) :
    selectedIdentifiedComplex R G a (Finset.univ.erase a) ≅ oneVariableTotalComplex R G a :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (selectedOneVariableEquiv R a).toModuleIso) (by
      intro _ _ _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact (collapseOneVariableChain_identifiedDifferential G R a c.val).symm)

/-- The actual one-U complex has n−1 total two-copy factors over the retained U ring. -/
noncomputable def oneVariablePolynomialNormalizationEquiv (hG : G.IsKnot) (a : Fin n) :
    HomotopyEquiv (oneVariableTotalComplex R G a)
      (iteratedModuleDouble (selectedIdentifiedComplex R G a ∅) (n - 1)) :=
  (HomotopyEquiv.ofIso (selectedOneVariableIso R G a).symm).trans
    (allSelectedNormalizationEquiv R G hG a)

end OnLeConjecture.KnotFloer.GridFull
