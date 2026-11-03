/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridVariableUAction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The total identified grid complexes over the retained polynomial variable

The scalar U acts by the selected O variable. The coefficient projections,
divided inclusion, and geometric shear are polynomial-linear maps on these
total modules. Their homogeneous components are the graded normalization maps.
The total complexes are useful for scalar extension, since U has Maslov degree
minus two and is not an endomorphism of one homogeneous component.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (R : Type*) [CommRing R]

/-- Restrict the full coefficient action to polynomials in the selected O variable. -/
noncomputable def selectedVariableModule (a : Fin n) : ModuleCat (Polynomial R) :=
  (ModuleCat.restrictScalars (oneVariableSection R a).toRingHom).obj
    (ModuleCat.of (MvPolynomial (Fin n) R) (GridChainMinus R n))

/-- The already identified chains form a module over the retained polynomial variable. -/
noncomputable def selectedIdentifiedSubmodule (a : Fin n) (s : Finset (Fin n)) :
    Submodule (Polynomial R) (selectedVariableModule R a) where
  carrier := {c | (show GridChainMinus R n from c) ∈ identifiedChains R a s}
  zero_mem' := (identifiedChains R a s).zero_mem
  add_mem' := (identifiedChains R a s).add_mem
  smul_mem' p c hc := by
    change oneVariableSection R a p • (show GridChainMinus R n from c) ∈ identifiedChains R a s
    exact (mem_identifiedChains R a s _).mpr
      ((identifyVariablesChain_selected_smul R a s p (show GridChainMinus R n from c)).trans
        (congrArg (fun c => oneVariableSection R a p • c)
          ((mem_identifiedChains R a s (show GridChainMinus R n from c)).mp hc)))

/-- The coefficient-identified module, with its genuine R[U] action. -/
noncomputable def selectedIdentifiedModule (a : Fin n) (s : Finset (Fin n)) :
    ModuleCat (Polynomial R) :=
  ModuleCat.of (Polynomial R) (selectedIdentifiedSubmodule R a s)

/-- The rectangle differential is linear over the selected polynomial variable. -/
noncomputable def selectedIdentifiedDifferential (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) : selectedIdentifiedModule R a s ⟶ selectedIdentifiedModule R a s :=
  ModuleCat.ofHom {
    toFun c := ⟨identifiedDifferential R G a s (show GridChainMinus R n from c.val),
      identifiedDifferential_mem_identifiedChains R G a s (show GridChainMinus R n from c.val)⟩
    map_add' c d := Subtype.ext (map_add _ c.val d.val)
    map_smul' p c := Subtype.ext (identifiedDifferential_selected_smul R G a s p
      (show GridChainMinus R n from c.val)) }

variable [CharP R 2]

/-- The total identified complex, retaining its polynomial U action. -/
noncomputable def selectedIdentifiedComplex (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) :
    HomologicalComplex (ModuleCat (Polynomial R)) (ComplexShape.refl Unit) where
  X _ := selectedIdentifiedModule R a s
  d _ _ := selectedIdentifiedDifferential R G a s
  shape i j h := by cases i; cases j; exact False.elim (h rfl)
  d_comp_d' _ _ _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact Subtype.ext (identifiedDifferential_sq R G a s (show GridChainMinus R n from c.val))

/-- A polynomial-linear map on total grid chains restricts to the identified modules. -/
noncomputable def selectedMapOfLinear (a : Fin n) (s t : Finset (Fin n))
    (f : GridChainMinus R n →ₗ[R] GridChainMinus R n)
    (hf : ∀ p c, f (oneVariableSection R a p • c) = oneVariableSection R a p • f c)
    (hm : ∀ c, c ∈ identifiedChains R a s → f c ∈ identifiedChains R a t) :
    selectedIdentifiedModule R a s ⟶ selectedIdentifiedModule R a t :=
  ModuleCat.ofHom {
    toFun c := ⟨f (show GridChainMinus R n from c.val),
      hm (show GridChainMinus R n from c.val) c.property⟩
    map_add' c d := Subtype.ext (map_add _ c.val d.val)
    map_smul' p c := Subtype.ext (hf p (show GridChainMinus R n from c.val)) }

end OnLeConjecture.KnotFloer.GridFull
