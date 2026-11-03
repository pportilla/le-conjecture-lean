/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.ShiftedDoubleComplex

/-!
# Composition of filtered native chain homotopy equivalences

The data include the two native chain maps and their native inverse homotopies.
All four maps preserve the specified real filtration. Composition and the shifted
double preserve these proved conditions.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer

open CategoryTheory HomologicalComplex

variable {R : Type*} [CommRing R]
variable {C D E : ChainComplex (ModuleCat R) ℤ}

/-- Every component of a native homotopy preserves the given real filtration. -/
def RealFiltration.PreservesHomotopy (F : RealFiltration C) (G : RealFiltration D)
    {f g : C ⟶ D} (h : Homotopy f g) : Prop :=
  ∀ v i j x, x ∈ F.level v i → h.hom i j x ∈ G.level v j

/-- A native chain homotopy equivalence whose maps and inverse homotopies preserve filtration. -/
structure FilteredChainHomotopyEquiv (F : RealFiltration C) (G : RealFiltration D)
    extends HomotopyEquiv C D where
  hom_preserves : F.Preserves G hom
  inv_preserves : G.Preserves F inv
  homotopyHomInvId_preserves : F.PreservesHomotopy F homotopyHomInvId
  homotopyInvHomId_preserves : G.PreservesHomotopy G homotopyInvHomId

namespace FilteredChainHomotopyEquiv

variable {F : RealFiltration C} {G : RealFiltration D} {H : RealFiltration E}

/-- The identity filtered homotopy equivalence. -/
noncomputable def refl (F : RealFiltration C) : FilteredChainHomotopyEquiv F F where
  toHomotopyEquiv := HomotopyEquiv.refl C
  hom_preserves := fun _ _ _ hx => hx
  inv_preserves := fun _ _ _ hx => hx
  homotopyHomInvId_preserves := fun _ _ _ _ _ => Submodule.zero_mem _
  homotopyInvHomId_preserves := fun _ _ _ _ _ => Submodule.zero_mem _

/-- Reverse both maps and the two filtered inverse homotopies. -/
noncomputable def symm (e : FilteredChainHomotopyEquiv F G) :
    FilteredChainHomotopyEquiv G F where
  toHomotopyEquiv := e.toHomotopyEquiv.symm
  hom_preserves := e.inv_preserves
  inv_preserves := e.hom_preserves
  homotopyHomInvId_preserves := e.homotopyInvHomId_preserves
  homotopyInvHomId_preserves := e.homotopyHomInvId_preserves

/-- Compose filtered native homotopy equivalences with their actual composed homotopies. -/
noncomputable def trans (e : FilteredChainHomotopyEquiv F G)
    (f : FilteredChainHomotopyEquiv G H) : FilteredChainHomotopyEquiv F H where
  toHomotopyEquiv := e.toHomotopyEquiv.trans f.toHomotopyEquiv
  hom_preserves := e.hom_preserves.comp f.hom_preserves
  inv_preserves := f.inv_preserves.comp e.inv_preserves
  homotopyHomInvId_preserves := by
    intro v i j x hx
    change e.inv.f j (f.homotopyHomInvId.hom i j (e.hom.f i x)) + 0 +
      e.homotopyHomInvId.hom i j x ∈ F.level v j
    rw [add_zero]
    exact Submodule.add_mem _
      (e.inv_preserves v j _ (f.homotopyHomInvId_preserves v i j _
        (e.hom_preserves v i x hx)))
      (e.homotopyHomInvId_preserves v i j x hx)
  homotopyInvHomId_preserves := by
    intro v i j x hx
    change f.hom.f j (e.homotopyInvHomId.hom i j (f.inv.f i x)) + 0 +
      f.homotopyInvHomId.hom i j x ∈ H.level v j
    rw [add_zero]
    exact Submodule.add_mem _
      (f.hom_preserves v j _ (e.homotopyInvHomId_preserves v i j _
        (f.inv_preserves v i x hx)))
      (f.homotopyInvHomId_preserves v i j x hx)

/-- An isomorphism whose two maps preserve filtration gives a filtered homotopy equivalence. -/
noncomputable def ofIso (e : C ≅ D) (he : F.Preserves G e.hom)
    (he' : G.Preserves F e.inv) : FilteredChainHomotopyEquiv F G where
  toHomotopyEquiv := HomotopyEquiv.ofIso e
  hom_preserves := he
  inv_preserves := he'
  homotopyHomInvId_preserves := fun _ _ _ _ _ => Submodule.zero_mem _
  homotopyInvHomId_preserves := fun _ _ _ _ _ => Submodule.zero_mem _

/-- The two shifted summands retain the filtered maps and both filtered inverse homotopies. -/
noncomputable def shiftedDouble (e : FilteredChainHomotopyEquiv F G) :
    FilteredChainHomotopyEquiv (shiftedDoubleFiltration F) (shiftedDoubleFiltration G) where
  toHomotopyEquiv := shiftedDoubleHomotopyEquiv e.toHomotopyEquiv
  hom_preserves := shiftedDoubleMap_preserves e.hom_preserves
  inv_preserves := shiftedDoubleMap_preserves e.inv_preserves
  homotopyHomInvId_preserves := by
    intro v i j x hx
    exact ⟨e.homotopyHomInvId_preserves v i j x.1 hx.1,
      e.homotopyHomInvId_preserves (v + 1) (i + 1) (j + 1) x.2 hx.2⟩
  homotopyInvHomId_preserves := by
    intro v i j x hx
    exact ⟨e.homotopyInvHomId_preserves v i j x.1 hx.1,
      e.homotopyInvHomId_preserves (v + 1) (i + 1) (j + 1) x.2 hx.2⟩

/-- Iterate the shifted double on the maps and both filtered inverse homotopies. -/
noncomputable def iteratedShiftedDouble (e : FilteredChainHomotopyEquiv F G) :
    (k : ℕ) → FilteredChainHomotopyEquiv
      (iteratedShiftedDoubleFiltration F k) (iteratedShiftedDoubleFiltration G k)
  | 0 => e
  | k + 1 => (iteratedShiftedDouble e k).shiftedDouble

end FilteredChainHomotopyEquiv

end OnLeConjecture.KnotFloer
