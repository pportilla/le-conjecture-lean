/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.SpectralThreshold
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# A complex and its shifted copy

The degree m module is `C_m × C_(m+1)`, with the two component differentials.
The Alexander bound v on the second component is v+1. Over characteristic two
this is tensoring with the zero-differential two-dimensional factor W in
bidegrees `(0,0)` and `(-1,-1)`. The component construction is compatible with
Mathlib's degree reindexing along `embeddingDown'Add 1 1`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer

open CategoryTheory HomologicalComplex

variable {R : Type*} [CommRing R]

/-- A complex and its degree-minus-one copy, with componentwise differential. -/
noncomputable def shiftedDouble (C : ChainComplex (ModuleCat R) ℤ) :
    ChainComplex (ModuleCat R) ℤ where
  X i := ModuleCat.of R (C.X i × C.X (i + 1))
  d i j := ModuleCat.ofHom ((C.d i j).hom.prodMap (C.d (i + 1) (j + 1)).hom)
  shape i j hij := by
    have h : ¬ (ComplexShape.down ℤ).Rel (i + 1) (j + 1) := by
      simpa only [ComplexShape.down_Rel, add_right_cancel_iff] using hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext
      (congrArg (fun f : C.X i ⟶ C.X j => f x.1) (C.shape i j hij))
      (congrArg (fun f : C.X (i + 1) ⟶ C.X (j + 1) => f x.2)
        (C.shape (i + 1) (j + 1) h))
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext
      (congrArg (fun f : C.X i ⟶ C.X k => f x.1) (C.d_comp_d i j k))
      (congrArg (fun f : C.X (i + 1) ⟶ C.X (k + 1) => f x.2)
        (C.d_comp_d (i + 1) (j + 1) (k + 1)))

theorem shiftedDouble_d (C : ChainComplex (ModuleCat R) ℤ) (i j : ℤ) :
    (shiftedDouble C).d i j =
      ModuleCat.ofHom ((C.d i j).hom.prodMap (C.d (i + 1) (j + 1)).hom) := rfl

/-- Apply a native chain map in both components of the shifted double. -/
noncomputable def shiftedDoubleMap {C D : ChainComplex (ModuleCat R) ℤ} (f : C ⟶ D) :
    shiftedDouble C ⟶ shiftedDouble D where
  f i := ModuleCat.ofHom ((f.f i).hom.prodMap (f.f (i + 1)).hom)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext
      (congrArg (fun g : C.X i ⟶ D.X j => g x.1) (f.comm i j))
      (congrArg (fun g : C.X (i + 1) ⟶ D.X (j + 1) => g x.2)
        (f.comm (i + 1) (j + 1)))

@[simp]
theorem shiftedDoubleMap_id (C : ChainComplex (ModuleCat R) ℤ) :
    shiftedDoubleMap (𝟙 C) = 𝟙 (shiftedDouble C) := by
  ext i : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

@[simp]
theorem shiftedDoubleMap_comp {C D E : ChainComplex (ModuleCat R) ℤ}
    (f : C ⟶ D) (g : D ⟶ E) :
    shiftedDoubleMap (f ≫ g) = shiftedDoubleMap f ≫ shiftedDoubleMap g := by
  ext i : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The two component maps of a homotopy on the shifted double. -/
noncomputable def shiftedDoubleHomotopyComponent {C D : ChainComplex (ModuleCat R) ℤ}
    {f g : C ⟶ D} (h : Homotopy f g) (i j : ℤ) :
    (shiftedDouble C).X i ⟶ (shiftedDouble D).X j :=
  ModuleCat.ofHom ((h.hom i j).hom.prodMap (h.hom (i + 1) (j + 1)).hom)

/-- Apply a native homotopy in both components, retaining its degree-one convention. -/
noncomputable def shiftedDoubleHomotopy {C D : ChainComplex (ModuleCat R) ℤ}
    {f g : C ⟶ D} (h : Homotopy f g) :
    Homotopy (shiftedDoubleMap f) (shiftedDoubleMap g) where
  hom := shiftedDoubleHomotopyComponent h
  zero i j hij := by
    have h' : ¬ (ComplexShape.down ℤ).Rel (j + 1) (i + 1) := by
      simpa only [ComplexShape.down_Rel, add_right_cancel_iff] using hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext
      (congrArg (fun f : C.X i ⟶ D.X j => f x.1) (h.zero i j hij))
      (congrArg (fun f : C.X (i + 1) ⟶ D.X (j + 1) => f x.2)
        (h.zero (i + 1) (j + 1) h'))
  comm i := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = i := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (m + 1 + 1) (m + 1) from rfl)]
    have h₁ := h.comm (m + 1)
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (m + 1 + 1) (m + 1) from rfl)] at h₁
    have h₂ := h.comm (m + 1 + 1)
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1 + 1) (m + 1) from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (m + 1 + 1 + 1) (m + 1 + 1) from rfl)] at h₂
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext
      (congrArg (fun k : C.X (m + 1) ⟶ D.X (m + 1) => k x.1) h₁)
      (congrArg (fun k : C.X (m + 1 + 1) ⟶ D.X (m + 1 + 1) => k x.2) h₂)

/-- A homotopy equivalence induces one on the shifted doubles. -/
noncomputable def shiftedDoubleHomotopyEquiv {C D : ChainComplex (ModuleCat R) ℤ}
    (e : HomotopyEquiv C D) : HomotopyEquiv (shiftedDouble C) (shiftedDouble D) where
  hom := shiftedDoubleMap e.hom
  inv := shiftedDoubleMap e.inv
  homotopyHomInvId := by simpa only [shiftedDoubleMap_comp, shiftedDoubleMap_id] using
    shiftedDoubleHomotopy e.homotopyHomInvId
  homotopyInvHomId := by simpa only [shiftedDoubleMap_comp, shiftedDoubleMap_id] using
    shiftedDoubleHomotopy e.homotopyInvHomId

/-- Give the second summand its Alexander-minus-one shift. -/
noncomputable def shiftedDoubleFiltration {C : ChainComplex (ModuleCat R) ℤ}
    (F : RealFiltration C) : RealFiltration (shiftedDouble C) where
  level v i := (F.level v i).prod (F.level (v + 1) (i + 1))
  mono i v v' hv := by
    intro c hc
    exact ⟨F.mono i hv hc.1, F.mono (i + 1) (by linarith) hc.2⟩
  differential_mem v i j c hc :=
    ⟨F.differential_mem v i j c.1 hc.1,
      F.differential_mem (v + 1) (i + 1) (j + 1) c.2 hc.2⟩

/-- Alexander-preserving maps remain so on the two shifted summands. -/
theorem shiftedDoubleMap_preserves {C D : ChainComplex (ModuleCat R) ℤ}
    {F : RealFiltration C} {G : RealFiltration D} {f : C ⟶ D}
    (hf : F.Preserves G f) :
    (shiftedDoubleFiltration F).Preserves (shiftedDoubleFiltration G) (shiftedDoubleMap f) := by
  intro v i c hc
  exact ⟨hf v i c.1 hc.1, hf (v + 1) (i + 1) c.2 hc.2⟩

/-- Iterate the zero-differential W factor through its explicit two shifted summands. -/
noncomputable def iteratedShiftedDouble (C : ChainComplex (ModuleCat R) ℤ) :
    ℕ → ChainComplex (ModuleCat R) ℤ
  | 0 => C
  | k + 1 => shiftedDouble (iteratedShiftedDouble C k)

/-- The iterated Alexander filtration uses the same degree and filtration shifts at every step. -/
noncomputable def iteratedShiftedDoubleFiltration {C : ChainComplex (ModuleCat R) ℤ}
    (F : RealFiltration C) : (k : ℕ) → RealFiltration (iteratedShiftedDouble C k)
  | 0 => F
  | k + 1 => shiftedDoubleFiltration (iteratedShiftedDoubleFiltration F k)

end OnLeConjecture.KnotFloer
