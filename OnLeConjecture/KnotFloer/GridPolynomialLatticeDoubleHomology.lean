/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.ShiftedDoubleComplex
public import OnLeConjecture.KnotFloer.DegreeSuccComplex

/-!
# Homology of the shifted two-copy complex

The degree m homology is the product of the original homology in degrees m
and m+1. The decomposition is natural for the existing two-copy chain map.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer

open CategoryTheory HomologicalComplex

variable {R : Type*} [CommRing R]

/-- First projection of the shifted double. -/
def shiftedDoubleFst (C : ChainComplex (ModuleCat R) ℤ) : shiftedDouble C ⟶ C where
  f _ := ModuleCat.ofHom (LinearMap.fst R _ _)
  comm' _ _ _ := rfl

/-- Second projection, with its precise degree shift. -/
def shiftedDoubleSnd (C : ChainComplex (ModuleCat R) ℤ) :
    shiftedDouble C ⟶ degreeSuccComplex C where
  f _ := ModuleCat.ofHom (LinearMap.snd R _ _)
  comm' _ _ _ := rfl

/-- Include the first copy. -/
def shiftedDoubleInl (C : ChainComplex (ModuleCat R) ℤ) : C ⟶ shiftedDouble C where
  f _ := ModuleCat.ofHom (LinearMap.inl R _ _)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (C.d i j x, C.d (i + 1) (j + 1) 0) = (C.d i j x, 0)
    rw [map_zero]

/-- Include the degree-minus-one copy. -/
def shiftedDoubleInr (C : ChainComplex (ModuleCat R) ℤ) :
    degreeSuccComplex C ⟶ shiftedDouble C where
  f _ := ModuleCat.ofHom (LinearMap.inr R _ _)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (C.d i j 0, C.d (i + 1) (j + 1) x) = (0, C.d (i + 1) (j + 1) x)
    rw [map_zero]

@[simp] theorem shiftedDoubleInl_fst (C : ChainComplex (ModuleCat R) ℤ) :
    shiftedDoubleInl C ≫ shiftedDoubleFst C = 𝟙 C := by ext m x; rfl

@[simp] theorem shiftedDoubleInl_snd (C : ChainComplex (ModuleCat R) ℤ) :
    shiftedDoubleInl C ≫ shiftedDoubleSnd C = 0 := by ext m x; rfl

@[simp] theorem shiftedDoubleInr_fst (C : ChainComplex (ModuleCat R) ℤ) :
    shiftedDoubleInr C ≫ shiftedDoubleFst C = 0 := by ext m x; rfl

@[simp] theorem shiftedDoubleInr_snd (C : ChainComplex (ModuleCat R) ℤ) :
    shiftedDoubleInr C ≫ shiftedDoubleSnd C = 𝟙 (degreeSuccComplex C) := by ext m x; rfl

@[simp] theorem shiftedDouble_total (C : ChainComplex (ModuleCat R) ℤ) :
    shiftedDoubleFst C ≫ shiftedDoubleInl C + shiftedDoubleSnd C ≫ shiftedDoubleInr C =
      𝟙 (shiftedDouble C) := by
  ext m x
  change (x.1, 0) + (0, x.2) = x
  exact Prod.ext (add_zero _) (zero_add _)

/-- Native homology decomposes according to the two degree-shifted summands. -/
def shiftedDoubleHomologyProduct (C : ChainComplex (ModuleCat R) ℤ) (m : ℤ) :
    (shiftedDouble C).homology m ≃ₗ[R] C.homology m × (degreeSuccComplex C).homology m where
  toFun ξ := (homologyMap (shiftedDoubleFst C) m ξ, homologyMap (shiftedDoubleSnd C) m ξ)
  invFun ξ := homologyMap (shiftedDoubleInl C) m ξ.1 + homologyMap (shiftedDoubleInr C) m ξ.2
  left_inv ξ := by
    have h : homologyMap (shiftedDoubleFst C) m ≫ homologyMap (shiftedDoubleInl C) m +
        homologyMap (shiftedDoubleSnd C) m ≫ homologyMap (shiftedDoubleInr C) m = 𝟙 _ := by
      rw [← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add,
        shiftedDouble_total, homologyMap_id]
    exact congrArg (fun f : (shiftedDouble C).homology m ⟶
      (shiftedDouble C).homology m => f ξ) h
  right_inv ξ := by
    have h₁ : homologyMap (shiftedDoubleInl C) m ≫ homologyMap (shiftedDoubleFst C) m = 𝟙 _ := by
      rw [← homologyMap_comp, shiftedDoubleInl_fst, homologyMap_id]
    have h₂ : homologyMap (shiftedDoubleInr C) m ≫ homologyMap (shiftedDoubleFst C) m = 0 := by
      rw [← homologyMap_comp, shiftedDoubleInr_fst, homologyMap_zero]
    have h₃ : homologyMap (shiftedDoubleInl C) m ≫ homologyMap (shiftedDoubleSnd C) m = 0 := by
      rw [← homologyMap_comp, shiftedDoubleInl_snd, homologyMap_zero]
    have h₄ : homologyMap (shiftedDoubleInr C) m ≫ homologyMap (shiftedDoubleSnd C) m = 𝟙 _ := by
      rw [← homologyMap_comp, shiftedDoubleInr_snd, homologyMap_id]
    apply Prod.ext
    · simp only [map_add]
      rw [show homologyMap (shiftedDoubleFst C) m
        (homologyMap (shiftedDoubleInr C) m ξ.2) = 0 from
          congrArg (fun f : (degreeSuccComplex C).homology m ⟶ C.homology m => f ξ.2) h₂,
        add_zero]
      exact congrArg (fun f : C.homology m ⟶ C.homology m => f ξ.1) h₁
    · simp only [map_add]
      rw [show homologyMap (shiftedDoubleSnd C) m
        (homologyMap (shiftedDoubleInl C) m ξ.1) = 0 from
          congrArg (fun f : C.homology m ⟶ (degreeSuccComplex C).homology m => f ξ.1) h₃,
        zero_add]
      exact congrArg (fun f : (degreeSuccComplex C).homology m ⟶
        (degreeSuccComplex C).homology m => f ξ.2) h₄
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The two-copy homology decomposition intertwines the given chain map in each component. -/
theorem shiftedDoubleHomologyProduct_naturality {C D : ChainComplex (ModuleCat R) ℤ}
    (φ : C ⟶ D) (m : ℤ) (ξ : (shiftedDouble C).homology m) :
    shiftedDoubleHomologyProduct D m (homologyMap (shiftedDoubleMap φ) m ξ) =
      ((homologyMap φ m) (shiftedDoubleHomologyProduct C m ξ).1,
        homologyMap (degreeSuccMap φ) m (shiftedDoubleHomologyProduct C m ξ).2) := by
  have hf : shiftedDoubleMap φ ≫ shiftedDoubleFst D = shiftedDoubleFst C ≫ φ := by
    ext i x; rfl
  have hs : shiftedDoubleMap φ ≫ shiftedDoubleSnd D =
      shiftedDoubleSnd C ≫ degreeSuccMap φ := by ext i x; rfl
  have hf' : homologyMap (shiftedDoubleMap φ) m ≫ homologyMap (shiftedDoubleFst D) m =
      homologyMap (shiftedDoubleFst C) m ≫ homologyMap φ m := by
    rw [← homologyMap_comp, ← homologyMap_comp, hf]
  have hs' : homologyMap (shiftedDoubleMap φ) m ≫ homologyMap (shiftedDoubleSnd D) m =
      homologyMap (shiftedDoubleSnd C) m ≫ homologyMap (degreeSuccMap φ) m := by
    rw [← homologyMap_comp, ← homologyMap_comp, hs]
  exact Prod.ext
    (congrArg (fun f : (shiftedDouble C).homology m ⟶ D.homology m => f ξ) hf')
    (congrArg (fun f : (shiftedDouble C).homology m ⟶
      (degreeSuccComplex D).homology m => f ξ) hs')

end OnLeConjecture.KnotFloer
