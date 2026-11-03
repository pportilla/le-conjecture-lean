/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Restriction and homology images for injective coefficient inclusions

The native transferred stabilization complex is not yet identified with an old
grid complex. These statements apply directly to its polynomial inclusion,
as well as to the ordinary grid inclusion. They require only chain maps,
degreewise injectivity, and preservation of their ranges.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.PolynomialLattice

open CategoryTheory HomologicalComplex

variable {R : Type*} [CommRing R]
variable {P C Q D : ChainComplex (ModuleCat R) ℤ}

/-- A native map preserves the ranges of the specified coefficient inclusions. -/
def Preserves (i : P ⟶ C) (j : Q ⟶ D) (φ : C ⟶ D) : Prop :=
  ∀ m x, x ∈ LinearMap.range (i.f m).hom → φ.f m x ∈ LinearMap.range (j.f m).hom

/-- Homology classes represented in the included complex. -/
def homologyImage (i : P ⟶ C) (m : ℤ) : Submodule R (C.homology m) :=
  LinearMap.range (homologyMap i m).hom

/-- Restrict a degreewise map along a target inclusion with unique preimages. -/
def restrictLinear (i : P ⟶ C) (j : Q ⟶ D)
    (hj : ∀ m, Function.Injective (j.f m))
    (φ : C ⟶ D) (hφ : Preserves i j φ) (m : ℤ) : P.X m →ₗ[R] Q.X m :=
  ((φ.f m).hom.comp (i.f m).hom).codRestrictOfInjective
    (j.f m).hom (hj m) (fun x => hφ m _ ⟨x, rfl⟩)

/-- The restricted map has the prescribed included value. -/
theorem restrictLinear_apply (i : P ⟶ C) (j : Q ⟶ D)
    (hj : ∀ m, Function.Injective (j.f m))
    (φ : C ⟶ D) (hφ : Preserves i j φ) (m : ℤ) (x : P.X m) :
    j.f m (restrictLinear i j hj φ hφ m x) = φ.f m (i.f m x) :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x

/-- Coefficient inclusion commutes with the native differential. -/
theorem inclusion_d (i : P ⟶ C) (m k : ℤ) (x : P.X m) :
    i.f k (P.d m k x) = C.d m k (i.f m x) :=
  (congrArg (fun f : P.X m ⟶ C.X k => f x) (i.comm m k)).symm

/-- The unique polynomial restriction is a chain map. -/
def restrictMap (i : P ⟶ C) (j : Q ⟶ D)
    (hj : ∀ m, Function.Injective (j.f m))
    (φ : C ⟶ D) (hφ : Preserves i j φ) : P ⟶ Q where
  f m := ModuleCat.ofHom (restrictLinear i j hj φ hφ m)
  comm' m k _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply hj k
    change j.f k (Q.d m k (restrictLinear i j hj φ hφ m x)) =
      j.f k (restrictLinear i j hj φ hφ k (P.d m k x))
    rw [inclusion_d, restrictLinear_apply, restrictLinear_apply, inclusion_d]
    exact congrArg (fun f : C.X m ⟶ D.X k => f (i.f m x)) (φ.comm m k)

/-- The coefficient-inclusion square commutes on the constructed chain maps. -/
theorem restrictMap_comm (i : P ⟶ C) (j : Q ⟶ D)
    (hj : ∀ m, Function.Injective (j.f m))
    (φ : C ⟶ D) (hφ : Preserves i j φ) :
    restrictMap i j hj φ hφ ≫ j = i ≫ φ := by
  apply HomologicalComplex.Hom.ext
  funext m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact restrictLinear_apply i j hj φ hφ m

/-- Degreewise injectivity makes the chain-map restriction unique. -/
theorem restrictMap_unique (i : P ⟶ C) (j : Q ⟶ D)
    (hj : ∀ m, Function.Injective (j.f m))
    (φ : C ⟶ D) (hφ : Preserves i j φ)
    (ψ : P ⟶ Q) (hψ : ψ ≫ j = i ≫ φ) : ψ = restrictMap i j hj φ hφ := by
  apply HomologicalComplex.Hom.ext
  funext m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply hj m
  exact congrArg (fun f : P ⟶ D => f.f m x)
    (hψ.trans (restrictMap_comm i j hj φ hφ).symm)

/-- The same inclusion square commutes on homology. -/
theorem restrictMap_homology_comm (i : P ⟶ C) (j : Q ⟶ D)
    (hj : ∀ m, Function.Injective (j.f m))
    (φ : C ⟶ D) (hφ : Preserves i j φ) (m : ℤ) :
    homologyMap (restrictMap i j hj φ hφ) m ≫ homologyMap j m =
      homologyMap i m ≫ homologyMap φ m := by
  rw [← homologyMap_comp, ← homologyMap_comp, restrictMap_comm]

/-- A range-preserving map carries the included homology image into its target image. -/
theorem homologyImage_map_le (i : P ⟶ C) (j : Q ⟶ D)
    (hj : ∀ m, Function.Injective (j.f m))
    (φ : C ⟶ D) (hφ : Preserves i j φ) (m : ℤ) :
    (homologyImage i m).map (homologyMap φ m).hom ≤ homologyImage j m := by
  unfold homologyImage
  rw [← LinearMap.range_comp]
  have hc := congrArg (fun f => f.hom) (restrictMap_homology_comm i j hj φ hφ m)
  change (homologyMap j m).hom.comp (homologyMap (restrictMap i j hj φ hφ) m).hom =
    (homologyMap φ m).hom.comp (homologyMap i m).hom at hc
  rw [← hc]
  exact LinearMap.range_comp_le_range _ _

/-- A homotopy equivalence preserving both ranges transports their homology images exactly. -/
theorem homologyImage_map_eq (i : P ⟶ C) (j : Q ⟶ D)
    (hi : ∀ m, Function.Injective (i.f m)) (hj : ∀ m, Function.Injective (j.f m))
    (e : HomotopyEquiv C D) (he : Preserves i j e.hom) (hei : Preserves j i e.inv)
    (m : ℤ) :
    (homologyImage i m).map (homologyMap e.hom m).hom = homologyImage j m := by
  apply le_antisymm (homologyImage_map_le i j hj e.hom he m)
  intro ξ hξ
  refine ⟨homologyMap e.inv m ξ, ?_, ?_⟩
  · exact homologyImage_map_le j i hi e.inv hei m ⟨ξ, hξ, rfl⟩
  · exact congrArg (fun f : D.homology m ⟶ D.homology m => f ξ)
      (e.toHomologyIso m).inv_hom_id

/-- The actual Laurent homology isomorphism restricts to the included homology images. -/
def homologyImageEquiv (i : P ⟶ C) (j : Q ⟶ D)
    (hi : ∀ m, Function.Injective (i.f m)) (hj : ∀ m, Function.Injective (j.f m))
    (e : HomotopyEquiv C D) (he : Preserves i j e.hom) (hei : Preserves j i e.inv)
    (m : ℤ) : homologyImage i m ≃ₗ[R] homologyImage j m :=
  (e.toHomologyIso m).toLinearEquiv.ofSubmodules _ _ (homologyImage_map_eq i j hi hj e he hei m)

/-- The restricted image equivalence is given by the original native homology map. -/
theorem homologyImageEquiv_apply (i : P ⟶ C) (j : Q ⟶ D)
    (hi : ∀ m, Function.Injective (i.f m)) (hj : ∀ m, Function.Injective (j.f m))
    (e : HomotopyEquiv C D) (he : Preserves i j e.hom) (hei : Preserves j i e.inv)
    (m : ℤ) (ξ : homologyImage i m) :
    (homologyImageEquiv i j hi hj e he hei m ξ : D.homology m) = homologyMap e.hom m ξ := rfl

end OnLeConjecture.KnotFloer.PolynomialLattice
