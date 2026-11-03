/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPolynomialLatticeRestrictionHomology
public import OnLeConjecture.KnotFloer.GridPolynomialLatticeDoubleHomology
public import OnLeConjecture.KnotFloer.DegreeSuccHomology

/-!
# The polynomial inclusion for a complex and its shifted copy

This inclusion uses the componentwise old grid differential. Its degree m
polynomial homology image decomposes into the original polynomial images
in degree m and the shifted degree m+1. No identification of a transferred
stabilization differential is assumed here.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]
variable (G : GridDiagram n) (a : Fin n)

/-- The coefficient inclusion in both shifted summands. -/
def polynomialDoubleInclusion :
    shiftedDouble (oneVariableMaslovComplex R G a) ⟶ shiftedDouble (laurentMaslovComplex G R) :=
  shiftedDoubleMap (polynomialLatticeInclusion R G a)

/-- Both polynomial summands inject into their Laurent summands. -/
theorem polynomialDoubleInclusion_injective (m : ℤ) :
    Function.Injective ((polynomialDoubleInclusion R G a).f m) := by
  intro x y h
  exact Prod.ext
    (polynomialLatticeInclusion_injective R G a m (congrArg Prod.fst h))
    (polynomialLatticeInclusion_injective R G a (m + 1) (congrArg Prod.snd h))

/-- The doubled polynomial lattice is the product of the two degreewise lattices. -/
theorem mem_range_polynomialDoubleInclusion_iff (m : ℤ)
    (x : (shiftedDouble (laurentMaslovComplex G R)).X m) :
    x ∈ LinearMap.range ((polynomialDoubleInclusion R G a).f m).hom ↔
      x.1 ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom ∧
      x.2 ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f (m + 1)).hom := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    exact ⟨(y, z), Prod.ext hy hz⟩

/-- The Laurent homology classes represented by doubled polynomial cycles. -/
def polynomialDoubleHomologyImage (m : ℤ) :
    Submodule R ((shiftedDouble (laurentMaslovComplex G R)).homology m) :=
  LinearMap.range (homologyMap (polynomialDoubleInclusion R G a) m).hom

/-- The shifted summand's polynomial homology image, before reindexing its degree. -/
def polynomialSuccessorHomologyImage (m : ℤ) :
    Submodule R ((degreeSuccComplex (laurentMaslovComplex G R)).homology m) :=
  LinearMap.range (homologyMap (degreeSuccMap (polynomialLatticeInclusion R G a)) m).hom

/-- The doubled image is exactly the product of the two polynomial images. -/
theorem polynomialDoubleHomologyImage_map_product (m : ℤ) :
    (polynomialDoubleHomologyImage R G a m).map
        (shiftedDoubleHomologyProduct (laurentMaslovComplex G R) m).toLinearMap =
      (polynomialHomologyImage R G a m).prod (polynomialSuccessorHomologyImage R G a m) := by
  ext x
  constructor
  · rintro ⟨ξ, ⟨η, rfl⟩, rfl⟩
    change (shiftedDoubleHomologyProduct (laurentMaslovComplex G R) m
      (homologyMap (shiftedDoubleMap (polynomialLatticeInclusion R G a)) m η)) ∈ _
    rw [shiftedDoubleHomologyProduct_naturality]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨ξ, hξ⟩, ⟨η, hη⟩⟩
    let z := (shiftedDoubleHomologyProduct (oneVariableMaslovComplex R G a) m).symm (ξ, η)
    refine ⟨homologyMap (polynomialDoubleInclusion R G a) m z, ⟨z, rfl⟩, ?_⟩
    change shiftedDoubleHomologyProduct (laurentMaslovComplex G R) m
      (homologyMap (shiftedDoubleMap (polynomialLatticeInclusion R G a)) m z) = x
    rw [shiftedDoubleHomologyProduct_naturality]
    dsimp only [z]
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext hξ hη

/-- Native doubled Laurent homology in degree m is the old homology in degrees m and m+1. -/
def polynomialDoubleHomologyEquiv (m : ℤ) :
    (shiftedDouble (laurentMaslovComplex G R)).homology m ≃ₗ[R]
      (laurentMaslovComplex G R).homology m × (laurentMaslovComplex G R).homology (m + 1) :=
  (shiftedDoubleHomologyProduct (laurentMaslovComplex G R) m).trans
    ((LinearEquiv.refl R _).prodCongr (degreeSuccHomologyEquiv (laurentMaslovComplex G R) m))

/-- Reindexing identifies the successor summand image with the old degree m+1 image. -/
theorem polynomialSuccessorHomologyImage_map (m : ℤ) :
    (polynomialSuccessorHomologyImage R G a m).map
        (degreeSuccHomologyEquiv (laurentMaslovComplex G R) m).toLinearMap =
      polynomialHomologyImage R G a (m + 1) := by
  ext ξ
  constructor
  · rintro ⟨η, ⟨z, rfl⟩, rfl⟩
    have h := degreeSuccHomologyEquiv_naturality (polynomialLatticeInclusion R G a) m z
    change degreeSuccHomologyEquiv (laurentMaslovComplex G R) m
      (homologyMap (degreeSuccMap (polynomialLatticeInclusion R G a)) m z) ∈ _
    rw [h]
    exact ⟨_, rfl⟩
  · rintro ⟨z, hz⟩
    let η := (degreeSuccHomologyEquiv (oneVariableMaslovComplex R G a) m).symm z
    refine ⟨homologyMap (degreeSuccMap (polynomialLatticeInclusion R G a)) m η,
      ⟨η, rfl⟩, ?_⟩
    have h := degreeSuccHomologyEquiv_naturality (polynomialLatticeInclusion R G a) m η
    exact h.trans (by dsimp only [η]; rw [LinearEquiv.apply_symm_apply]; exact hz)

/-- Exact decomposition of the doubled polynomial homology image into degrees m and m+1. -/
theorem polynomialDoubleHomologyImage_map (m : ℤ) :
    (polynomialDoubleHomologyImage R G a m).map
        (polynomialDoubleHomologyEquiv R G m).toLinearMap =
      (polynomialHomologyImage R G a m).prod (polynomialHomologyImage R G a (m + 1)) := by
  ext x
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    have hp := (polynomialDoubleHomologyImage_map_product R G a m).le ⟨ξ, hξ, rfl⟩
    exact ⟨hp.1, (polynomialSuccessorHomologyImage_map R G a m).le ⟨_, hp.2, rfl⟩⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨η, hη, heq⟩ := (polynomialSuccessorHomologyImage_map R G a m).ge hy
    have hprod : (x.1, η) ∈ (polynomialHomologyImage R G a m).prod
        (polynomialSuccessorHomologyImage R G a m) := ⟨hx, hη⟩
    obtain ⟨ξ, hξ, hpair⟩ := (polynomialDoubleHomologyImage_map_product R G a m).ge hprod
    refine ⟨ξ, hξ, ?_⟩
    change (LinearEquiv.refl R _ |>.prodCongr
      (degreeSuccHomologyEquiv (laurentMaslovComplex G R) m))
        (shiftedDoubleHomologyProduct (laurentMaslovComplex G R) m ξ) = x
    change shiftedDoubleHomologyProduct (laurentMaslovComplex G R) m ξ = (x.1, η) at hpair
    rw [hpair]
    exact Prod.ext rfl heq

/-- The doubled polynomial image itself is linearly equivalent to the product of the old images. -/
def polynomialDoubleHomologyImageEquiv (m : ℤ) :
    polynomialDoubleHomologyImage R G a m ≃ₗ[R]
      (polynomialHomologyImage R G a m).prod (polynomialHomologyImage R G a (m + 1)) :=
  (polynomialDoubleHomologyEquiv R G m).ofSubmodules _ _
    (polynomialDoubleHomologyImage_map R G a m)

end OnLeConjecture.KnotFloer.GridFull
