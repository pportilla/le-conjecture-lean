/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPolynomialLatticeCycles

/-!
# Restricting Laurent chain maps to the polynomial lattice

A degreewise Laurent map preserving the polynomial images has a unique native
polynomial restriction. A bifiltered map with first-coordinate shift zero
satisfies this preservation property for any second-coordinate shift.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n k : ℕ} (R : Type*) [CommRing R] [CharP R 2]
variable (G : GridDiagram n) (H : GridDiagram k) (a : Fin n) (b : Fin k)

/-- Polynomial chains are exactly those in some bifiltration level with first coordinate zero. -/
theorem mem_polynomialLattice_iff_exists_zero_level (m : ℤ)
    (x : (laurentMaslovComplex G R).X m) :
    x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom ↔
      ∃ B : ℝ, x ∈ (laurentMaslovBifiltration G R).level 0 B m := by
  rw [mem_range_polynomialLatticeInclusion_iff]
  constructor
  · intro hx
    refine ⟨maslovCoordinateBound G m, ?_⟩
    intro y j hj
    exact ⟨neg_nonpos.mpr (by exact_mod_cast hx y j hj),
      (laurentMaslovBifiltration_bound G R m x y j hj).2⟩
  · rintro ⟨B, hB⟩ y j hj
    exact_mod_cast neg_nonpos.mp (hB y j hj).1

/-- A linear map between native Laurent degrees restricts along the injective
polynomial inclusions. -/
def polynomialLatticeRestrictLinear (i j : ℤ)
    (f : (laurentMaslovComplex G R).X i →ₗ[R] (laurentMaslovComplex H R).X j)
    (hf : ∀ x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f i).hom,
      f x ∈ LinearMap.range ((polynomialLatticeInclusion R H b).f j).hom) :
    (oneVariableMaslovComplex R G a).X i →ₗ[R] (oneVariableMaslovComplex R H b).X j :=
  (f.comp ((polynomialLatticeInclusion R G a).f i).hom).codRestrictOfInjective
    ((polynomialLatticeInclusion R H b).f j).hom
    (polynomialLatticeInclusion_injective R H b j) (fun x => hf _ ⟨x, rfl⟩)

/-- The restriction has exactly the required underlying Laurent map. -/
theorem polynomialLatticeRestrictLinear_apply (i j : ℤ)
    (f : (laurentMaslovComplex G R).X i →ₗ[R] (laurentMaslovComplex H R).X j)
    (hf : ∀ x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f i).hom,
      f x ∈ LinearMap.range ((polynomialLatticeInclusion R H b).f j).hom)
    (x : (oneVariableMaslovComplex R G a).X i) :
    (polynomialLatticeInclusion R H b).f j (polynomialLatticeRestrictLinear R G H a b i j f hf x) =
      f ((polynomialLatticeInclusion R G a).f i x) :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x

/-- Inclusion commutes with the differential on actual native polynomial chains. -/
theorem polynomialLatticeInclusion_d (i j : ℤ)
    (x : (oneVariableMaslovComplex R G a).X i) :
    (polynomialLatticeInclusion R G a).f j
      ((oneVariableMaslovComplex R G a).d i j x) =
        (laurentMaslovComplex G R).d i j ((polynomialLatticeInclusion R G a).f i x) :=
  (congrArg (fun f : (oneVariableMaslovComplex R G a).X i ⟶
    (laurentMaslovComplex G R).X j => f x) ((polynomialLatticeInclusion R G a).comm i j)).symm

/-- A Laurent chain map preserving the polynomial images restricts to a polynomial chain map. -/
def polynomialLatticeRestrictMap
    (φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R)
    (hφ : ∀ m x, x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom →
      φ.f m x ∈ LinearMap.range ((polynomialLatticeInclusion R H b).f m).hom) :
    oneVariableMaslovComplex R G a ⟶ oneVariableMaslovComplex R H b where
  f m := ModuleCat.ofHom (polynomialLatticeRestrictLinear R G H a b m m (φ.f m).hom (hφ m))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply polynomialLatticeInclusion_injective R H b j
    change (polynomialLatticeInclusion R H b).f j
      ((oneVariableMaslovComplex R H b).d i j
        (polynomialLatticeRestrictLinear R G H a b i i (φ.f i).hom (hφ i) x)) =
      (polynomialLatticeInclusion R H b).f j
        (polynomialLatticeRestrictLinear R G H a b j j (φ.f j).hom (hφ j)
          ((oneVariableMaslovComplex R G a).d i j x))
    rw [polynomialLatticeInclusion_d, polynomialLatticeRestrictLinear_apply,
      polynomialLatticeRestrictLinear_apply, polynomialLatticeInclusion_d]
    exact congrArg (fun f : (laurentMaslovComplex G R).X i ⟶
      (laurentMaslovComplex H R).X j => f ((polynomialLatticeInclusion R G a).f i x)) (φ.comm i j)

/-- The restriction commutes with the coefficient inclusions. -/
theorem polynomialLatticeRestrictMap_comm
    (φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R)
    (hφ : ∀ m x, x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom →
      φ.f m x ∈ LinearMap.range ((polynomialLatticeInclusion R H b).f m).hom) :
    polynomialLatticeRestrictMap R G H a b φ hφ ≫ polynomialLatticeInclusion R H b =
      polynomialLatticeInclusion R G a ≫ φ := by
  apply HomologicalComplex.Hom.ext
  funext m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact polynomialLatticeRestrictLinear_apply R G H a b m m (φ.f m).hom (hφ m)

/-- No other polynomial chain map can have the same included Laurent map. -/
theorem polynomialLatticeRestrictMap_unique
    (φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R)
    (hφ : ∀ m x, x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom →
      φ.f m x ∈ LinearMap.range ((polynomialLatticeInclusion R H b).f m).hom)
    (ψ : oneVariableMaslovComplex R G a ⟶ oneVariableMaslovComplex R H b)
    (hψ : ψ ≫ polynomialLatticeInclusion R H b = polynomialLatticeInclusion R G a ≫ φ) :
    ψ = polynomialLatticeRestrictMap R G H a b φ hφ := by
  apply HomologicalComplex.Hom.ext
  funext m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply polynomialLatticeInclusion_injective R H b m
  have h := congrArg (fun f : oneVariableMaslovComplex R G a ⟶
    laurentMaslovComplex H R => f.f m x)
      (hψ.trans (polynomialLatticeRestrictMap_comm R G H a b φ hφ).symm)
  exact h

/-- A zero first-coordinate shift preserves the polynomial chain image. -/
theorem polynomialLattice_preserved_of_shifts
    (φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R) (s : ℝ)
    (hφ : (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R) φ 0 s)
    (m : ℤ) (x : (laurentMaslovComplex G R).X m)
    (hx : x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom) :
    φ.f m x ∈ LinearMap.range ((polynomialLatticeInclusion R H b).f m).hom := by
  obtain ⟨B, hB⟩ := (mem_polynomialLattice_iff_exists_zero_level R G a m x).mp hx
  apply (mem_polynomialLattice_iff_exists_zero_level R H b m _).mpr
  exact ⟨B + s, by simpa only [zero_add] using hφ 0 B m x hB⟩

/-- The native polynomial restriction of a zero-first-shift Laurent map. -/
def polynomialLatticeRestrictMapOfShifts
    (φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R) (s : ℝ)
    (hφ : (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R) φ 0 s) :
    oneVariableMaslovComplex R G a ⟶ oneVariableMaslovComplex R H b :=
  polynomialLatticeRestrictMap R G H a b φ (polynomialLattice_preserved_of_shifts R G H a b φ s hφ)

end OnLeConjecture.KnotFloer.GridFull
