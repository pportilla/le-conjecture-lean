/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Prod

/-! # Two-copy functor for total module complexes -/

@[expose] public section

namespace OnLeConjecture.KnotFloer

open CategoryTheory HomologicalComplex

universe u v w

variable (R : Type u) [CommRing R]

/-- Apply a module map separately in the two components. -/
noncomputable def moduleDoubleMap {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    ModuleCat.of R (M × M) ⟶ ModuleCat.of R (N × N) :=
  ModuleCat.ofHom (f.hom.prodMap f.hom)

/-- The additive functor taking a module to two copies of itself. -/
noncomputable def moduleDoubleFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (M × M)
  map := moduleDoubleMap R
  map_id _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance : (moduleDoubleFunctor R).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

variable {R} {ι : Type w} {c : ComplexShape ι}

/-- Iterate the two-copy construction on an existing total complex. -/
noncomputable def iteratedModuleDouble (C : HomologicalComplex (ModuleCat.{v} R) c) :
    ℕ → HomologicalComplex (ModuleCat.{v} R) c
  | 0 => C
  | k + 1 => ((moduleDoubleFunctor R).mapHomologicalComplex c).obj (iteratedModuleDouble C k)

/-- An actual native homotopy equivalence remains one after each two-copy operation. -/
noncomputable def iteratedModuleDoubleEquiv {C D : HomologicalComplex (ModuleCat.{v} R) c}
    (e : HomotopyEquiv C D) : (k : ℕ) →
    HomotopyEquiv (iteratedModuleDouble C k) (iteratedModuleDouble D k)
  | 0 => e
  | k + 1 => (moduleDoubleFunctor R).mapHomotopyEquiv (iteratedModuleDoubleEquiv e k)

end OnLeConjecture.KnotFloer
