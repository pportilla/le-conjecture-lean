/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusFirstClass
public import OnLeConjecture.KnotFloer.GridPolynomialLatticeCycles

/-!
# The explicit torus corner class belongs to the polynomial image

Its defining native cycle is the corner state with constant coefficient one.
Consequently its homology class lies in the polynomial homology image,
independently of the selected O variable. Nonvanishing and uniqueness of that
image class remain separate normalization obligations.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable (n : ℕ) (R : Type*) [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- Constant corner coefficients belong to the polynomial coefficient lattice. -/
theorem reflectedTorusAnchorChain_mem_polynomialLattice :
    (Finsupp.single (reflectedTorusAnchor n) 1 : LaurentChain R (consecutiveTorusGridSize n)) ∈
      LinearMap.range (oneVariableToLaurentChain R) := by
  refine ⟨Finsupp.single (reflectedTorusAnchor n) 1, ?_⟩
  ext x
  simp [oneVariableToLaurentChain_apply, Finsupp.single_apply]

/-- The corner class has a polynomial native cycle representative. -/
theorem reflectedTorusAnchorClass_mem_polynomialHomologyImage
    (a : Fin (consecutiveTorusGridSize n)) :
    reflectedTorusAnchorClass n R ∈ polynomialHomologyImage R (reflectedTorusGrid n) a 0 := by
  apply (mem_polynomialHomologyImage_iff_exists_cycle R (reflectedTorusGrid n) a 0 _).mpr
  refine ⟨reflectedTorusAnchorCycle n R, ?_, rfl⟩
  have h := (mem_range_oneVariableToLaurentChain_iff R _).mp
    (reflectedTorusAnchorChain_mem_polynomialLattice n R)
  simpa only [reflectedTorusAnchorCycle, nativeCornerCycleOfChain_apply] using h

/-- The first computed representative has the same polynomial-image homology class. -/
theorem firstTorusNativeCycle_class_mem_polynomialHomologyImage
    (a : Fin (consecutiveTorusGridSize n)) :
    (laurentMaslovComplex (reflectedTorusGrid n) R).homologyπ 0 (firstTorusNativeCycle n R) ∈
      polynomialHomologyImage R (reflectedTorusGrid n) a 0 := by
  rw [firstTorusNativeCycle_homology]
  exact reflectedTorusAnchorClass_mem_polynomialHomologyImage n R a

end OnLeConjecture.KnotFloer.GridFull
