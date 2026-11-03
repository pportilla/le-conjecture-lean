/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.ShiftedDoubleComplex

/-! # Degree reindexing for the second stabilization summand -/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer

open CategoryTheory HomologicalComplex

variable {R : Type*} [CommRing R]

/-- Reindex a complex so that degree m is its original degree m+1. -/
def degreeSuccComplex (C : ChainComplex (ModuleCat R) ℤ) :
    ChainComplex (ModuleCat R) ℤ where
  X i := C.X (i + 1)
  d i j := C.d (i + 1) (j + 1)
  shape i j hij := C.shape _ _ (by
    simpa only [ComplexShape.down_Rel, add_right_cancel_iff] using hij)
  d_comp_d' i j k _ _ := C.d_comp_d (i + 1) (j + 1) (k + 1)

/-- Reindex a native chain map by one degree. -/
def degreeSuccMap {C D : ChainComplex (ModuleCat R) ℤ} (φ : C ⟶ D) :
    degreeSuccComplex C ⟶ degreeSuccComplex D where
  f i := φ.f (i + 1)
  comm' i j _ := φ.comm (i + 1) (j + 1)

end OnLeConjecture.KnotFloer
