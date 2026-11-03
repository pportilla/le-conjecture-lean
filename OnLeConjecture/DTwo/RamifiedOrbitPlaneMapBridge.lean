/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.RamifiedOrbitPolynomials
public import OnLeConjecture.DTwo.RamifiedOrbitTransversality

/-!
# The first two coordinates of the ramified polynomial triple

This identity identifies the polynomial evaluation map used by weighted
collision persistence with the plane map whose strict derivative was computed.
-/

public section

namespace OnLeConjecture.DTwo

open DThree

theorem ramifiedOrbitPlaneMap_eq_firstTwo_weightedPolynomialMap
    (a : ℕ) (R : OrbitSourceForm) (q : Fin 2 → ℂ) :
    ramifiedOrbitPlaneMap a q =
      ![weightedPolynomialMap (ramifiedOrbitPolynomials a R) (orbitPointOfFinTwo q) 0,
        weightedPolynomialMap (ramifiedOrbitPolynomials a R) (orbitPointOfFinTwo q) 1] := by
  simp only [weightedPolynomialMap, ramifiedOrbitPolynomials, orbitInitialPolynomialMap,
    Matrix.cons_val_zero, Matrix.cons_val_one, ramifiedOrbitSubstitution_phi,
    ramifiedOrbitSubstitution_psi]
  simp [ramifiedOrbitPlaneMap, orbitPointOfFinTwo,
    ContinuousLinearEquiv.finTwoArrow_symm_apply]

end OnLeConjecture.DTwo
