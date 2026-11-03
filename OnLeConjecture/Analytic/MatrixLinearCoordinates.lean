/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.UnitCoordinateScaling
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Invertible matrices as analytic coordinates

An invertible scalar matrix gives a pointed analytic equivalence with
explicit coordinate pullbacks.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem exists_equiv_linear_matrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) :
    ∃ e : PointedEquivGerm n, ∀ i,
      e.forward.pullbackRingHom (coordinate i) = ∑ j, constRingHom n (M i j) * coordinate j := by
  let L := (Matrix.toLin' M).toContinuousLinearMap
  have hL : L.det ≠ 0 := by
    simpa only [L, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin'] using hM
  let A := L.toContinuousLinearEquivOfDetNeZero hL
  apply PointedMapGerm.exists_equiv_with_coordinate_pullbacks
    (fun i => ∑ j, constRingHom n (M i j) * coordinate j)
    (fun i => (maximalIdeal n).sum_mem fun j _ =>
      (maximalIdeal n).mul_mem_left _ (coordinate_mem_maximalIdeal j)) A
  intro i z
  change differentialLinearMap n (∑ j, constRingHom n (M i j) * coordinate j) z = A z i
  rw [map_sum]
  simp only [sum_apply, differentialLinearMap_apply, differential_mul,
    valueRingHom_const, valueRingHom_coordinate, differential_constRingHom,
    zero_smul, add_zero, smul_apply, differential_coordinate_apply, smul_eq_mul]
  change (∑ j, M i j * z j) =
    L.toContinuousLinearEquivOfDetNeZero hL z i
  rw [ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply]
  rfl

end OnLeConjecture.Analytic.Germ
