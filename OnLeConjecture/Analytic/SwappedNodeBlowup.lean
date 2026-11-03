/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrdinaryNodeBlowup
import Mathlib.Tactic

/-!
# The node calculation with the coordinate tangents interchanged
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem coordinateSwapPointedEquiv_pullback_second :
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom (coordinate 1) =
      coordinate (0 : Fin 2) := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [coordinateSwapPointedEquiv, pointedEquivGermOfContinuousLinearEquiv]
  apply Subtype.ext
  change ((MapGerm.ofFunction (coordinateSwapEquiv (1 : Fin 2))
    ((coordinateSwapEquiv (1 : Fin 2)).analyticAt 0)).component 1).1 = (coordinate (0 : Fin 2)).1
  rw [MapGerm.component_ofFunction, coe_coordinate]
  apply Filter.Germ.coe_eq.mpr
  refine Filter.Eventually.of_forall fun z ↦ ?_
  change (Equiv.piCongrLeft (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1) z) 1 = z 0
  simp [Equiv.piCongrLeft]

theorem exists_transverse_swapped_node_factorization
    (v : Germ 2) (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (1 : Fin 2) *
      (constRingHom 2 α * coordinate (1 : Fin 2) +
        constRingHom 2 β * coordinate (0 : Fin 2)) ∈ maximalIdeal 2 ^ 3) :
    ∃ F G : Germ 2, v = F * G ∧ F ∈ maximalIdeal 2 ∧ G ∈ maximalIdeal 2 ∧
      IsUnit (jacobian F G) := by
  let e := coordinateSwapPointedEquiv (1 : Fin 2)
  have ht := e.forward.pullback_mem_maximalIdeal_pow hv
  have hx : e.forward.pullbackRingHom (coordinate (0 : Fin 2)) = coordinate (1 : Fin 2) := by
    rw [PointedMapGerm.pullback_coordinate]
    exact coordinateSwapPointedEquiv_component_zero 1
  have hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate (0 : Fin 2) :=
    coordinateSwapPointedEquiv_pullback_second
  rw [map_sub, map_mul, map_add, map_mul, map_mul,
    PointedMapGerm.pullback_constRingHom, PointedMapGerm.pullback_constRingHom, hx, hy] at ht
  obtain ⟨F, G, hfactor, hF, hG, hJac⟩ :=
    exists_transverse_node_factorization (e.forward.pullbackRingHom v) α β hβ ht
  refine ⟨e.inverse.pullbackRingHom F, e.inverse.pullbackRingHom G, ?_, ?_, ?_, ?_⟩
  · have h := congrArg e.pullbackRingEquiv.symm hfactor
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv v) =
      e.pullbackRingEquiv.symm (F * G) at h
    simpa only [RingEquiv.symm_apply_apply, map_mul, PointedEquivGerm.pullbackRingEquiv_symm_apply]
      using h
  · simpa only [pow_one] using e.inverse.pullback_mem_maximalIdeal_pow
      (by simpa only [pow_one] using hF : F ∈ maximalIdeal 2 ^ 1)
  · simpa only [pow_one] using e.inverse.pullback_mem_maximalIdeal_pow
      (by simpa only [pow_one] using hG : G ∈ maximalIdeal 2 ^ 1)
  · exact jacobian_isUnit_pullback_equiv e.symm F G hJac

theorem pointBlowup_swapped_node_not_mem_square
    (e : PointedEquivGerm 2) (c : ℂ) (v U T : Germ 2) (hU : IsUnit U)
    (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (1 : Fin 2) *
      (constRingHom 2 α * coordinate (1 : Fin 2) +
        constRingHom 2 β * coordinate (0 : Fin 2)) ∈ maximalIdeal 2 ^ 3)
    (htransform : (pointBlowupChartGerm c).pullbackRingHom
      (e.forward.pullbackRingHom (v * U)) = coordinate (1 : Fin 2) ^ 2 * T) :
    T ∉ maximalIdeal 2 ^ 2 := by
  obtain ⟨F, G, hfactor, hF, hG, hJac⟩ := exists_transverse_swapped_node_factorization v α β hβ hv
  apply pointBlowup_transverse_product_not_mem_square c
    (e.forward.pullbackRingHom F) (e.forward.pullbackRingHom (G * U)) T
  · simpa only [pow_one] using e.forward.pullback_mem_maximalIdeal_pow
      (by simpa only [pow_one] using hF : F ∈ maximalIdeal 2 ^ 1)
  · have hGU := (maximalIdeal 2).mul_mem_right U hG
    simpa only [pow_one] using e.forward.pullback_mem_maximalIdeal_pow
      (by simpa only [pow_one] using hGU : G * U ∈ maximalIdeal 2 ^ 1)
  · exact jacobian_isUnit_pullback_equiv e F (G * U)
      (jacobian_isUnit_mul_unit_right F G U hG hJac hU)
  · simpa only [hfactor, mul_assoc, map_mul] using htransform

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.AnalyticPointBasis

open OnLeConjecture.Analytic.Germ

theorem swapped_node_child_not_mem_square
    {N : ℕ} (c : AnalyticPointBasis N) (p : Fin N) (hp : c.multiplicity p = 2)
    (v U : Germ 2) (hU : IsUnit U) (hidentity : c.germ p = v * U)
    (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (1 : Fin 2) *
      (constRingHom 2 α * coordinate (1 : Fin 2) +
        constRingHom 2 β * coordinate (0 : Fin 2)) ∈ maximalIdeal 2 ^ 3)
    (q : Fin N) (hq : c.ParentRelation q p) : c.germ q ∉ maximalIdeal 2 ^ 2 := by
  apply pointBlowup_swapped_node_not_mem_square (c.sourceCoordinates q) (c.chartCenter q)
    v U (c.germ q) hU α β hβ hv
  have h := c.transform_identity q hq.1
  simpa only [hq.2, hp, hidentity] using h

end OnLeConjecture.Analytic.AnalyticPointBasis
