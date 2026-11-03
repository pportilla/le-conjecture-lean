/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParametricGermDivision
public import OnLeConjecture.Analytic.SumDifferenceCoordinates
public import OnLeConjecture.Analytic.CyclicHypersurfaceCoordinates
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# The hypersurface equation after eliminating the second source coordinate

Parametric analytic division and the power-difference identity give the
factored first plane equation. Its correction has order at least two when
`p ≥ 3`, so the sum-and-difference coordinates are constructed by the
analytic inverse function theorem.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- The polynomial quotient of the difference of two powers. -/
@[expose] noncomputable def powerDifferenceQuotient (p : ℕ) : Germ 3 :=
  ∑ i ∈ Finset.range p,
    coordinate (0 : Fin 3) ^ i * coordinate (1 : Fin 3) ^ (p - 1 - i)

theorem powerDifferenceQuotient_identity (p : ℕ) :
    (coordinate (0 : Fin 3) - coordinate (1 : Fin 3)) * powerDifferenceQuotient p =
      coordinate 0 ^ p - coordinate 1 ^ p :=
  (Commute.all (coordinate (0 : Fin 3)) (coordinate (1 : Fin 3))).mul_geom_sum₂ p

theorem powerDifferenceQuotient_mem_maximalIdeal_pow (p : ℕ) :
    powerDifferenceQuotient p ∈ maximalIdeal 3 ^ (p - 1) := by
  apply Submodule.sum_mem
  intro i hi
  have hi' : i < p := Finset.mem_range.mp hi
  have hterm := Ideal.mul_mem_mul
    (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (0 : Fin 3)) i)
    (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (1 : Fin 3)) (p - 1 - i))
  rw [← pow_add, show i + (p - 1 - i) = p - 1 by omega] at hterm
  exact hterm

/-- Substitution of the power difference and the remaining parameter. -/
@[expose] noncomputable def powerDifferenceParameters (p : ℕ) : PointedMapGerm 3 2 :=
  PointedMapGerm.ofFunction
    (fun q : Source 3 => ![q 0 ^ p - q 1 ^ p, q 2])
    (by
      apply AnalyticAt.pi
      intro i
      have hq (j : Fin 3) : AnalyticAt ℂ (fun q : Source 3 => q j) 0 :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j).analyticAt 0
      fin_cases i
      · exact ((hq 0).pow p).sub ((hq 1).pow p)
      · exact hq 2)
    (by ext i; fin_cases i <;> simp)

@[simp] theorem powerDifferenceParameters_pullback_first (p : ℕ) :
    (powerDifferenceParameters p).pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate (0 : Fin 3) ^ p - coordinate (1 : Fin 3) ^ p := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  simp only [powerDifferenceParameters, PointedMapGerm.ofFunction,
    MapGerm.component_ofFunction]
  rfl

@[simp] theorem powerDifferenceParameters_pullback_second (p : ℕ) :
    (powerDifferenceParameters p).pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinate (2 : Fin 3) := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  simp only [powerDifferenceParameters, PointedMapGerm.ofFunction,
    MapGerm.component_ofFunction, coe_coordinate]
  rfl

/-- The parameter-only part of a two-variable defect, after substitution. -/
@[expose] noncomputable def cyclicParameterDefect (p : ℕ) (D : Germ 2) : Germ 3 :=
  (powerDifferenceParameters p).pullbackRingHom
    (hyperplaneExtension 1 (hyperplaneRestriction 1 D))

/-- The analytic hypersurface factorization and its actual coordinates.
The correction's order is proved, not included as a hypothesis. -/
theorem exists_cyclicPlane_hypersurface_coordinates
    (p ν : ℕ) (hp : 3 ≤ p) (D : Germ 2) :
    ∃ K h : Germ 3, ∃ e : PointedEquivGerm 3,
      h ∈ maximalIdeal 3 ^ 2 ∧
      (powerDifferenceParameters p).pullbackRingHom D =
        cyclicParameterDefect p D + (coordinate 0 ^ p - coordinate 1 ^ p) * K ∧
      h = coordinate 2 ^ ν * powerDifferenceQuotient p * K ∧
      e.forward.pullbackRingHom (coordinate (0 : Fin 3)) = coordinate 0 - coordinate 1 ∧
      e.forward.pullbackRingHom (coordinate (1 : Fin 3)) = coordinate 0 + coordinate 1 + h ∧
      e.forward.pullbackRingHom (coordinate (2 : Fin 3)) = coordinate 2 ∧
      coordinate (0 : Fin 3) ^ 2 - coordinate (1 : Fin 3) ^ 2 +
          coordinate 2 ^ ν * (powerDifferenceParameters p).pullbackRingHom D =
        e.forward.pullbackRingHom (coordinate 0 * coordinate 1) +
          coordinate 2 ^ ν * cyclicParameterDefect p D := by
  obtain ⟨q, hq⟩ := exists_eq_hyperplaneExtension_add_coordinate_mul D
  let K := (powerDifferenceParameters p).pullbackRingHom q
  have hD : (powerDifferenceParameters p).pullbackRingHom D =
      cyclicParameterDefect p D + (coordinate 0 ^ p - coordinate 1 ^ p) * K := by
    have heq := congrArg (powerDifferenceParameters p).pullbackRingHom hq
    simpa only [map_add, map_mul, powerDifferenceParameters_pullback_first,
      cyclicParameterDefect, K] using heq
  let h : Germ 3 := coordinate 2 ^ ν * powerDifferenceQuotient p * K
  have hh : h ∈ maximalIdeal 3 ^ 2 := by
    have hquot : powerDifferenceQuotient p ∈ maximalIdeal 3 ^ 2 :=
      (Ideal.pow_le_pow_right (show 2 ≤ p - 1 by omega))
        (powerDifferenceQuotient_mem_maximalIdeal_pow p)
    exact (maximalIdeal 3 ^ 2).mul_mem_right K
      ((maximalIdeal 3 ^ 2).mul_mem_left (coordinate 2 ^ ν) hquot)
  obtain ⟨e, he0, he1, he2⟩ := exists_sumDifference_equiv_of_mem_maximalIdeal_sq h hh
  refine ⟨K, h, e, hh, hD, rfl, he0, he1, he2, ?_⟩
  rw [hD, map_mul, he0, he1, ← powerDifferenceQuotient_identity p]
  dsimp only [h]
  ring

/-- Once the parameter defect has a coordinate-power unit factor, the
original first plane equation is analytically equivalent to the cyclic
hypersurface equation. -/
theorem exists_cyclicPlane_normalized_hypersurface
    (p ν r : ℕ) (hp : 3 ≤ p) (D : Germ 2) (ε : (Germ 3)ˣ)
    (hdefect : coordinate (2 : Fin 3) ^ ν * cyclicParameterDefect p D =
      coordinate 2 ^ r * (↑ε : Germ 3)) :
    ∃ e : PointedEquivGerm 3,
      e.forward.pullbackRingHom (coordinate (0 : Fin 3)) = coordinate 0 - coordinate 1 ∧
      e.forward.pullbackRingHom (coordinate (2 : Fin 3)) = coordinate 2 ∧
      e.forward.pullbackRingHom (Analytic.CyclicCover.relationGerm r) =
        -(↑(ε⁻¹) : Germ 3) *
          (coordinate (0 : Fin 3) ^ 2 - coordinate (1 : Fin 3) ^ 2 +
            coordinate 2 ^ ν * (powerDifferenceParameters p).pullbackRingHom D) := by
  obtain ⟨K, h, d, hh, hD, hhEq, hd0, hd1, _, heq⟩ :=
    exists_cyclicPlane_hypersurface_coordinates p ν hp D
  obtain ⟨e, he0, _, he2, heR⟩ :=
    Analytic.CyclicCover.exists_hypersurface_coordinates h hh ε r
  refine ⟨e, he0, he2, ?_⟩
  rw [heR, heq, map_mul, hd0, hd1, hdefect]

end OnLeConjecture.DTwo
