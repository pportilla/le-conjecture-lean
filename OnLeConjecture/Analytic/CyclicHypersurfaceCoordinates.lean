/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SumDifferenceCoordinates
public import OnLeConjecture.Analytic.UnitCoordinateScaling
public import OnLeConjecture.Analytic.CyclicCoverKernel
import Mathlib.Tactic

/-!
# Coordinates for the cyclic fiber-product hypersurface

An equation `(s-S)(s+S+h) + lambda^r epsilon`, where `h` has order at
least two and `epsilon` is a unit, is equivalent to `U Xi - lambda^r`.
The actual analytic coordinate change preserves `U=s-S` and `lambda`.
-/

public section

namespace OnLeConjecture.Analytic

namespace CyclicCover

/-- Normalize the hypersurface equation without changing its difference
coordinate or its parameter. -/
theorem exists_hypersurface_coordinates
    (h : Germ 3) (hh : h ∈ Germ.maximalIdeal 3 ^ 2)
    (ε : (Germ 3)ˣ) (r : ℕ) :
    ∃ e : PointedEquivGerm 3,
      e.forward.pullbackRingHom (Germ.coordinate (0 : Fin 3)) =
          Germ.coordinate 0 - Germ.coordinate 1 ∧
      e.forward.pullbackRingHom (Germ.coordinate (1 : Fin 3)) =
          -(Germ.coordinate 0 + Germ.coordinate 1 + h) * (↑(ε⁻¹) : Germ 3) ∧
      e.forward.pullbackRingHom (Germ.coordinate (2 : Fin 3)) =
          Germ.coordinate 2 ∧
      e.forward.pullbackRingHom (relationGerm r) =
        -(↑(ε⁻¹) : Germ 3) * ((Germ.coordinate 0 - Germ.coordinate 1) *
          (Germ.coordinate 0 + Germ.coordinate 1 + h) +
          Germ.coordinate 2 ^ r * (↑ε : Germ 3)) := by
  obtain ⟨d, hd0, hd1, hd2⟩ :=
    Germ.exists_sumDifference_equiv_of_mem_maximalIdeal_sq h hh
  let u : Fin 3 → Germ 3 := ![1, -↑(ε⁻¹), 1]
  have hu : ∀ i, IsUnit (u i) := by
    intro i
    fin_cases i
    · exact isUnit_one
    · exact (ε⁻¹).isUnit.neg
    · exact isUnit_one
  obtain ⟨e, he⟩ := d.exists_coordinate_mul_units u hu
  have h0 : e.forward.pullbackRingHom (Germ.coordinate (0 : Fin 3)) =
      Germ.coordinate 0 - Germ.coordinate 1 := by
    simpa [u, hd0] using he 0
  have h1 : e.forward.pullbackRingHom (Germ.coordinate (1 : Fin 3)) =
      -(Germ.coordinate 0 + Germ.coordinate 1 + h) * (↑(ε⁻¹) : Germ 3) := by
    rw [he, hd1]
    change (Germ.coordinate 0 + Germ.coordinate 1 + h) *
      (-(↑(ε⁻¹) : Germ 3)) = _
    ring
  have h2 : e.forward.pullbackRingHom (Germ.coordinate (2 : Fin 3)) =
      Germ.coordinate 2 := by
    simpa [u, hd2] using he 2
  refine ⟨e, h0, h1, h2, ?_⟩
  rw [relationGerm, map_sub, map_mul, map_pow, h0, h1, h2]
  have hinv : (↑(ε⁻¹) : Germ 3) * (↑ε : Germ 3) = 1 := ε.inv_mul
  calc
    (Germ.coordinate 0 - Germ.coordinate 1) *
        (-(Germ.coordinate 0 + Germ.coordinate 1 + h) * (↑(ε⁻¹) : Germ 3)) -
        Germ.coordinate 2 ^ r =
      -(↑(ε⁻¹) : Germ 3) * ((Germ.coordinate 0 - Germ.coordinate 1) *
        (Germ.coordinate 0 + Germ.coordinate 1 + h)) -
        Germ.coordinate 2 ^ r * ((↑(ε⁻¹) : Germ 3) * (↑ε : Germ 3)) := by
          rw [hinv]
          ring
    _ = _ := by ring

end CyclicCover

end OnLeConjecture.Analytic
