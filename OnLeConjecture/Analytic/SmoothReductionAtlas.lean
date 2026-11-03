/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectivePointBasisCompleteness
public import OnLeConjecture.Analytic.SmoothReductionCoordinates

/-!
# Transverse regularity of the constructed smooth critical coordinates

The monic distinguished polynomial and retained unit in the constructed
coordinates imply the exact transverse order. This supplies the root
input to the projective atlas construction.
-/

public section

namespace OnLeConjecture.Analytic.SmoothReductionCoordinates

open OnLeConjecture.Analytic.Germ
open _root_.Polynomial

variable {g : PointedMapGerm 2 3} {h : Germ 2} {m : ℕ}
    (S : SmoothReductionCoordinates g h m)

theorem polynomial_residue : S.polynomial.map (valueRingHom 1) = X ^ m := by
  ext i
  rw [coeff_map, coeff_X_pow]
  by_cases hi : i = m
  · subst i
    have hcoeff : S.polynomial.coeff m = 1 := by
      simpa only [S.degree] using S.monic.coeff_natDegree
    rw [hcoeff, map_one, if_pos rfl]
  · by_cases hlt : i < m
    · rw [mem_maximalIdeal_iff.mp (S.distinguished i hlt), if_neg hi]
    · have hdeg : S.polynomial.natDegree < i := by rw [S.degree]; omega
      rw [coeff_eq_zero_of_natDegree_lt hdeg, map_zero, if_neg hi]

theorem source_first_regular :
    IsRegularInFirstCoordinateOfOrder (S.source.forward.pullbackRingHom (g.1.component 0)) m := by
  rw [S.first_prepared, mul_comm]
  apply (isRegularInFirstCoordinateOfOrder_unit_mul_iff _ _ S.multiplier_unit).mpr
  change vanishingOrder ((lineGerm (firstCoordinateVector 1)).pullbackRingHom
    (firstCoordinatePolynomialEvaluation S.polynomial)) = m
  rw [← pointBlowupExceptionalLine_eq_lineGerm, firstAxis_pullback_polynomialEvaluation,
    S.polynomial_residue]
  rw [map_pow, oneVariablePolynomialEvaluation, aeval_X]
  exact vanishingOrder_coordinate_pow m

theorem first_regular : IsRegularInFirstCoordinateOfOrder (S.map.1.component 0) m := by
  rw [S.component]
  exact S.source_first_regular

end OnLeConjecture.Analytic.SmoothReductionCoordinates
