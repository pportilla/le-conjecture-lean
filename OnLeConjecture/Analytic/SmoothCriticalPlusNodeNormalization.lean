/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SmoothCriticalNodeNormalization
public import OnLeConjecture.Analytic.DiagonalCoordinates

/-!
# Plus-sign node normalization preserving a smooth curve

A linear shear turns the quadratic initial form `x²+y²` into the form
used by the convergent transverse factorization theorem. The simultaneous
node normalization is then followed by a constant diagonal change.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem exists_transverse_factors_of_sumSquares_tail
    (v : Germ 2)
    (hv : v - (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ 2) ∈
      maximalIdeal 2 ^ 3) :
    ∃ f g : Germ 2, v = f * g ∧ f ∈ maximalIdeal 2 ∧ g ∈ maximalIdeal 2 ∧
      IsUnit (jacobian f g) := by
  let q := coordinate (0 : Fin 2) - constRingHom 2 Complex.I * coordinate (1 : Fin 2)
  have hq : q ∈ maximalIdeal 2 := (maximalIdeal 2).sub_mem (coordinate_mem_maximalIdeal 0)
    ((maximalIdeal 2).mul_mem_left _ (coordinate_mem_maximalIdeal 1))
  have hregular : differential q (firstCoordinateVector 1) ≠ 0 := by
    change differential q (coordinateVector (0 : Fin 2)) ≠ 0
    rw [← valueRingHom_partialDerivative]
    dsimp only [q]
    norm_num [partialDerivative_sub, partialDerivative_mul, partialDerivative_const,
      partialDerivative_coordinate_same, partialDerivative_coordinate_ne]
  obtain ⟨a, ha0, hafix⟩ :=
    exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension q hq hregular
  have ha1 : a.pullbackAlgEquiv (coordinate (1 : Fin 2)) = coordinate (1 : Fin 2) := by
    simpa only [hyperplaneExtension_coordinate, show (0 : Fin 1).succ = (1 : Fin 2) from rfl]
      using hafix (coordinate (0 : Fin 1))
  have hI : constRingHom 2 Complex.I ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hβ : (-2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have htemplate : a.pullbackAlgEquiv
      (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ 2) =
      coordinate (0 : Fin 2) * (constRingHom 2 1 * coordinate (0 : Fin 2) +
        constRingHom 2 (-2 * Complex.I) * coordinate (1 : Fin 2)) := by
    rw [map_add, map_pow, map_pow, ha0, ha1]
    dsimp only [q]
    simp only [map_one, map_mul, map_neg, map_ofNat]
    linear_combination coordinate (1 : Fin 2) ^ 2 * hI
  have htail := a.forward.pullback_mem_maximalIdeal_pow hv
  change a.pullbackAlgEquiv (v - _) ∈ maximalIdeal 2 ^ 3 at htail
  rw [map_sub, htemplate] at htail
  obtain ⟨f, g, hfactor, hf, hg, hjac⟩ := exists_transverse_node_factorization
    (a.pullbackAlgEquiv v) 1 (-2 * Complex.I) hβ htail
  refine ⟨a.symm.pullbackAlgEquiv f, a.symm.pullbackAlgEquiv g, ?_,
    a.symm.forward.pullback_mem_maximalIdeal hf,
    a.symm.forward.pullback_mem_maximalIdeal hg,
    jacobian_isUnit_pullback_equiv a.symm f g hjac⟩
  have hpull := congrArg a.pullbackAlgEquiv.symm hfactor
  rw [a.pullbackAlgEquiv.symm_apply_apply, map_mul] at hpull
  exact hpull

/-- The plus-sign normal form is constructed from the node jet and the
actual intersection with the specified smooth equation. -/
theorem exists_smooth_critical_plus_node_normalization
    (v h : Germ 2)
    (hv : v - (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ 2) ∈
      maximalIdeal 2 ^ 3)
    (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h v)
    (hi : PlaneCurve.intersectionMultiplicity h v hfinite = 2) :
    ∃ e : PointedEquivGerm 2, ∃ U : Germ 2, IsUnit U ∧
      e.forward.pullbackRingHom v = coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ 2 ∧
      e.forward.pullbackRingHom h = coordinate (1 : Fin 2) * U := by
  obtain ⟨f, g, hfactor, hf, hg, hjac⟩ := exists_transverse_factors_of_sumSquares_tail v hv
  obtain ⟨a, U, hU, hav, hah⟩ := exists_smooth_critical_node_normalization
    v h f g hfactor hf hg hjac hh hdh hfinite hi
  let scales : Fin 2 → ℂ := ![1, Complex.I]
  have hscales : ∀ i, scales i ≠ 0 := by
    intro i
    fin_cases i
    · exact one_ne_zero
    · exact Complex.I_ne_zero
  let d := diagonalPointedEquiv scales hscales
  have hd0 : d.pullbackAlgEquiv (coordinate (0 : Fin 2)) = coordinate (0 : Fin 2) := by
    rw [show d.pullbackAlgEquiv (coordinate (0 : Fin 2)) = d.forward.1.component 0 from
      d.forward.pullback_coordinate 0, diagonalPointedEquiv_component]
    change constRingHom 2 1 * coordinate 0 = coordinate 0
    rw [map_one, one_mul]
  have hd1 : d.pullbackAlgEquiv (coordinate (1 : Fin 2)) =
      constRingHom 2 Complex.I * coordinate (1 : Fin 2) := by
    rw [show d.pullbackAlgEquiv (coordinate (1 : Fin 2)) = d.forward.1.component 1 from
      d.forward.pullback_coordinate 1, diagonalPointedEquiv_component]
    rfl
  have hIunit : IsUnit (constRingHom 2 Complex.I) :=
    isUnit_iff_valueRingHom_ne_zero.mpr (by simp)
  refine ⟨a.comp d, constRingHom 2 Complex.I * d.pullbackAlgEquiv U,
    hIunit.mul (hU.map d.pullbackAlgEquiv.toRingHom), ?_, ?_⟩
  · change (a.comp d).pullbackAlgEquiv v = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    change d.pullbackAlgEquiv (a.forward.pullbackRingHom v) = _
    rw [hav, map_sub, map_pow, map_pow, hd0, hd1, mul_pow, ← map_pow, Complex.I_sq,
      map_neg, map_one, neg_one_mul, sub_neg_eq_add]
  · change (a.comp d).pullbackAlgEquiv h = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    change d.pullbackAlgEquiv (a.forward.pullbackRingHom h) = _
    rw [hah, map_mul, hd1]
    ring

end OnLeConjecture.Analytic.Germ
