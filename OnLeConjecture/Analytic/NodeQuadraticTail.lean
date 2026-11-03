/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MatrixLinearCoordinates
public import OnLeConjecture.Analytic.OrdinaryNodeBlowup
public import OnLeConjecture.Analytic.OrdinaryNodeFactorization

/-!
# Transverse factors from a node quadratic jet

An analytic germ with quadratic jet `x²-y²` has two convergent transverse
factors. The construction does not normalize the given germ or change any
previously recorded point-basis data.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem exists_transverse_factors_of_differenceSquares_tail
    (v : Germ 2)
    (hv : v - (coordinate (0 : Fin 2) ^ 2 - coordinate (1 : Fin 2) ^ 2) ∈
      maximalIdeal 2 ^ 3) :
    ∃ f g : Germ 2, v = f * g ∧ f ∈ maximalIdeal 2 ∧ g ∈ maximalIdeal 2 ∧
      IsUnit (jacobian f g) := by
  obtain ⟨e, he⟩ := exists_equiv_linear_matrix
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) (by simp [Matrix.det_fin_two])
  have he0 : e.forward.pullbackRingHom (coordinate (0 : Fin 2)) = coordinate 0 + coordinate 1 :=
    by simpa [Fin.sum_univ_succ] using he 0
  have he1 : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 :=
    by simpa [Fin.sum_univ_succ] using he 1
  have htail := e.forward.pullback_mem_maximalIdeal_pow hv
  rw [map_sub, map_sub, map_pow, map_pow, he0, he1] at htail
  have htemplate : (coordinate (0 : Fin 2) + coordinate 1) ^ 2 - coordinate 1 ^ 2 =
      coordinate 0 * (constRingHom 2 1 * coordinate 0 + constRingHom 2 2 * coordinate 1) := by
    simp only [map_one, map_ofNat]
    ring
  rw [htemplate] at htail
  obtain ⟨f, g, hfactor, hf, hg, hjac⟩ := exists_transverse_node_factorization
    (e.forward.pullbackRingHom v) 1 2 (by norm_num) htail
  refine ⟨e.inverse.pullbackRingHom f, e.inverse.pullbackRingHom g, ?_,
    e.inverse.pullback_mem_maximalIdeal hf, e.inverse.pullback_mem_maximalIdeal hg,
    jacobian_isUnit_pullback_equiv e.symm f g hjac⟩
  have hpull := congrArg e.pullbackRingEquiv.symm hfactor
  change e.pullbackRingEquiv.symm (e.pullbackRingEquiv v) = _ at hpull
  rw [e.pullbackRingEquiv.symm_apply_apply, map_mul] at hpull
  exact hpull

theorem irreducibleBranchCount_eq_two_of_transverse_factors
    (v f g : Germ 2) (hfactor : v = f * g)
    (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hjac : IsUnit (jacobian f g)) : PlaneCurve.irreducibleBranchCount v = 2 := by
  have hfi := (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf
    (not_mem_square_of_jacobian_isUnit_left f g hjac)).2
  have hgi := (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq g hg
    (not_mem_square_of_jacobian_isUnit_right f g hjac)).2
  have hnot : ¬ Associated f g := by
    rintro ⟨u, hu⟩
    apply valueRingHom_ne_zero_of_isUnit hjac
    rw [← hu, jacobian_mul_right, jacobian_self]
    simp only [mul_zero, add_zero, map_mul, mem_maximalIdeal_iff.mp hf, zero_mul]
  exact PlaneCurve.irreducibleBranchCount_eq_two_of_eq_mul v f g hfi hgi hnot hfactor

theorem irreducibleBranchCount_eq_two_of_differenceSquares_tail
    (v : Germ 2)
    (hv : v - (coordinate (0 : Fin 2) ^ 2 - coordinate (1 : Fin 2) ^ 2) ∈
      maximalIdeal 2 ^ 3) : PlaneCurve.irreducibleBranchCount v = 2 := by
  obtain ⟨f, g, hfactor, hf, hg, hjac⟩ := exists_transverse_factors_of_differenceSquares_tail v hv
  exact irreducibleBranchCount_eq_two_of_transverse_factors v f g hfactor hf hg hjac

end OnLeConjecture.Analytic.Germ
