/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SquareJetMemberNormalization
public import OnLeConjecture.DTwo.QuadraticJetAlgebra

/-!
# Normalizing a specified member with a square quadratic initial form

The vanishing discriminant gives a linear square with nonzero coefficient.
A complex square root absorbs that coefficient. Smooth straightening and
quadratic normalization then act on the specified analytic member.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem exists_smooth_square_root_of_quadratic_discriminant_zero
    (Q : OrbitSourceForm) (hQ : Q.IsHomogeneous 2) (hne : Q ≠ 0)
    (hdisc : binaryQuadraticDiscriminant Q = 0) :
    ∃ l : Germ 2, l ∈ maximalIdeal 2 ∧ differential l ≠ 0 ∧
      coordinatePolynomialAlgHom 2 Q = l ^ 2 := by
  obtain ⟨a, u, v, ha, huv, hform⟩ :=
    exists_scalar_mul_linear_sq_of_discriminant_eq_zero hQ hne hdisc
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (by decide : 0 < 2)
  have hbne : b ≠ 0 := by
    intro hz
    apply ha
    simpa only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using hb.symm
  let l : Germ 2 := constRingHom 2 b *
    (constRingHom 2 u * coordinate 0 + constRingHom 2 v * coordinate 1)
  have hl : l ∈ maximalIdeal 2 :=
    (maximalIdeal 2).mul_mem_left _ ((maximalIdeal 2).add_mem
      ((maximalIdeal 2).mul_mem_left _ (coordinate_mem_maximalIdeal 0))
      ((maximalIdeal 2).mul_mem_left _ (coordinate_mem_maximalIdeal 1)))
  have hderiv0 : valueRingHom 2 (partialDerivative (0 : Fin 2) l) = b * u := by
    simp [l, partialDerivative_mul, partialDerivative_add,
      partialDerivative_const, partialDerivative_coordinate_same, partialDerivative_coordinate_ne]
  have hderiv1 : valueRingHom 2 (partialDerivative (1 : Fin 2) l) = b * v := by
    simp [l, partialDerivative_mul, partialDerivative_add,
      partialDerivative_const, partialDerivative_coordinate_same, partialDerivative_coordinate_ne]
  have hdl : differential l ≠ 0 := by
    intro hd
    have hzero := (differential_eq_zero_iff_partialDerivatives_vanish l).mp hd
    rcases huv with hu | hv
    · exact mul_ne_zero hbne hu (hderiv0.symm.trans (hzero 0))
    · exact mul_ne_zero hbne hv (hderiv1.symm.trans (hzero 1))
  refine ⟨l, hl, hdl, ?_⟩
  have hb' : constRingHom 2 b ^ 2 = constRingHom 2 a := by rw [← map_pow, hb]
  rw [hform]
  simp only [map_mul, map_pow, coordinatePolynomialAlgHom_C, binaryLinearForm,
    orbitPolynomialS, orbitPolynomialLambda, map_add, coordinatePolynomialAlgHom_X]
  dsimp only [l]
  rw [mul_pow, hb']

theorem exists_square_quadratic_member_normalization
    (v : Germ 2) (Q : OrbitSourceForm) (hQ : Q.IsHomogeneous 2) (hne : Q ≠ 0)
    (hdisc : binaryQuadraticDiscriminant Q = 0)
    (hv : v - coordinatePolynomialAlgHom 2 Q ∈ maximalIdeal 2 ^ 3)
    (hreduced : Squarefree v) :
    ∃ k : ℕ, 3 ≤ k ∧ ∃ e : PointedEquivGerm 2,
      e.forward.pullbackRingHom v = PlaneCurve.morseCurve k := by
  obtain ⟨l, hl, hdl, hQeq⟩ :=
    exists_smooth_square_root_of_quadratic_discriminant_zero Q hQ hne hdisc
  exact exists_smooth_square_jet_member_normalization v l hl hdl
    (by rwa [← hQeq]) hreduced

end OnLeConjecture.DTwo
