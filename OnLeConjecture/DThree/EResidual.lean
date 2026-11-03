/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# The residual fibre product for the `E` pair

This file formalizes the explicit algebra in the first part of Lemma
`dthree-Edouble`.  It proves the parametrization in equation
`dthree-Erespar`, including its converse away from the diagonal.  It also
records the monic relation for the finite map and the difference factorization
in equation `dthree-EB`.
-/

public section

namespace OnLeConjecture.DThree

variable {K : Type*} [Field K] [CharZero K]

/-- The cubic coordinate of the `E` pair after writing `w = t^3`. -/
@[expose]
noncomputable def eP (x w : K) : K :=
  x ^ 3 + 3 * w

/-- The quartic coordinate of the `E` pair after writing `w = t^3`. -/
@[expose]
noncomputable def eQ (x w : K) : K :=
  x ^ 4 + 4 * x * w

/-- The first `w` coordinate in the residual parametrization by `x` and `X`.
The second coordinate is `eResidualW X x`. -/
@[expose]
noncomputable def eResidualW (x X : K) : K :=
  (X ^ 3 + X ^ 2 * x + X * x ^ 2 - 3 * x ^ 3) / 12

/-- The coordinate `eP` on the residual parametrization. -/
theorem eP_on_residual (x X : K) :
    eP x (eResidualW x X) =
      (x + X) * (x ^ 2 + X ^ 2) / 4 := by
  simp only [eP, eResidualW]
  field_simp
  ring

/-- The coordinate `eQ` on the residual parametrization. -/
theorem eQ_on_residual (x X : K) :
    eQ x (eResidualW x X) =
      x * X * (x ^ 2 + x * X + X ^ 2) / 3 := by
  simp only [eQ, eResidualW]
  field_simp
  ring

/-- The parametrization in equation `dthree-Erespar` lies in the fibre
product of `(eP, eQ)`. -/
theorem e_residual_parametrizes_fibre (x X : K) :
    eP x (eResidualW x X) = eP X (eResidualW X x) ∧
      eQ x (eResidualW x X) = eQ X (eResidualW X x) := by
  constructor
  · rw [eP_on_residual, eP_on_residual]
    ring
  · rw [eQ_on_residual, eQ_on_residual]
    ring

private theorem e_residual_w_of_fibre
    {x X w W : K}
    (hx : x ≠ X)
    (hP : eP x w = eP X W)
    (hQ : eQ x w = eQ X W) :
    w = eResidualW x X := by
  have hxsub : x - X ≠ 0 := sub_ne_zero.mpr hx
  have hfactor :
      (x - X) *
          (12 * w - (X ^ 3 + X ^ 2 * x + X * x ^ 2 - 3 * x ^ 3)) = 0 := by
    simp only [eP] at hP
    simp only [eQ] at hQ
    linear_combination 3 * hQ - 4 * X * hP
  have hnumerator :
      12 * w - (X ^ 3 + X ^ 2 * x + X * x ^ 2 - 3 * x ^ 3) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hxsub
  simp only [eResidualW]
  field_simp
  linear_combination hnumerator

/-- Away from the diagonal, equality of the two `E` coordinates is equivalent
to the residual parametrization in equation `dthree-Erespar`. -/
theorem e_fibre_iff_residual
    {x X w W : K} (hx : x ≠ X) :
    (eP x w = eP X W ∧ eQ x w = eQ X W) ↔
      (w = eResidualW x X ∧ W = eResidualW X x) := by
  constructor
  · rintro ⟨hP, hQ⟩
    exact ⟨e_residual_w_of_fibre hx hP hQ,
      e_residual_w_of_fibre hx.symm hP.symm hQ.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact e_residual_parametrizes_fibre x X

/-- The first equation defining the residual degree nine curve after the
substitution `w = t^3`. -/
theorem e_residual_first_equation (x X : K) :
    12 * eResidualW x X +
        (x - X) * (X ^ 2 + 2 * X * x + 3 * x ^ 2) = 0 := by
  simp only [eResidualW]
  field_simp
  ring

/-- The second equation defining the residual degree nine curve after the
substitution `W = T^3`. -/
theorem e_residual_second_equation (x X : K) :
    12 * eResidualW X x -
        (x - X) * (3 * X ^ 2 + 2 * X * x + x ^ 2) = 0 := by
  simp only [eResidualW]
  field_simp
  ring

/-- Away from `x = X`, the two equations in `dthree-C9` define exactly the
fibre product of the original homogeneous `E` pair. -/
theorem e_fibre_iff_C9
    {x t X T : K} (hx : x ≠ X) :
    (eP x (t ^ 3) = eP X (T ^ 3) ∧
        eQ x (t ^ 3) = eQ X (T ^ 3)) ↔
      (12 * t ^ 3 +
            (x - X) * (X ^ 2 + 2 * X * x + 3 * x ^ 2) = 0 ∧
        12 * T ^ 3 -
            (x - X) * (3 * X ^ 2 + 2 * X * x + x ^ 2) = 0) := by
  constructor
  · intro h
    rcases (e_fibre_iff_residual hx).mp h with ⟨hw, hW⟩
    constructor
    · rw [hw]
      exact e_residual_first_equation x X
    · rw [hW]
      exact e_residual_second_equation x X
  · rintro ⟨hfirst, hsecond⟩
    apply (e_fibre_iff_residual hx).mpr
    constructor
    · apply mul_left_cancel₀ (by norm_num : (12 : K) ≠ 0)
      linear_combination hfirst - e_residual_first_equation x X
    · apply mul_left_cancel₀ (by norm_num : (12 : K) ≠ 0)
      linear_combination hsecond - e_residual_second_equation x X

omit [CharZero K] in
/-- The monic quartic relation used to present `K[x,w]` over `K[eP,eQ]`. -/
theorem e_monic_relation (x w : K) :
    x ^ 4 - 4 * eP x w * x + 3 * eQ x w = 0 := by
  simp only [eP, eQ]
  ring

/-- A value written in the basis `1, x, x^2, x^3` over the coordinate ring
of the image. -/
@[expose]
noncomputable def eBasisValue
    (c0 c1 c2 c3 x : K) : K :=
  c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3

/-- The factor denoted by `Theta_R` in equation `dthree-EB`. -/
@[expose]
noncomputable def eTheta
    (c1 c2 c3 x X : K) : K :=
  c1 + c2 * (x + X) + c3 * (x ^ 2 + x * X + X ^ 2)

omit [CharZero K] in
/-- Equation `dthree-EB` for common coefficient values on two points of one
fibre. -/
theorem e_basis_difference_factorization
    (c0 c1 c2 c3 x X : K) :
    eBasisValue c0 c1 c2 c3 x - eBasisValue c0 c1 c2 c3 X =
      (x - X) * eTheta c1 c2 c3 x X := by
  simp only [eBasisValue, eTheta]
  ring

end OnLeConjecture.DThree
