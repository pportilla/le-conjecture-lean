/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HResidual

/-!
# The Cramer identity in Lemma `dthree-Horders`

This file proves the algebraic identity behind the formula for `d[R]/dw`.
The variables `R_x` and `R_w` represent the two partial derivatives of an
arbitrary function.  The variables `dX` and `dW` represent a tangent vector to
a fibre of the `H` pair.
-/

public section

namespace OnLeConjecture.DThree

variable {K : Type*} [Field K] [CharZero K]

/-- The partial derivative `P_x`. -/
@[expose]
noncomputable def hPPartialX (x w : K) : K :=
  3 * x ^ 2 + 3 * w

/-- The partial derivative `P_w`. -/
@[expose]
noncomputable def hPPartialW (x : K) : K :=
  3 * x

/-- The partial derivative `Q_x`. -/
@[expose]
noncomputable def hQPartialX (x w : K) : K :=
  4 * x ^ 3 + 8 * x * w

/-- The partial derivative `Q_w`. -/
@[expose]
noncomputable def hQPartialW (x w : K) : K :=
  4 * x ^ 2 + 4 * w

/-- The quotient `J(P,R)/w^2` at a point, expressed through the partial
derivatives of `R`. -/
@[expose]
noncomputable def hLambdaP
    (x w R_x R_w : K) : K :=
  (hPPartialX x w * R_w - hPPartialW x * R_x) / w ^ 2

/-- The quotient `J(Q,R)/w^2` at a point, expressed through the partial
derivatives of `R`. -/
@[expose]
noncomputable def hLambdaQ
    (x w R_x R_w : K) : K :=
  (hQPartialX x w * R_w - hQPartialW x w * R_x) / w ^ 2

omit [CharZero K] in
/-- The determinant of the two coordinate gradients is `12 w^2`. -/
theorem h_partial_jacobian_identity (x w : K) :
    hPPartialX x w * hQPartialW x w -
        hPPartialW x * hQPartialX x w = 12 * w ^ 2 := by
  simp only [hPPartialX, hPPartialW, hQPartialX, hQPartialW]
  exact h_jacobian_identity x w

/-- Cramer's rule expresses the derivative of `R` along a tangent vector in
terms of `hLambdaP` and `hLambdaQ`. -/
theorem h_cramer_tangent_identity
    {x w R_x R_w dX dW A B : K}
    (hw : w ≠ 0)
    (hA : A = hPPartialX x w * dX + hPPartialW x * dW)
    (hB : B = hQPartialX x w * dX + hQPartialW x w * dW) :
    R_x * dX + R_w * dW =
      (-A * hLambdaQ x w R_x R_w +
          B * hLambdaP x w R_x R_w) / 12 := by
  rw [hA, hB]
  simp only [hLambdaP, hLambdaQ, hPPartialX, hPPartialW,
    hQPartialX, hQPartialW]
  field_simp [hw]
  ring

/-- At `(1,w)`, the tangent vector `(0,1)` gives the first value in the
difference formula for `d[R]/dw`. -/
theorem h_cramer_vertical_identity
    {w R_x R_w : K} (hw : w ≠ 0) :
    R_w =
      (-3 * hLambdaQ 1 w R_x R_w +
          4 * (1 + w) * hLambdaP 1 w R_x R_w) / 12 := by
  simp only [hLambdaP, hLambdaQ, hPPartialX, hPPartialW,
    hQPartialX, hQPartialW]
  field_simp [hw]
  ring

/-- The difference of the two Cramer formulas is the identity for `d[R]/dw`
in Lemma `dthree-Horders`. -/
theorem h_cramer_difference_identity
    {w X W R_x R_w S_x S_w dX dW : K}
    (hw : w ≠ 0) (hW : W ≠ 0)
    (hP_tangent :
      3 = hPPartialX X W * dX + hPPartialW X * dW)
    (hQ_tangent :
      4 * (1 + w) =
        hQPartialX X W * dX + hQPartialW X W * dW) :
    R_w - (S_x * dX + S_w * dW) =
      (-3 *
          (hLambdaQ 1 w R_x R_w - hLambdaQ X W S_x S_w) +
        4 * (1 + w) *
          (hLambdaP 1 w R_x R_w - hLambdaP X W S_x S_w)) / 12 := by
  have hfirst := h_cramer_vertical_identity (w := w) (R_x := R_x)
    (R_w := R_w) hw
  have hsecond := h_cramer_tangent_identity
    (x := X) (w := W) (R_x := S_x) (R_w := S_w)
    (dX := dX) (dW := dW) (A := 3) (B := 4 * (1 + w))
    hW hP_tangent hQ_tangent
  calc
    R_w - (S_x * dX + S_w * dW) =
        (-3 * hLambdaQ 1 w R_x R_w +
            4 * (1 + w) * hLambdaP 1 w R_x R_w) / 12 -
          (-3 * hLambdaQ X W S_x S_w +
            4 * (1 + w) * hLambdaP X W S_x S_w) / 12 :=
      congrArg₂ (fun a b : K ↦ a - b) hfirst hsecond
    _ = _ := by ring

end OnLeConjecture.DThree
