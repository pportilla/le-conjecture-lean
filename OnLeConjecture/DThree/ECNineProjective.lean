/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ENoninvariantRotation
public import OnLeConjecture.DThree.EInvariantCollision
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# The projective C9 curve and its difference section

This file defines the two homogeneous cubic equations of the C9 curve in
projective three space.  It also defines the homogeneous difference section
associated with a binary form.  Vanishing of the section away from the point
`[1:0:1:0]` supplies two distinct source points with the same values under the
three initial coordinates.
-/

public section

namespace OnLeConjecture.DThree

open scoped LinearAlgebra.Projectivization

/-- The vector space with coordinates `(x,t,X,T)` used for the C9 curve. -/
abbrev ECNineAmbient := Fin 4 → ℂ

/-- The homogeneous coordinate `x` on the C9 ambient space. -/
@[expose]
noncomputable def eCNineX : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.X 0

/-- The homogeneous coordinate `t` on the C9 ambient space. -/
@[expose]
noncomputable def eCNineT : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.X 1

/-- The homogeneous coordinate `X` on the C9 ambient space. -/
@[expose]
noncomputable def eCNineCapitalX : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.X 2

/-- The homogeneous coordinate `T` on the C9 ambient space. -/
@[expose]
noncomputable def eCNineCapitalT : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.X 3

/-- The first cubic equation of the C9 curve. -/
@[expose]
noncomputable def eCNineFirstPolynomial : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.C 12 * eCNineT ^ 3 +
    (eCNineX - eCNineCapitalX) *
      (eCNineCapitalX ^ 2 +
        MvPolynomial.C 2 * eCNineCapitalX * eCNineX +
        MvPolynomial.C 3 * eCNineX ^ 2)

/-- The second cubic equation of the C9 curve. -/
@[expose]
noncomputable def eCNineSecondPolynomial : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.C 12 * eCNineCapitalT ^ 3 -
    (eCNineX - eCNineCapitalX) *
      (MvPolynomial.C 3 * eCNineCapitalX ^ 2 +
        MvPolynomial.C 2 * eCNineCapitalX * eCNineX + eCNineX ^ 2)

/-- The difference of a binary form on the two pairs of C9 coordinates. -/
@[expose]
noncomputable def eCNineDifferenceSection
    (R : Form ℂ) : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.aeval ![eCNineX, eCNineT] R -
    MvPolynomial.aeval ![eCNineCapitalX, eCNineCapitalT] R

/-- The first C9 equation evaluated at `(x,t,X,T)`. -/
@[expose]
noncomputable def eCNineFirstValue (x t X _T : ℂ) : ℂ :=
  12 * t ^ 3 + (x - X) * (X ^ 2 + 2 * X * x + 3 * x ^ 2)

/-- The second C9 equation evaluated at `(x,t,X,T)`. -/
@[expose]
noncomputable def eCNineSecondValue (x _t X T : ℂ) : ℂ :=
  12 * T ^ 3 - (x - X) * (3 * X ^ 2 + 2 * X * x + x ^ 2)

/-- The two scalar C9 equations. -/
@[expose]
def ECNineEquations (x t X T : ℂ) : Prop :=
  eCNineFirstValue x t X T = 0 ∧ eCNineSecondValue x t X T = 0

/-- The scalar value of the difference section. -/
@[expose]
noncomputable def eCNineDifferenceValue
    (R : Form ℂ) (x t X T : ℂ) : ℂ :=
  MvPolynomial.eval ![x, t] R - MvPolynomial.eval ![X, T] R

@[simp]
theorem eCNineFirstPolynomial_eval (x t X T : ℂ) :
    MvPolynomial.eval ![x, t, X, T] eCNineFirstPolynomial =
      eCNineFirstValue x t X T := by
  simp [eCNineFirstPolynomial, eCNineFirstValue, eCNineX, eCNineT,
    eCNineCapitalX]

@[simp]
theorem eCNineSecondPolynomial_eval (x t X T : ℂ) :
    MvPolynomial.eval ![x, t, X, T] eCNineSecondPolynomial =
      eCNineSecondValue x t X T := by
  simp [eCNineSecondPolynomial, eCNineSecondValue, eCNineX,
    eCNineCapitalX, eCNineCapitalT]

@[simp]
theorem eCNineDifferenceSection_eval
    (R : Form ℂ) (x t X T : ℂ) :
    MvPolynomial.eval ![x, t, X, T] (eCNineDifferenceSection R) =
      eCNineDifferenceValue R x t X T := by
  change MvPolynomial.aeval ![x, t, X, T]
      (MvPolynomial.aeval ![eCNineX, eCNineT] R -
        MvPolynomial.aeval ![eCNineCapitalX, eCNineCapitalT] R) =
    MvPolynomial.aeval ![x, t] R - MvPolynomial.aeval ![X, T] R
  rw [map_sub]
  congr 1
  · rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_bind₁]
    congr
    funext i
    fin_cases i
    all_goals simp [eCNineX, eCNineT]
  · rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_bind₁]
    congr
    funext i
    fin_cases i
    all_goals simp [eCNineCapitalX, eCNineCapitalT]

/-- The first defining polynomial is homogeneous of degree three. -/
theorem eCNineFirstPolynomial_isHomogeneous :
    eCNineFirstPolynomial.IsHomogeneous 3 := by
  have hx := MvPolynomial.isHomogeneous_X ℂ (0 : Fin 4)
  have ht := MvPolynomial.isHomogeneous_X ℂ (1 : Fin 4)
  have hX := MvPolynomial.isHomogeneous_X ℂ (2 : Fin 4)
  have hquadratic :
      (eCNineCapitalX ^ 2 +
        MvPolynomial.C 2 * eCNineCapitalX * eCNineX +
        MvPolynomial.C 3 * eCNineX ^ 2).IsHomogeneous 2 := by
    simpa [eCNineX, eCNineCapitalX, Nat.one_mul] using
      ((hX.pow 2).add ((hX.C_mul (2 : ℂ)).mul hx)).add
        ((hx.pow 2).C_mul (3 : ℂ))
  simpa [eCNineFirstPolynomial, eCNineX, eCNineT,
    eCNineCapitalX, Nat.one_mul] using
      (ht.pow 3).C_mul (12 : ℂ) |>.add ((hx.sub hX).mul hquadratic)

/-- The second defining polynomial is homogeneous of degree three. -/
theorem eCNineSecondPolynomial_isHomogeneous :
    eCNineSecondPolynomial.IsHomogeneous 3 := by
  have hx := MvPolynomial.isHomogeneous_X ℂ (0 : Fin 4)
  have hT := MvPolynomial.isHomogeneous_X ℂ (3 : Fin 4)
  have hX := MvPolynomial.isHomogeneous_X ℂ (2 : Fin 4)
  have hquadratic :
      (MvPolynomial.C 3 * eCNineCapitalX ^ 2 +
        MvPolynomial.C 2 * eCNineCapitalX * eCNineX +
        eCNineX ^ 2).IsHomogeneous 2 := by
    simpa [eCNineX, eCNineCapitalX, Nat.one_mul] using
      (((hX.pow 2).C_mul (3 : ℂ)).add
        ((hX.C_mul (2 : ℂ)).mul hx)).add (hx.pow 2)
  simpa [eCNineSecondPolynomial, eCNineX, eCNineCapitalX,
    eCNineCapitalT, Nat.one_mul] using
      (hT.pow 3).C_mul (12 : ℂ) |>.sub ((hx.sub hX).mul hquadratic)

/-- The difference section has the same degree as the binary form. -/
theorem eCNineDifferenceSection_isHomogeneous
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    (eCNineDifferenceSection R).IsHomogeneous N := by
  have hleft :
      (MvPolynomial.aeval ![eCNineX, eCNineT] R).IsHomogeneous N := by
    have hleft := hR.aeval
      ![eCNineX, eCNineT] (fun i ↦ by
        fin_cases i
        all_goals exact MvPolynomial.isHomogeneous_X ℂ _)
    rw [one_mul] at hleft
    exact hleft
  have hright :
      (MvPolynomial.aeval ![eCNineCapitalX, eCNineCapitalT] R).IsHomogeneous N := by
    have hright := hR.aeval
      ![eCNineCapitalX, eCNineCapitalT] (fun i ↦ by
        fin_cases i
        all_goals exact MvPolynomial.isHomogeneous_X ℂ _)
    rw [one_mul] at hright
    exact hright
  exact hleft.sub hright

/-- Evaluation of a homogeneous binary form scales by the degree. -/
theorem eHomogeneousForm_eval_scale
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (a x t : ℂ) :
    MvPolynomial.eval ![a * x, a * t] R =
      a ^ N * MvPolynomial.eval ![x, t] R := by
  induction hR using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      simp only [map_add, ihp, ihq, mul_add]
  | monomial d r hr =>
      simp only [MvPolynomial.eval_monomial]
      rw [show ![a * x, a * t] = fun i ↦ a * ![x, t] i by
        funext i
        fin_cases i <;> rfl]
      simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib]
      rw [Finset.prod_pow_eq_pow_sum]
      have hdegree : ∑ i ∈ d.support, d i = N := by
        simpa [Finsupp.weight_apply, Finsupp.sum] using hr
      rw [hdegree]
      ring

/-- Scaling all four coordinates scales the first C9 equation cubically. -/
theorem eCNineFirstValue_scale
    (a x t X T : ℂ) :
    eCNineFirstValue (a * x) (a * t) (a * X) (a * T) =
      a ^ 3 * eCNineFirstValue x t X T := by
  simp only [eCNineFirstValue]
  ring

/-- Scaling all four coordinates scales the second C9 equation cubically. -/
theorem eCNineSecondValue_scale
    (a x t X T : ℂ) :
    eCNineSecondValue (a * x) (a * t) (a * X) (a * T) =
      a ^ 3 * eCNineSecondValue x t X T := by
  simp only [eCNineSecondValue]
  ring

/-- Scaling all four coordinates scales the difference section by its degree. -/
theorem eCNineDifferenceValue_scale
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (a x t X T : ℂ) :
    eCNineDifferenceValue R (a * x) (a * t) (a * X) (a * T) =
      a ^ N * eCNineDifferenceValue R x t X T := by
  simp only [eCNineDifferenceValue, eHomogeneousForm_eval_scale hR]
  ring

/-- The C9 curve as a subset of projective three space. -/
noncomputable def eCNineProjectiveCurve : Set (ℙ ℂ ECNineAmbient) :=
  {p | Projectivization.lift
    (fun (v : {v : ECNineAmbient // v ≠ 0}) ↦
      ECNineEquations (v.1 0) (v.1 1) (v.1 2) (v.1 3))
    (by
      intro a b scalar hab
      have hscalar : scalar ≠ 0 := by
        intro hzero
        apply a.2
        rw [hab, hzero, zero_smul]
      have hcoordinate (i : Fin 4) : a.1 i = scalar * b.1 i := by
        have hi := congrFun hab i
        simpa [Pi.smul_apply, smul_eq_mul] using hi
      apply propext
      simp only [ECNineEquations]
      simp only [hcoordinate 0, hcoordinate 1, hcoordinate 2, hcoordinate 3,
        eCNineFirstValue_scale, eCNineSecondValue_scale]
      simp [hscalar]) p}

/-- Vanishing of the difference section on projective three space. -/
noncomputable def eCNineProjectiveSectionZero
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    Set (ℙ ℂ ECNineAmbient) :=
  {p | Projectivization.lift
    (fun (v : {v : ECNineAmbient // v ≠ 0}) ↦ eCNineDifferenceValue R
      (v.1 0) (v.1 1) (v.1 2) (v.1 3) = 0)
    (by
      intro a b scalar hab
      have hscalar : scalar ≠ 0 := by
        intro hzero
        apply a.2
        rw [hab, hzero, zero_smul]
      have hcoordinate (i : Fin 4) : a.1 i = scalar * b.1 i := by
        have hi := congrFun hab i
        simpa [Pi.smul_apply, smul_eq_mul] using hi
      apply propext
      simp only [hcoordinate 0, hcoordinate 1, hcoordinate 2, hcoordinate 3,
        eCNineDifferenceValue_scale hR]
      simp [hscalar]) p}

theorem eCNineProjectiveCurve_mk_iff
    (x t X T : ℂ) (hnonzero : ![x, t, X, T] ≠ (0 : ECNineAmbient)) :
    Projectivization.mk ℂ ![x, t, X, T] hnonzero ∈
        eCNineProjectiveCurve ↔
      ECNineEquations x t X T := by
  simp [eCNineProjectiveCurve]

theorem eCNineProjectiveSectionZero_mk_iff
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (x t X T : ℂ) (hnonzero : ![x, t, X, T] ≠ (0 : ECNineAmbient)) :
    Projectivization.mk ℂ ![x, t, X, T] hnonzero ∈
        eCNineProjectiveSectionZero hR ↔
      eCNineDifferenceValue R x t X T = 0 := by
  simp [eCNineProjectiveSectionZero]

/-- The distinguished point `[1:0:1:0]` on the C9 curve. -/
noncomputable def eCNinePZero : ℙ ℂ ECNineAmbient :=
  Projectivization.mk ℂ ![(1 : ℂ), 0, 1, 0] (by
    intro h
    have hzero := congrFun h (0 : Fin 4)
    norm_num at hzero)

theorem eCNinePZero_mem_curve :
    eCNinePZero ∈ eCNineProjectiveCurve := by
  rw [eCNinePZero]
  simp [eCNineProjectiveCurve, ECNineEquations,
    eCNineFirstValue, eCNineSecondValue]

theorem eCNinePZero_mem_section
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    eCNinePZero ∈ eCNineProjectiveSectionZero hR := by
  rw [eCNinePZero]
  simp [eCNineProjectiveSectionZero, eCNineDifferenceValue]

/-- A C9 point whose two first coordinates agree is the distinguished point. -/
theorem eCNine_mk_eq_pZero_of_x_eq_X
    (x t X T : ℂ) (hnonzero : ![x, t, X, T] ≠ (0 : ECNineAmbient))
    (hcurve : Projectivization.mk ℂ ![x, t, X, T] hnonzero ∈
      eCNineProjectiveCurve)
    (hxX : x = X) :
    Projectivization.mk ℂ ![x, t, X, T] hnonzero = eCNinePZero := by
  have hequations :=
    (eCNineProjectiveCurve_mk_iff x t X T hnonzero).mp hcurve
  rw [ECNineEquations, eCNineFirstValue, eCNineSecondValue, hxX] at hequations
  norm_num at hequations
  have ht : t = 0 := hequations.1
  have hT : T = 0 := hequations.2
  have hx : x ≠ 0 := by
    intro hxzero
    apply hnonzero
    funext i
    fin_cases i <;> simp [hxzero, ht, hT, ← hxX]
  rw [eCNinePZero]
  apply (Projectivization.mk_eq_mk_iff' ℂ
    ![x, t, X, T] ![(1 : ℂ), 0, 1, 0] hnonzero _).mpr
  refine ⟨x, ?_⟩
  funext i
  fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, ht, hT, ← hxX]

/-- Away from `[1:0:1:0]`, the two first coordinates of a C9
representative are distinct. -/
theorem eCNine_x_ne_X_of_mk_ne_pZero
    (x t X T : ℂ) (hnonzero : ![x, t, X, T] ≠ (0 : ECNineAmbient))
    (hcurve : Projectivization.mk ℂ ![x, t, X, T] hnonzero ∈
      eCNineProjectiveCurve)
    (hoff : Projectivization.mk ℂ ![x, t, X, T] hnonzero ≠ eCNinePZero) :
    x ≠ X := by
  intro hxX
  exact hoff (eCNine_mk_eq_pZero_of_x_eq_X
    x t X T hnonzero hcurve hxX)

/-- A projective C9 zero of the difference section away from the distinguished
point gives a collision of the three initial coordinates. -/
theorem eCNine_off_pZero_section_zero_gives_initial_collision
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (x t X T : ℂ) (hnonzero : ![x, t, X, T] ≠ (0 : ECNineAmbient))
    (hcurve : Projectivization.mk ℂ ![x, t, X, T] hnonzero ∈
      eCNineProjectiveCurve)
    (hsection : Projectivization.mk ℂ ![x, t, X, T] hnonzero ∈
      eCNineProjectiveSectionZero hR)
    (hoff : Projectivization.mk ℂ ![x, t, X, T] hnonzero ≠ eCNinePZero) :
    (x, t) ≠ (X, T) ∧
      weightedPolynomialMap (eInvariantPolynomialMap R) (x, t) =
        weightedPolynomialMap (eInvariantPolynomialMap R) (X, T) := by
  have hxX : x ≠ X :=
    eCNine_x_ne_X_of_mk_ne_pZero x t X T hnonzero hcurve hoff
  have hequations :=
    (eCNineProjectiveCurve_mk_iff x t X T hnonzero).mp hcurve
  have hfibre := (e_fibre_iff_C9 hxX).mpr hequations
  have hthird : MvPolynomial.eval ![x, t] R =
      MvPolynomial.eval ![X, T] R := by
    exact sub_eq_zero.mp
      ((eCNineProjectiveSectionZero_mk_iff hR x t X T hnonzero).mp
        hsection)
  refine ⟨fun h ↦ hxX (congrArg Prod.fst h), ?_⟩
  funext i
  fin_cases i
  · simpa [eInvariantPolynomialMap_first] using hfibre.1
  · simpa [eInvariantPolynomialMap_second] using hfibre.2
  · exact hthird

end OnLeConjecture.DThree
