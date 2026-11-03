/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FreeChainCoefficientOrder
public import OnLeConjecture.Analytic.AnalyticPointBasis
import Mathlib.Tactic

/-!
# Straightening a finite chain of free point blowup charts

The explicitly given charts `b_c(x,y)=(y*(x+c),y)` admit compatible
zero-center coordinates. Their composite has first component
`y^h*x + ∑ j<h, c_j*y^(j+1)`. The extra term is removed by an invertible
analytic triangular coordinate change at the root. No assertion that an
arbitrary proximity or resolution chain has this free-chart form is made.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- An analytic triangular shear preserves the second coordinate. -/
@[expose] noncomputable def triangularShear (S : ℂ → ℂ) (z : Source 2) : Source 2 :=
  ![z 0 + S (z 1), z 1]

theorem triangularShear_analyticAt (S : ℂ → ℂ) (hS : AnalyticAt ℂ S 0) :
    AnalyticAt ℂ (triangularShear S) 0 := by
  apply AnalyticAt.pi
  intro i
  have hx := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0
  have hy := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0
  fin_cases i
  · exact hx.add (hS.comp_of_eq hy rfl)
  · exact hy

theorem triangularShear_origin (S : ℂ → ℂ) (hS0 : S 0 = 0) : triangularShear S 0 = 0 := by
  ext i
  fin_cases i <;> simp [triangularShear, hS0]

@[expose] noncomputable def triangularShearGerm
    (S : ℂ → ℂ) (hS : AnalyticAt ℂ S 0) (hS0 : S 0 = 0) : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (triangularShear S) (triangularShear_analyticAt S hS)
    (triangularShear_origin S hS0)

/-- The inverse of the actual triangular shear is the shear by `-S`. -/
@[expose] noncomputable def triangularShearEquiv
    (S : ℂ → ℂ) (hS : AnalyticAt ℂ S 0) (hS0 : S 0 = 0) : PointedEquivGerm 2 where
  forward := triangularShearGerm S hS hS0
  inverse := triangularShearGerm (fun y ↦ -S y) hS.neg (by simp [hS0])
  forward_inverse := by
    have h : triangularShear S ∘ triangularShear (fun y ↦ -S y) = id := by
      funext z
      ext i
      fin_cases i <;> simp [triangularShear]
    simp only [triangularShearGerm, PointedMapGerm.comp_ofFunction, h,
      PointedMapGerm.identity]
  inverse_forward := by
    have h : triangularShear (fun y ↦ -S y) ∘ triangularShear S = id := by
      funext z
      ext i
      fin_cases i <;> simp [triangularShear]
    simp only [triangularShearGerm, PointedMapGerm.comp_ofFunction, h,
      PointedMapGerm.identity]

@[simp] theorem triangularShearGerm_pullback_one
    (S : ℂ → ℂ) (hS : AnalyticAt ℂ S 0) (hS0 : S 0 = 0) :
    (triangularShearGerm S hS hS0).pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinate (1 : Fin 2) := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  exact MapGerm.component_ofFunction (triangularShear S) (triangularShear_analyticAt S hS) 1

/-- The polynomial translation contributed by the first `h` chart centers. -/
@[expose] noncomputable def freeChainShift (c : ℕ → ℂ) (h : ℕ) (y : ℂ) : ℂ :=
  ∑ j ∈ Finset.range h, c j * y ^ (j + 1)

theorem freeChainShift_analyticAt (c : ℕ → ℂ) (h : ℕ) :
    AnalyticAt ℂ (freeChainShift c h) 0 := by
  unfold freeChainShift
  apply Finset.analyticAt_fun_sum
  intro j _hj
  exact analyticAt_const.mul (analyticAt_id.pow (j + 1))

@[simp] theorem freeChainShift_origin (c : ℕ → ℂ) (h : ℕ) : freeChainShift c h 0 = 0 := by
  simp [freeChainShift]

@[simp] theorem freeChainShift_zero (c : ℕ → ℂ) : freeChainShift c 0 = 0 := by
  funext y
  simp [freeChainShift]

theorem freeChainShift_succ (c : ℕ → ℂ) (h : ℕ) (y : ℂ) :
    freeChainShift c (h + 1) y = freeChainShift c h y + c h * y ^ (h + 1) := by
  exact Finset.sum_range_succ _ h

@[expose] noncomputable def freeChainStraighteningEquiv (c : ℕ → ℂ) (h : ℕ) :
    PointedEquivGerm 2 :=
  triangularShearEquiv (freeChainShift c h) (freeChainShift_analyticAt c h)
    (freeChainShift_origin c h)

/-- The actual successive composite, appending the `h`th chart on the
right, in the order in which it is applied to the original germ. -/
@[expose] noncomputable def freeChartChain (c : ℕ → ℂ) : ℕ → PointedMapGerm 2 2
  | 0 => PointedMapGerm.identity 2
  | h + 1 => (freeChartChain c h).comp (pointBlowupChartGerm (c h))

/-- The closed expression for the map represented by the successive
chart composite. -/
@[expose] noncomputable def freeChartChainExpression
    (c : ℕ → ℂ) (h : ℕ) : Source 2 → Source 2 :=
  triangularShear (freeChainShift c h) ∘ freeChainChart h

theorem freeChartChainExpression_apply (c : ℕ → ℂ) (h : ℕ) (z : Source 2) :
    freeChartChainExpression c h z =
      ![z 1 ^ h * z 0 + ∑ j ∈ Finset.range h, c j * z 1 ^ (j + 1), z 1] := rfl

private theorem freeChartChainExpression_succ (c : ℕ → ℂ) (h : ℕ) :
    freeChartChainExpression c (h + 1) =
      freeChartChainExpression c h ∘ pointBlowupChart (c h) := by
  funext z
  ext i
  fin_cases i
  · change z 1 ^ (h + 1) * z 0 + freeChainShift c (h + 1) (z 1) =
      z 1 ^ h * (z 1 * (z 0 + c h)) + freeChainShift c h (z 1)
    rw [freeChainShift_succ, pow_succ]
    ring
  · rfl

/-- A polynomial triangular source equivalence straightens the whole
finite free chart chain. This is an equality of actual analytic map germs. -/
theorem freeChartChain_eq_straightening_comp (c : ℕ → ℂ) (h : ℕ) :
    freeChartChain c h =
      (freeChainStraighteningEquiv c h).forward.comp (freeChainChartGerm h) := by
  induction h with
  | zero =>
      simp only [freeChartChain, freeChainChartGerm_zero, PointedMapGerm.comp_identity,
        freeChainStraighteningEquiv, triangularShearEquiv, freeChainShift_zero]
      have heq : triangularShear (0 : ℂ → ℂ) = id := by
        funext z
        ext i
        fin_cases i <;> simp [triangularShear]
      simp only [triangularShearGerm, heq, PointedMapGerm.identity]
  | succ h ih =>
      rw [freeChartChain, ih]
      simp only [freeChainStraighteningEquiv, triangularShearEquiv,
        triangularShearGerm, freeChainChartGerm, pointBlowupChartGerm,
        PointedMapGerm.comp_ofFunction]
      have heq := freeChartChainExpression_succ c h
      change triangularShear (freeChainShift c (h + 1)) ∘ freeChainChart (h + 1) =
        (triangularShear (freeChainShift c h) ∘ freeChainChart h) ∘ pointBlowupChart (c h)
        at heq
      simp only [heq]

theorem freeChartChainExpression_analyticAt (c : ℕ → ℂ) (h : ℕ) :
    AnalyticAt ℂ (freeChartChainExpression c h) 0 :=
  (triangularShear_analyticAt _ (freeChainShift_analyticAt c h)).comp_of_eq
    (freeChainChart_analyticAt h) (freeChainChart_origin h)

theorem freeChartChainExpression_origin (c : ℕ → ℂ) (h : ℕ) :
    freeChartChainExpression c h 0 = 0 := by
  simp only [freeChartChainExpression, Function.comp_apply, freeChainChart_origin]
  exact triangularShear_origin _ (freeChainShift_origin c h)

/-- The successive analytic map composite is represented by the displayed
closed polynomial formula, not merely by matching coordinate orders. -/
theorem freeChartChain_eq_expression (c : ℕ → ℂ) (h : ℕ) :
    freeChartChain c h = PointedMapGerm.ofFunction (freeChartChainExpression c h)
      (freeChartChainExpression_analyticAt c h) (freeChartChainExpression_origin c h) := by
  rw [freeChartChain_eq_straightening_comp]
  simp only [freeChainStraighteningEquiv, triangularShearEquiv, triangularShearGerm,
    freeChainChartGerm, PointedMapGerm.comp_ofFunction, freeChartChainExpression]

/-- Pulling the original germ back along the chart chain is the same as
pulling its root coordinate transform back through `h` zero-center charts. -/
theorem freeChartChain_pullback_straightened (c : ℕ → ℂ) (h : ℕ) (f : Germ 2) :
    (freeChartChain c h).pullbackRingHom f =
      (freeChainChartGerm h).pullbackRingHom
        ((freeChainStraighteningEquiv c h).forward.pullbackRingHom f) := by
  rw [freeChartChain_eq_straightening_comp, PointedMapGerm.pullbackRingHom_comp]
  rfl

@[simp] theorem freeChainStraighteningEquiv_zero_forward (c : ℕ → ℂ) :
    (freeChainStraighteningEquiv c 0).forward = PointedMapGerm.identity 2 := by
  simpa only [freeChartChain, freeChainChartGerm_zero, PointedMapGerm.comp_identity]
    using (freeChartChain_eq_straightening_comp c 0).symm

/-- The remaining chart-center polynomial at the `j`th center. -/
@[expose] noncomputable def freeChainTailEquiv (c : ℕ → ℂ) (h j : ℕ) :
    PointedEquivGerm 2 :=
  freeChainStraighteningEquiv (fun t ↦ c (j + t)) (h - j)

@[simp] theorem freeChainTailEquiv_zero (c : ℕ → ℂ) (h : ℕ) :
    freeChainTailEquiv c h 0 = freeChainStraighteningEquiv c h := by
  simp only [freeChainTailEquiv, Nat.zero_add, Nat.sub_zero]

@[simp] theorem freeChainTailEquiv_final_forward (c : ℕ → ℂ) (h : ℕ) :
    (freeChainTailEquiv c h h).forward = PointedMapGerm.identity 2 := by
  simp only [freeChainTailEquiv, Nat.sub_self, freeChainStraighteningEquiv_zero_forward]

private theorem freeChainShift_tail (c : ℕ → ℂ) (h j : ℕ) (hj : j < h) (y : ℂ) :
    freeChainShift (fun t ↦ c (j + t)) (h - j) y =
      y * freeChainShift (fun t ↦ c (j + 1 + t)) (h - (j + 1)) y + c j * y := by
  have hexponent : h - j = (h - (j + 1)) + 1 := by omega
  rw [hexponent, freeChainShift, Finset.sum_range_succ']
  simp only [Nat.add_zero, Nat.zero_add, pow_one]
  congr 1
  rw [freeChainShift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [show j + (t + 1) = j + 1 + t by omega, pow_succ]
  ring

/-- The remaining polynomial shears turn each specified free-chart edge
into an actual zero-center chart edge. -/
theorem freeChainTailEquiv_chart_identity (c : ℕ → ℂ) (h j : ℕ) (hj : j < h) :
    (freeChainTailEquiv c h j).forward.comp (pointBlowupChartGerm 0) =
      (pointBlowupChartGerm (c j)).comp (freeChainTailEquiv c h (j + 1)).forward := by
  have heq :
      triangularShear (freeChainShift (fun t ↦ c (j + t)) (h - j)) ∘ pointBlowupChart 0 =
        pointBlowupChart (c j) ∘
          triangularShear (freeChainShift (fun t ↦ c (j + 1 + t)) (h - (j + 1))) := by
    funext z
    ext i
    fin_cases i
    · change z 1 * (z 0 + 0) + freeChainShift (fun t ↦ c (j + t)) (h - j) (z 1) =
        z 1 * (z 0 + freeChainShift (fun t ↦ c (j + 1 + t)) (h - (j + 1)) (z 1) + c j)
      rw [freeChainShift_tail c h j hj]
      ring
    · rfl
  simp only [freeChainTailEquiv, freeChainStraighteningEquiv, triangularShearEquiv,
    triangularShearGerm, pointBlowupChartGerm, PointedMapGerm.comp_ofFunction, heq]

/-- The germ at each center after its remaining-tail coordinate shear. -/
@[expose] noncomputable def straightenedFreeChain
    (c : ℕ → ℂ) (h : ℕ) (f : ℕ → Germ 2) (j : ℕ) : Germ 2 :=
  (freeChainTailEquiv c h j).forward.pullbackRingHom (f j)

@[simp] theorem straightenedFreeChain_root (c : ℕ → ℂ) (h : ℕ) (f : ℕ → Germ 2) :
    straightenedFreeChain c h f 0 =
      (freeChainStraighteningEquiv c h).forward.pullbackRingHom (f 0) := by
  simp only [straightenedFreeChain, freeChainTailEquiv_zero]

@[simp] theorem straightenedFreeChain_final (c : ℕ → ℂ) (h : ℕ) (f : ℕ → Germ 2) :
    straightenedFreeChain c h f h = f h := by
  simp only [straightenedFreeChain, freeChainTailEquiv_final_forward,
    PointedMapGerm.pullbackRingHom_identity, RingHom.id_apply]

/-- Every ordinary order condition is preserved at every center. -/
theorem straightenedFreeChain_mem_pow_iff
    (c : ℕ → ℂ) (h : ℕ) (f : ℕ → Germ 2) (j k : ℕ) :
    straightenedFreeChain c h f j ∈ maximalIdeal 2 ^ k ↔ f j ∈ maximalIdeal 2 ^ k :=
  (freeChainTailEquiv c h j).pullback_mem_maximalIdeal_pow_iff (f j)

/-- An actual free-chart transform identity becomes an actual zero-center
identity. The order being factored can vary from edge to edge. -/
theorem straightenedFreeChain_step
    (c : ℕ → ℂ) (h : ℕ) (f : ℕ → Germ 2) (j m : ℕ) (hj : j < h)
    (hstep : (pointBlowupChartGerm (c j)).pullbackRingHom (f j) =
      coordinate (1 : Fin 2) ^ m * f (j + 1)) :
    (pointBlowupChartGerm 0).pullbackRingHom (straightenedFreeChain c h f j) =
      coordinate (1 : Fin 2) ^ m * straightenedFreeChain c h f (j + 1) := by
  unfold straightenedFreeChain
  rw [← RingHom.comp_apply, ← PointedMapGerm.pullbackRingHom_comp,
    freeChainTailEquiv_chart_identity c h j hj, PointedMapGerm.pullbackRingHom_comp,
    RingHom.comp_apply, hstep, map_mul, map_pow]
  have hy : (freeChainTailEquiv c h (j + 1)).forward.pullbackRingHom
      (coordinate (1 : Fin 2)) = coordinate (1 : Fin 2) :=
    triangularShearGerm_pullback_one _ (freeChainShift_analyticAt _ _)
      (freeChainShift_origin _ _)
  rw [hy]

/-- The coefficient-order theorem now applies to any specified free chart
chain once the root is prepared in the proved straightening coordinates.
No compatibility of zero-center coordinates is assumed separately. -/
theorem coefficient_mem_pow_of_straightened_prepared_freeChain
    (c : ℕ → ℂ) (h m : ℕ) (P : Polynomial (Germ 1)) (f : ℕ → Germ 2)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : (freeChainStraighteningEquiv c h).forward.pullbackRingHom (f 0) =
      firstCoordinatePolynomialEvaluation P * u)
    (hsteps : ∀ j < h, (pointBlowupChartGerm (c j)).pullbackRingHom (f j) =
      coordinate (1 : Fin 2) ^ m * f (j + 1))
    (hfinal : f h ∈ maximalIdeal 2 ^ m) (i : ℕ) (hi : i ≤ m) :
    P.coeff i ∈ maximalIdeal 1 ^ ((h + 1) * (m - i)) := by
  apply coefficient_mem_pow_of_prepared_freeChain h m P
    (straightenedFreeChain c h f) u hu
  · simpa only [straightenedFreeChain_root] using hprepared
  · intro j hj
    exact straightenedFreeChain_step c h f j m hj (hsteps j hj)
  · simpa only [straightenedFreeChain_final] using hfinal
  · exact hi

end Germ

end OnLeConjecture.Analytic
