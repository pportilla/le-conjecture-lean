/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPlaneImplicitBranch
public import OnLeConjecture.Analytic.ImplicitDefectFactorization
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# The centered cyclic equation and its first derivative

Centering the unknown at a root of unity makes the analytic branch
pointed. The derivative calculation identifies the unit in its implicit
defect factorization.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

@[expose] noncomputable def cyclicCenteredEquation
    (k p : ℕ) (β : ℂ → ℂ) (ζ : ℂ) (q : Source 2) : ℂ :=
  β (q 1 ^ p) - (ζ + q 0) ^ k * β (q 1 ^ p * (ζ + q 0))

theorem cyclicCenteredEquation_analyticAt
    (k p : ℕ) (hp : 0 < p) (β : ℂ → ℂ)
    (hβ : AnalyticAt ℂ β 0) (ζ : ℂ) :
    AnalyticAt ℂ (cyclicCenteredEquation k p β ζ) 0 := by
  have hx : AnalyticAt ℂ (fun q : Source 2 => q 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt 0
  have hy : AnalyticAt ℂ (fun q : Source 2 => q 1) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt 0
  have hz : AnalyticAt ℂ (fun q : Source 2 => ζ + q 0) 0 :=
    analyticAt_const.add hx
  have hb1 : AnalyticAt ℂ (fun q : Source 2 => β (q 1 ^ p)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 2)) _ (hy.pow p)
    simpa only [Pi.pow_apply, Pi.zero_apply, zero_pow hp.ne'] using hβ
  have hb2 : AnalyticAt ℂ (fun q : Source 2 => β (q 1 ^ p * (ζ + q 0))) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 2)) _ ((hy.pow p).mul hz)
    simpa only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply, zero_pow hp.ne', zero_mul] using hβ
  exact hb1.sub ((hz.pow k).mul hb2)

theorem cyclicCenteredEquation_first_derivative
    (k p : ℕ) (hp : 0 < p) (β : ℂ → ℂ)
    (hβ : AnalyticAt ℂ β 0) (ζ : ℂ) :
    fderiv ℂ (cyclicCenteredEquation k p β ζ) 0 (firstCoordinateVector 1) =
      -((k : ℂ) * ζ ^ (k - 1) * β 0) := by
  let ι : ℂ →L[ℂ] Source 2 :=
    ContinuousLinearMap.pi ![ContinuousLinearMap.id ℂ ℂ, 0]
  have hfun : (fun t : ℂ => cyclicCenteredEquation k p β ζ (ι t)) =
      (fun t : ℂ => β 0 - (ζ + t) ^ k * β 0) := by
    funext t
    simp [cyclicCenteredEquation, ι, zero_pow hp.ne']
  have hscalar : HasDerivAt
      (fun t : ℂ => cyclicCenteredEquation k p β ζ (ι t))
      (-((k : ℂ) * ζ ^ (k - 1) * β 0)) 0 := by
    rw [hfun]
    simpa only [id_eq, Pi.pow_apply, add_zero, mul_one] using
      ((((hasDerivAt_id (0 : ℂ)).const_add ζ).pow k).mul_const (β 0)).const_sub (β 0)
  have hF : HasStrictFDerivAt (cyclicCenteredEquation k p β ζ)
      (fderiv ℂ (cyclicCenteredEquation k p β ζ) 0) (ι 0) := by
    simpa only [map_zero] using
      (cyclicCenteredEquation_analyticAt k p hp β hβ ζ).hasStrictFDerivAt
  have hcomp := hF.comp 0 ι.hasStrictFDerivAt
  have heq := hcomp.hasFDerivAt.unique hscalar.hasFDerivAt
  have h := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) heq
  have hi : ι 1 = firstCoordinateVector 1 := by
    ext i
    fin_cases i <;> simp [ι, firstCoordinateVector]
  simpa only [ContinuousLinearMap.comp_apply, hi,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using h

/-- The centered equation as an actual analytic germ. -/
@[expose] noncomputable def cyclicCenteredEquationGerm
    (k p : ℕ) (hp : 0 < p) (β : ℂ → ℂ)
    (hβ : AnalyticAt ℂ β 0) (ζ : ℂ) : Germ 2 :=
  ofFunction (cyclicCenteredEquation k p β ζ)
    (cyclicCenteredEquation_analyticAt k p hp β hβ ζ)

/-- The defect of the power of the implicit unknown is a unit multiple of
the parameter-axis defect. The value of that unit is exactly `-1 / β(0)`.
This includes the identically zero defect. -/
theorem cyclicCenteredEquation_power_defect_unit
    {n : ℕ} (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (ζ : ℂ) (hζ : ζ ^ k = 1) (φ : PointedMapGerm n 2)
    (hsolution : φ.pullbackRingHom (cyclicCenteredEquationGerm k p hp β hβ ζ) = 0) :
    ∃ ε : Germ n, IsUnit ε ∧
      1 - (constRingHom n ζ + φ.pullbackRingHom (coordinate (0 : Fin 2))) ^ k =
        φ.pullbackRingHom (hyperplaneExtension 1
          (hyperplaneRestriction 1 (cyclicCenteredEquationGerm k p hp β hβ ζ))) * ε ∧
      valueRingHom n ε = -1 / β 0 := by
  have hζ0 : ζ ≠ 0 := by
    intro hz
    simp [hz, zero_pow hk.ne'] at hζ
  let b : ℂ := (k : ℂ) * ζ ^ (k - 1)
  have hb : b ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hk.ne') (pow_ne_zero _ hζ0)
  let F := cyclicCenteredEquationGerm k p hp β hβ ζ
  have hderiv : differential F (firstCoordinateVector 1) = -(b * β 0) :=
    cyclicCenteredEquation_first_derivative k p hp β hβ ζ
  have hregular : differential F (firstCoordinateVector 1) ≠ 0 := by
    rw [hderiv]
    exact neg_ne_zero.mpr (mul_ne_zero hb hc)
  obtain ⟨u, hu, hfactor, hvalue⟩ := exists_implicit_defect_unit F hregular φ hsolution
  rw [hderiv, neg_neg] at hvalue
  let z : Germ n := constRingHom n ζ + φ.pullbackRingHom (coordinate (0 : Fin 2))
  let B : Germ n := ∑ i ∈ Finset.range k,
    constRingHom n ζ ^ i * z ^ (k - 1 - i)
  have hzvalue : valueRingHom n z = ζ := by
    dsimp only [z]
    rw [map_add, PointedMapGerm.valueRingHom_pullback]
    simp
  have hBvalue : valueRingHom n B = b := by
    dsimp only [B]
    rw [map_sum]
    calc
      _ = ∑ _i ∈ Finset.range k, ζ ^ (k - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [map_mul, map_pow, valueRingHom_const, hzvalue]
        rw [← pow_add, show i + (k - 1 - i) = k - 1 by
          have := Finset.mem_range.mp hi
          omega]
      _ = b := by simp [b]
  have hB : IsUnit B := isUnit_of_valueRingHom_ne_zero (hBvalue ▸ hb)
  obtain ⟨v, hv⟩ := hu
  subst u
  let ε : Germ n := -B * (↑(v⁻¹) : Germ n)
  refine ⟨ε, hB.neg.mul (v⁻¹).isUnit, ?_, ?_⟩
  · have hgeom : (constRingHom n ζ - z) * B = 1 - z ^ k := by
      have h := (Commute.all (constRingHom n ζ) z).mul_geom_sum₂ k
      simpa only [B, ← map_pow, hζ, map_one] using h
    change 1 - z ^ k = _ * ε
    rw [← hgeom, hfactor]
    dsimp only [ε, z]
    have hinv : (↑v : Germ n) * (↑(v⁻¹) : Germ n) = 1 := v.mul_inv
    calc
      _ = -(φ.pullbackRingHom (coordinate (0 : Fin 2)) * B) := by ring
      _ = -(φ.pullbackRingHom (coordinate (0 : Fin 2)) * B) *
          ((↑v : Germ n) * (↑(v⁻¹) : Germ n)) := by rw [hinv, mul_one]
      _ = _ := by ring
  · have hinv : valueRingHom n (↑(v⁻¹) : Germ n) * (b * β 0) = 1 := by
      rw [← hvalue, ← map_mul, v.inv_mul, map_one]
    simp only [ε, map_mul, map_neg, hBvalue]
    apply (eq_div_iff hc).mpr
    calc
      -b * valueRingHom n (↑(v⁻¹) : Germ n) * β 0 =
          -(valueRingHom n (↑(v⁻¹) : Germ n) * (b * β 0)) := by ring
      _ = -1 := by rw [hinv]

end OnLeConjecture.DTwo
