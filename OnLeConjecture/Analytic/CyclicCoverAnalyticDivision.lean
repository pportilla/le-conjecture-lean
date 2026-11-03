/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CoordinatePowerFiniteDivision
public import OnLeConjecture.Analytic.CyclicCoverKernel

/-!
# Analytic division and the cyclic-cover kernel

Convergent division by the last coordinate power gives the hypersurface
remainder. Independence of its pulled-back residues identifies the kernel
without an additional analytic-division hypothesis.
-/

public section

open Filter
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic.CyclicCover

/-- The cyclic permutation placing the last coordinate first. -/
@[expose] noncomputable def lastCoordinateFirst (z : Source 3) : Source 3 :=
  ![z 2, z 0, z 1]

/-- The inverse cyclic permutation. -/
@[expose] noncomputable def firstCoordinateLast (z : Source 3) : Source 3 :=
  ![z 1, z 2, z 0]

theorem lastCoordinateFirst_analyticAt : AnalyticAt ℂ lastCoordinateFirst 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2).analyticAt 0
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt 0
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 1).analyticAt 0

theorem firstCoordinateLast_analyticAt : AnalyticAt ℂ firstCoordinateLast 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 1).analyticAt 0
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2).analyticAt 0
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt 0

@[simp]
theorem lastCoordinateFirst_zero : lastCoordinateFirst (0 : Source 3) = 0 := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem firstCoordinateLast_zero : firstCoordinateLast (0 : Source 3) = 0 := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem firstCoordinateLast_lastCoordinateFirst (z : Source 3) :
    firstCoordinateLast (lastCoordinateFirst z) = z := by
  funext i
  fin_cases i <;> rfl

theorem hyperplaneTail_lastCoordinateFirst (z : Source 3) :
    Germ.hyperplaneTail 2 (lastCoordinateFirst z) = projectionFunction z := by
  funext i
  fin_cases i <;> rfl

/-- Convergent analytic division by the hypersurface equation in the
three cover coordinates. -/
theorem exists_analytic_function_cover_division
    (r : ℕ) (hr : 0 < r) (F : Source 3 → ℂ) (hF : AnalyticAt ℂ F 0) :
    ∃ Q : Source 3 → ℂ, ∃ R : Source 2 → Fin r → ℂ,
      AnalyticAt ℂ Q 0 ∧ AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in nhds 0,
        F z = (z 0 * z 1 - z 2 ^ r) * Q z +
          ∑ i : Fin r, R (projectionFunction z) i * z 2 ^ i.1 := by
  let G := F ∘ firstCoordinateLast
  have hG : AnalyticAt ℂ G 0 := AnalyticAt.comp_of_eq hF
    firstCoordinateLast_analyticAt firstCoordinateLast_zero
  let h : Source 2 → ℂ := fun y => y 0 * y 1
  have hh : AnalyticAt ℂ h 0 :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt 0).mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt 0)
  have hhZero : h 0 = 0 := by simp [h]
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel hr
  obtain ⟨Q, R, hQ, hR, hdivision⟩ :
      ∃ Q : Source 3 → ℂ, ∃ R : Source 2 → Fin r → ℂ,
        AnalyticAt ℂ Q 0 ∧ AnalyticAt ℂ R 0 ∧
        ∀ᶠ z in nhds 0,
          G z = (z 0 ^ r - h (Germ.hyperplaneTail 2 z)) * Q z +
            ∑ i : Fin r, z 0 ^ i.1 * R (Germ.hyperplaneTail 2 z) i := by
    have hresult := Germ.exists_analytic_function_coordinatePower_division
      G hG (r - 1) h hh hhZero
    dsimp only [Germ.GeneralCoefficientSpace] at hresult
    rw [hpred] at hresult
    exact hresult
  let Qcover : Source 3 → ℂ := fun z => -Q (lastCoordinateFirst z)
  have hQcover : AnalyticAt ℂ Qcover 0 :=
    (AnalyticAt.comp_of_eq hQ lastCoordinateFirst_analyticAt lastCoordinateFirst_zero).neg
  refine ⟨Qcover, R, hQcover, hR, ?_⟩
  have hpull := lastCoordinateFirst_analyticAt.continuousAt.eventually
    (by simpa only [lastCoordinateFirst_zero] using hdivision)
  filter_upwards [hpull] with z hz
  have hz' : F z = (z 2 ^ r - z 0 * z 1) * Q (lastCoordinateFirst z) +
      ∑ i : Fin r, z 2 ^ i.1 * R (projectionFunction z) i := by
    change G (lastCoordinateFirst z) =
      ((lastCoordinateFirst z) 0 ^ r - h (Germ.hyperplaneTail 2 (lastCoordinateFirst z))) *
        Q (lastCoordinateFirst z) +
          ∑ i : Fin r, (lastCoordinateFirst z) 0 ^ i.1 *
            R (Germ.hyperplaneTail 2 (lastCoordinateFirst z)) i at hz
    dsimp only [G, Function.comp_def] at hz
    rw [firstCoordinateLast_lastCoordinateFirst, hyperplaneTail_lastCoordinateFirst] at hz
    simpa only [lastCoordinateFirst, h, projectionFunction,
      Matrix.cons_val_zero, Matrix.cons_val_one] using hz
  rw [hz']
  congr 1
  · dsimp [Qcover]
    ring
  · apply Finset.sum_congr rfl
    intro i _hi
    ring

/-- Every analytic three-variable germ has a convergent remainder of
degree less than `r` modulo the hypersurface equation. -/
theorem exists_analytic_germ_cover_division (r : ℕ) (hr : 0 < r) (f : Germ 3) :
    ∃ q : Germ 3, ∃ a : Fin r → Germ 2,
      f = relationGerm r * q + ∑ i,
        projectionGerm.pullbackRingHom (a i) * Germ.coordinate (2 : Fin 3) ^ i.1 := by
  obtain ⟨F, hF, hf⟩ := Germ.exists_analyticRepresentative_allOrders f
  obtain ⟨Q, R, hQ, hR, hdivision⟩ := exists_analytic_function_cover_division r hr F hF
  have hRi (i : Fin r) : AnalyticAt ℂ (fun y => R y i) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      AnalyticAt.comp (f := R)
        (g := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i).analyticAt (R 0)) hR
  let q : Germ 3 := Germ.ofFunction Q hQ
  let a : Fin r → Germ 2 := fun i => Germ.ofFunction (fun y => R y i) (hRi i)
  let φ := Filter.Germ.coeRingHom (R := ℂ) (nhds (0 : Source 3))
  let ψ := (analyticGermSubring 3).subtype
  let coordinate : Fin 3 → Source 3 → ℂ := fun i z => z i
  let term : Fin r → Source 3 → ℂ := fun i =>
    (fun z => R (projectionFunction z) i) * coordinate 2 ^ i.1
  let H : Source 3 → ℂ :=
    (coordinate 0 * coordinate 1 - coordinate 2 ^ r) * Q + ∑ i, term i
  have hFG : φ F = φ H := by
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hdivision] with z hz
    simpa only [H, term, coordinate, Pi.add_apply, Pi.mul_apply, Pi.sub_apply,
      Pi.pow_apply, Finset.sum_apply] using hz
  have hprojection (i : Fin r) :
      ψ (projectionGerm.pullbackRingHom (a i)) =
        φ (fun z => R (projectionFunction z) i) := by
    change (Germ.compPointed (Germ.ofFunction (fun y => R y i) (hRi i)) projectionGerm).1 = _
    rw [projectionGerm, Germ.compPointed_ofFunction]
    rfl
  refine ⟨q, a, ?_⟩
  apply Subtype.ext
  rw [hf]
  change φ F = ψ (relationGerm r * q + ∑ i,
    projectionGerm.pullbackRingHom (a i) * Germ.coordinate (2 : Fin 3) ^ i.1)
  rw [hFG]
  simp only [H, term, relationGerm, map_add, map_mul, map_sub, map_pow,
    map_sum, hprojection]
  rfl

/-- The pullback kernel of the cyclic cover is the principal ideal
generated by its hypersurface equation. -/
theorem ker_coverGerm_pullback_eq_span (r : ℕ) (hr : 0 < r) :
    RingHom.ker (coverGerm r hr).pullbackRingHom = Ideal.span {relationGerm r} :=
  ker_coverGerm_pullback_eq_span_of_analytic_division r hr
    (exists_analytic_germ_cover_division r hr)

/-- Equality after cyclic-cover pullback is exactly equality modulo the
hypersurface equation. -/
theorem cover_pullback_eq_iff_sub_mem_span (r : ℕ) (hr : 0 < r) (f g : Germ 3) :
    (coverGerm r hr).pullbackRingHom f = (coverGerm r hr).pullbackRingHom g ↔
      f - g ∈ Ideal.span {relationGerm r} := by
  rw [← ker_coverGerm_pullback_eq_span r hr, RingHom.mem_ker, map_sub, sub_eq_zero]

end OnLeConjecture.Analytic.CyclicCover
