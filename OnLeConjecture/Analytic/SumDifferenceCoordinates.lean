/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Inverse
public import OnLeConjecture.Analytic.Coordinates
public import OnLeConjecture.Analytic.CoordinateAxesFactorization
import Mathlib.Tactic

/-!
# Analytic sum-and-difference coordinates with a higher-order correction

The functions `s-S`, `s+S+h`, and `lambda` are analytic coordinates whenever
`h` has zero first jet. The proof constructs the coordinate equivalence
using the analytic inverse function theorem.
-/

public section

namespace OnLeConjecture.Analytic

/-- The coordinate expression before applying the inverse function theorem. -/
@[expose] noncomputable def sumDifferenceFunction
    (H : Source 3 → ℂ) (z : Source 3) : Source 3 :=
  ![z 0 - z 1, z 0 + z 1 + H z, z 2]

theorem sumDifferenceFunction_analyticAt (H : Source 3 → ℂ)
    (hH : AnalyticAt ℂ H 0) : AnalyticAt ℂ (sumDifferenceFunction H) 0 := by
  apply AnalyticAt.pi
  intro i
  have hp (j : Fin 3) : AnalyticAt ℂ (fun z : Source 3 => z j) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j).analyticAt 0
  fin_cases i
  · exact (hp 0).sub (hp 1)
  · exact ((hp 0).add (hp 1)).add hH
  · exact hp 2

theorem sumDifferenceFunction_zero (H : Source 3 → ℂ) (hH : H 0 = 0) :
    sumDifferenceFunction H (0 : Source 3) = 0 := by
  ext i
  fin_cases i <;> simp [sumDifferenceFunction, hH]

/-- A zero first jet suffices for the actual analytic coordinate change. -/
theorem exists_sumDifference_equiv_of_zero_first_jet
    (H : Source 3 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hdH : fderiv ℂ H 0 = 0) :
    ∃ e : PointedEquivGerm 3,
      e.forward = PointedMapGerm.ofFunction (sumDifferenceFunction H)
        (sumDifferenceFunction_analyticAt H hH) (sumDifferenceFunction_zero H hH0) := by
  let proj (i : Fin 3) : Source 3 →L[ℂ] ℂ := ContinuousLinearMap.proj i
  let L : Source 3 →L[ℂ] Source 3 :=
    ContinuousLinearMap.pi ![proj 0 - proj 1, proj 0 + proj 1, proj 2]
  have hderiv : HasFDerivAt (sumDifferenceFunction H) L 0 := by
    have hproj (j : Fin 3) : HasFDerivAt (fun z : Source 3 => z j) (proj j) 0 := by
      have heq : (fun z : Source 3 => z j) = (proj j : Source 3 → ℂ) := by
        ext z
        rfl
      rw [heq]
      exact (proj j).hasFDerivAt
    apply hasFDerivAt_pi.mpr
    intro i
    have hHz : HasFDerivAt H (0 : Source 3 →L[ℂ] ℂ) 0 := by
      simpa only [hdH] using hH.hasStrictFDerivAt.hasFDerivAt
    fin_cases i
    · simpa [sumDifferenceFunction, L, Pi.sub_def] using (hproj 0).sub (hproj 1)
    · simpa [sumDifferenceFunction, L, Pi.add_def] using
        ((hproj 0).add (hproj 1)).add hHz
    · simpa [sumDifferenceFunction, L] using hproj 2
  apply PointedMapGerm.exists_pointedEquivGerm_of_differential_bijective
  change Function.Bijective (fderiv ℂ (sumDifferenceFunction H) 0)
  rw [hderiv.fderiv]
  have hL (z : Source 3) : L z = ![z 0 - z 1, z 0 + z 1, z 2] := by
    ext i
    fin_cases i <;> simp [L, proj]
  constructor
  · intro z w h
    rw [hL, hL] at h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    change z 0 - z 1 = w 0 - w 1 at h0
    change z 0 + z 1 = w 0 + w 1 at h1
    change z 2 = w 2 at h2
    ext i
    fin_cases i
    · change z 0 = w 0
      linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1
    · change z 1 = w 1
      linear_combination -(1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1
    · exact h2
  · intro w
    refine ⟨![(w 0 + w 1) / 2, (w 1 - w 0) / 2, w 2], ?_⟩
    rw [hL]
    ext i
    fin_cases i <;> simp <;> ring

namespace Germ

/-- The coordinate change for an arbitrary analytic correction of order
at least two, with its pullbacks specified as actual analytic germs. -/
theorem exists_sumDifference_equiv_of_mem_maximalIdeal_sq
    (h : Germ 3) (hh : h ∈ maximalIdeal 3 ^ 2) :
    ∃ e : PointedEquivGerm 3,
      e.forward.pullbackRingHom (coordinate (0 : Fin 3)) = coordinate 0 - coordinate 1 ∧
      e.forward.pullbackRingHom (coordinate (1 : Fin 3)) = coordinate 0 + coordinate 1 + h ∧
      e.forward.pullbackRingHom (coordinate (2 : Fin 3)) = coordinate 2 := by
  obtain ⟨H, hH, hrep⟩ := exists_analytic_representative h
  have hjet := mem_firstOrderIdeal_iff.mp (maximalIdeal_sq_le_firstOrderIdeal 3 hh)
  have hH0 : H 0 = 0 := by simpa only [hrep, valueRingHom_ofFunction] using hjet.1
  have hdH : fderiv ℂ H 0 = 0 := by simpa only [hrep, differential_ofFunction] using hjet.2
  obtain ⟨e, he⟩ := exists_sumDifference_equiv_of_zero_first_jet H hH hH0 hdH
  refine ⟨e, ?_, ?_, ?_⟩
  all_goals
    rw [he, PointedMapGerm.pullback_coordinate]
    apply Subtype.ext
    simp only [PointedMapGerm.ofFunction, MapGerm.component_ofFunction,
      hrep, coe_coordinate]
    rfl

end Germ

end OnLeConjecture.Analytic
