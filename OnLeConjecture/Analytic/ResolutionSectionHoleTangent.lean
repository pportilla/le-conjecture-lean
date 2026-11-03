/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionHoleCharts

/-! # Positive-ray agreement with the clockwise source circle

The real-axis tangent of the hole chart is a positive real multiple of
the derivative of the retained holomorphic parametrization in the
clockwise circle direction. This identifies the orientation as a tangent
vector statement, before any global boundary-component identification.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff ComplexConjugate

namespace OnLeConjecture.Analytic

/-- A vector tangent to a complex coordinate circle with negative angular
sign lies on its clockwise tangent ray. -/
theorem exists_pos_smul_clockwise_of_angular_negative {u v : ℂ} (hu : u ≠ 0)
    (hre : (conj u * v).re = 0) (him : (conj u * v).im < 0) :
    ∃ a : ℝ, 0 < a ∧ v = a • (-Complex.I * u) := by
  let a := -(conj u * v).im / Complex.normSq u
  have hn : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have ha : 0 < a := div_pos (neg_pos.mpr him) hn
  have hb : conj u * v = ((conj u * v).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  refine ⟨a, ha, ?_⟩
  apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hu)
  rw [hb]
  have hnC : conj u * u = (Complex.normSq u : ℂ) := Complex.normSq_eq_conj_mul_self.symm
  have hnC0 : (Complex.normSq u : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [Complex.real_smul]
  calc
    (((conj u * v).im : ℂ) * Complex.I) =
        (-(a : ℂ) * (Complex.normSq u : ℂ)) * Complex.I := by
      congr 1
      simp only [a, Complex.ofReal_div, Complex.ofReal_neg]
      field_simp [hnC0]
    _ = conj u * ((a : ℂ) * (-Complex.I * u)) := by
      rw [show conj u * ((a : ℂ) * (-Complex.I * u)) =
        (-(a : ℂ) * (conj u * u)) * Complex.I by ring, hnC]

namespace PlaneLevelCoordinateDisk

variable {f : CollarPlane → ℂ} {s : ℂ} {z : CollarPlane}

/-- The oriented hole-chart tangent agrees with the clockwise derivative
of the SAME disk parametrization, by a strictly positive factor. -/
theorem holeChart_tangent_eq_pos_clockwise (D : PlaneLevelCoordinateDisk f s z)
    {u : ℂ} (hu : u ∈ D.W) (hu0 : u ≠ 0)
    (hf : AnalyticAt ℂ f (D.ψ u)) (hfn : fderiv ℂ f (D.ψ u) ≠ 0)
    {O : Set CollarPlane} (C : SectionRadiusBoundaryChart f D.holeRadius O (D.ψ u)) :
    ∃ a : ℝ, 0 < a ∧
      fderiv ℝ C.φ 0 1 = a • fderiv ℂ D.ψ u (-Complex.I * u) := by
  obtain ⟨hk, hre, him⟩ := D.holeRadius_chart_tangent C hf.differentiableAt
  rw [D.left_inverse _ hu] at hre him
  obtain ⟨a, ha, he⟩ := exists_pos_smul_clockwise_of_angular_negative hu0 hre him
  refine ⟨a, ha, ?_⟩
  apply D.coordinate_prod_fderiv_injective hu hf.differentiableAt hfn
  apply Prod.ext
  · change D.coordinate (fderiv ℝ C.φ 0 1) =
      D.coordinate (a • fderiv ℂ D.ψ u (-Complex.I * u))
    have hm : D.coordinate (a • fderiv ℂ D.ψ u (-Complex.I * u)) =
        a • D.coordinate (fderiv ℂ D.ψ u (-Complex.I * u)) :=
      (D.coordinate.restrictScalars ℝ).map_smul a _
    rw [hm, D.coordinate_fderiv hu]
    exact he
  · change fderiv ℂ f (D.ψ u) (fderiv ℝ C.φ 0 1) =
      fderiv ℂ f (D.ψ u) (a • fderiv ℂ D.ψ u (-Complex.I * u))
    have hm : fderiv ℂ f (D.ψ u) (a • fderiv ℂ D.ψ u (-Complex.I * u)) =
        a • fderiv ℂ f (D.ψ u) (fderiv ℂ D.ψ u (-Complex.I * u)) :=
      ((fderiv ℂ f (D.ψ u)).restrictScalars ℝ).map_smul a _
    rw [hk, hm, D.level_fderiv hu hf.differentiableAt, smul_zero]

end PlaneLevelCoordinateDisk
end OnLeConjecture.Analytic
