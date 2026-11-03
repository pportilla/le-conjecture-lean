/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IntegralDerivationZero
public import OnLeConjecture.Analytic.FiniteParametricMorse
public import OnLeConjecture.Analytic.PlaneFiniteFiberCriterion
public import OnLeConjecture.Analytic.GenericReducedPencil

/-!
# Nonvanishing of the Jacobian of a finite plane map

The analytic chain rule makes a vector field that kills the components into
a derivation over the image ring. Finiteness and characteristic zero force
that derivation to vanish.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace PointedMapGerm

theorem vectorField_eq_zero_of_isFiniteAtOrigin
    (F : PointedMapGerm 2 2) (hfinite : F.IsFiniteAtOrigin)
    (a b : Germ 2)
    (hcomponents : ∀ j : Fin 2,
      a * partialDerivative 0 (F.1.component j) +
        b * partialDerivative 1 (F.1.component j) = 0) :
    a = 0 ∧ b = 0 := by
  let D : Derivation ℂ (Germ 2) (Germ 2) :=
    a • partialDerivation 0 + b • partialDerivation 1
  have hD (z : Germ 2) : D z =
      a * partialDerivative 0 z + b * partialDerivative 1 z := rfl
  have hpull (q : Germ 2) : D (F.pullbackRingHom q) = 0 := by
    rw [hD, pullbackRingHom_apply, partialDerivative_compPointed_sum,
      partialDerivative_compPointed_sum, Fin.sum_univ_two, Fin.sum_univ_two]
    calc
      _ = Germ.compPointed (partialDerivative 0 q) F *
          (a * partialDerivative 0 (F.1.component 0) +
            b * partialDerivative 1 (F.1.component 0)) +
          Germ.compPointed (partialDerivative 1 q) F *
          (a * partialDerivative 0 (F.1.component 1) +
            b * partialDerivative 1 (F.1.component 1)) := by ring
      _ = 0 := by rw [hcomponents 0, hcomponents 1]; ring
  have himage (q : F.ImageRing) : D (q : Germ 2) = 0 := by
    obtain ⟨Q, rfl⟩ := F.pullbackToImageRing_surjective q
    exact hpull Q
  let L : Germ 2 →ₗ[F.ImageRing] Germ 2 :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun r z => by
        change D ((r : Germ 2) * z) = (r : Germ 2) * D z
        rw [D.leibniz, himage, smul_zero, add_zero, smul_eq_mul] }
  let E : Derivation F.ImageRing (Germ 2) (Germ 2) :=
    Derivation.mk' L (fun z w => D.leibniz z w)
  let : Module.Finite F.ImageRing (Germ 2) := hfinite
  let : CharZero F.ImageRing := ⟨fun n m h => by
    have h' := congrArg F.imageValueRingHom h
    simp only [map_natCast] at h'
    exact Nat.cast_injective (R := ℂ) h'⟩
  have hE : E = 0 := OnLeConjecture.Algebra.derivation_eq_zero_of_finite
    (fun n hn => F.image_isUnit_of_value_ne_zero (by
      rw [map_natCast]
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))) E
  have hzero (z : Germ 2) : D z = 0 := by
    have hz := congrArg (fun T : Derivation F.ImageRing (Germ 2) (Germ 2) => T z) hE
    exact hz
  constructor
  · simpa [hD, partialDerivative_coordinate_ne] using hzero (coordinate (0 : Fin 2))
  · simpa [hD, partialDerivative_coordinate_ne] using hzero (coordinate (1 : Fin 2))

theorem jacobian_ne_zero_of_isFiniteAtOrigin
    (F : PointedMapGerm 2 2) (hfinite : F.IsFiniteAtOrigin) :
    jacobian (F.1.component 0) (F.1.component 1) ≠ 0 := by
  intro hJ
  have hpartials : ∀ i : Fin 2,
      partialDerivative 0 (F.1.component i) = 0 ∧
        partialDerivative 1 (F.1.component i) = 0 := by
    intro i
    have h := F.vectorField_eq_zero_of_isFiniteAtOrigin hfinite
      (-partialDerivative 1 (F.1.component i))
      (partialDerivative 0 (F.1.component i)) (by
        intro j
        have hij : jacobian (F.1.component i) (F.1.component j) = 0 := by
          fin_cases i <;> fin_cases j
          · exact jacobian_self _
          · exact hJ
          · change jacobian (F.1.component 1) (F.1.component 0) = 0
            rw [jacobian_swap, hJ, neg_zero]
          · exact jacobian_self _
        change _ = 0
        rw [jacobian] at hij
        linear_combination hij)
    exact ⟨h.2, neg_eq_zero.mp h.1⟩
  have h := F.vectorField_eq_zero_of_isFiniteAtOrigin hfinite 1 0 (by
    intro j
    rw [(hpartials j).1, mul_zero, zero_mul, add_zero])
  exact one_ne_zero h.1

theorem jacobian_ne_zero_of_hasFiniteCoordinateFiber
    (F : PointedMapGerm 2 2) (hfinite : F.HasFiniteCoordinateFiber) :
    jacobian (F.1.component 0) (F.1.component 1) ≠ 0 :=
  F.jacobian_ne_zero_of_isFiniteAtOrigin (finiteFiberCriterionAtOrigin_two 2 F hfinite)

end PointedMapGerm

namespace Germ

/-- Two germs vanishing at the origin define a pointed analytic plane map. -/
theorem exists_pointedMapGerm_pair {n : ℕ} (f g : Germ n)
    (hf : f ∈ maximalIdeal n) (hg : g ∈ maximalIdeal n) :
    ∃ F : PointedMapGerm n 2, F.1.component 0 = f ∧ F.1.component 1 = g := by
  obtain ⟨f₀, hf₀, rfl⟩ := Germ.exists_ofFunction f
  obtain ⟨g₀, hg₀, rfl⟩ := Germ.exists_ofFunction g
  have hfzero : f₀ 0 = 0 := by
    simpa only [mem_maximalIdeal_iff, valueRingHom_ofFunction] using hf
  have hgzero : g₀ 0 = 0 := by
    simpa only [mem_maximalIdeal_iff, valueRingHom_ofFunction] using hg
  let F₀ : Source n → Source 2 := fun z => ![f₀ z, g₀ z]
  have hF₀ : AnalyticAt ℂ F₀ 0 := by
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact hf₀
    · exact hg₀
  have hFzero : F₀ 0 = 0 := by
    ext i
    fin_cases i <;> simp [F₀, hfzero, hgzero]
  refine ⟨PointedMapGerm.ofFunction F₀ hF₀ hFzero, ?_, ?_⟩
  · apply Subtype.ext
    exact MapGerm.component_ofFunction F₀ hF₀ 0
  · apply Subtype.ext
    exact MapGerm.component_ofFunction F₀ hF₀ 1

/-- Finite intersection of two pointed plane germs forces a nonzero Jacobian. -/
theorem jacobian_ne_zero_of_hasFiniteIntersection (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hfinite : PlaneCurve.HasFiniteIntersection f g) : jacobian f g ≠ 0 := by
  obtain ⟨F, hFf, hFg⟩ := exists_pointedMapGerm_pair f g hf hg
  have hIdeal : F.1.coordinateIdeal = PlaneCurve.pairIdeal f g := by
    apply le_antisymm
    · rw [MapGerm.coordinateIdeal_le]
      intro j
      fin_cases j
      · change F.1.component 0 ∈ PlaneCurve.pairIdeal f g
        rw [hFf]
        exact Ideal.subset_span (show f ∈ ({f, g} : Set (Germ 2)) by simp)
      · change F.1.component 1 ∈ PlaneCurve.pairIdeal f g
        rw [hFg]
        exact Ideal.subset_span (show g ∈ ({f, g} : Set (Germ 2)) by simp)
    · rw [PlaneCurve.pairIdeal, Ideal.span_le]
      intro z hz
      rcases (show z = f ∨ z = g by simpa using hz) with rfl | rfl
      · rw [← hFf]
        exact F.1.component_mem_coordinateIdeal 0
      · rw [← hFg]
        exact F.1.component_mem_coordinateIdeal 1
  have hFfinite : F.HasFiniteCoordinateFiber := by
    change Module.Finite ℂ (Germ 2 ⧸ F.1.coordinateIdeal)
    rw [hIdeal]
    exact hfinite
  simpa only [hFf, hFg] using F.jacobian_ne_zero_of_hasFiniteCoordinateFiber hFfinite

/-- There are only finitely many nonreduced members of a finite pointed pencil. -/
theorem finite_not_squarefree_pointed_pencil (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hfinite : PlaneCurve.HasFiniteIntersection f g) :
    {c : ℂ | ¬Squarefree (f + constRingHom 2 c * g)}.Finite :=
  finite_not_squarefree_pencil f g hfinite
    (jacobian_ne_zero_of_hasFiniteIntersection f g hf hg hfinite)

theorem exists_squarefree_pointed_pencil_member_mem_open (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hfinite : PlaneCurve.HasFiniteIntersection f g)
    (U : Set ℂ) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ c ∈ U, Squarefree (f + constRingHom 2 c * g) :=
  exists_squarefree_pencil_member_mem_open f g hfinite
    (jacobian_ne_zero_of_hasFiniteIntersection f g hf hg hfinite) U hU hUne

end Germ

end OnLeConjecture.Analytic
