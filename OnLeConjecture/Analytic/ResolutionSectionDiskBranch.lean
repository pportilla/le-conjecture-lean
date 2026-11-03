/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionHoleTangent

/-! # The target-section parametrization of each retained source disk

The centered holomorphic parametrization is the actual section map
composed with the already chosen source disk chart. Its circle image is
literally the centered image of the corresponding hole circle. This does
not identify that circle with a small Euclidean sphere link.
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- The actual target-section parametrization, centered at the image of
the chosen critical point. -/
def diskBranch (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (u : ℂ) : CollarPlane :=
  euclideanSectionMap A.H ((D j).ψ u) -
    euclideanSectionMap A.H ((EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))

@[simp] theorem diskBranch_zero (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) :
    L.diskBranch D j 0 = 0 := by
  simp only [diskBranch, (D j).ψ_zero, sub_self]

/-- The parametrization is holomorphic near the entire closed source disk. -/
theorem diskBranch_analytic (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j)
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    (hD : ∀ j, ∀ w ∈ (D j).closedDisk,
      (EuclideanSpace.equiv (Fin 2) ℂ) w ∈ ball 0 L.radius) (j : L.points) :
    AnalyticOnNhd ℂ (L.diskBranch D j) (closedBall 0 (D j).radius) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  intro u hu
  have hψ := (D j).analytic u ((D j).closedBall_subset hu)
  have hH := ha (e ((D j).ψ u)) (ball_subset_closedBall (hD j _ ⟨u, hu, rfl⟩))
  exact (((e.symm.analyticAt _).comp (((hyperplaneTail 2).analyticAt _).comp
    (hH.comp (e.analyticAt _)))).comp hψ).sub analyticAt_const

/-- This parametrization is injective on the entire closed source disk,
even though its differential can vanish at the central critical point. -/
theorem diskBranch_injOn (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j)
    (hD : ∀ j, ∀ w ∈ (D j).closedDisk,
      (EuclideanSpace.equiv (Fin 2) ℂ) w ∈ ball 0 L.radius) (j : L.points) :
    InjOn (L.diskBranch D j) (closedBall 0 (D j).radius) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  intro u hu v hv he
  have he' : euclideanSectionMap A.H ((D j).ψ u) =
      euclideanSectionMap A.H ((D j).ψ v) := by
    simpa only [diskBranch, sub_left_inj] using he
  have hsource (t : ℂ) (ht : t ∈ closedBall 0 (D j).radius) :
      e ((D j).ψ t) ∈ L.sourceLevel :=
    ⟨ball_subset_closedBall (hD j _ ⟨t, ht, rfl⟩),
      (D j).level_eq t ((D j).closedBall_subset ht)⟩
  have he'' : A.sectionMap (e ((D j).ψ u)) = A.sectionMap (e ((D j).ψ v)) := by
    have h := congrArg e he'
    simpa only [e, euclideanSectionMap, ContinuousLinearEquiv.apply_symm_apply,
      ResolutionSectionAssembly.sectionMap] using h
  exact (D j).injOn ((D j).closedBall_subset hu) ((D j).closedBall_subset hv)
    (e.injective (L.sectionMap_injOn (hsource u hu) (hsource v hv) he''))

/-- The target image of the hole circle is exactly the circle image of the
centered analytic parametrization, after the indicated translation. -/
theorem diskBranch_circle_image (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) :
    L.diskBranch D j '' sphere 0 (D j).radius =
      (fun y => y - euclideanSectionMap A.H
        ((EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))) ''
        (euclideanSectionMap A.H '' (D j).boundaryCircle) := by
  simp only [PlaneLevelCoordinateDisk.boundaryCircle, image_image]
  rfl

/-- The circle of the same source disk lies in the actual compact exterior
and has the literal target image used by its section embedding. -/
theorem diskBranch_circle_in_exterior_image (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) {ε : ℝ}
    (hdisj : Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk))
    (hD : ∀ j, (D j).closedDisk ⊆ targetSectionCut A.H L.radius ε L.parameter)
    (j : L.points) :
    euclideanSectionMap A.H '' (D j).boundaryCircle ⊆
      euclideanSectionMap A.H '' L.diskExterior D ε := by
  apply image_mono
  rw [← L.diskExterior_inter_closedDisk D hdisj hD j]
  exact inter_subset_left

end ResolutionSectionLevel
end OnLeConjecture.Analytic
