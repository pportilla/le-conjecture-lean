/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionCriticalExterior
public import OnLeConjecture.Analytic.ResolutionSectionHoleCharts

/-! # The standing hypotheses on one punctured nearby section

`ResolutionSectionAssembly.exists_targetSectionCriticalExterior` chooses one
nearby level `L`, one target cutoff `ε` and pairwise disjoint coordinate disks
`D` around the complete critical list of `L`. We record the conclusions used
later about this one choice as the proposition `L.ExteriorHypotheses D ε`, and
prove that every sufficiently small `ε` admits such a choice at one fixed source
radius. We also collect elementary consequences for the literal punctured
section `L.diskExterior D ε`.
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.DifferentialTopology OnLeConjecture.PlaneCurve

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

namespace ResolutionSectionAssembly

/-- The Milnor number `μ = dim_ℂ 𝒪₂ / J(v)` of the reduced source equation `v`. -/
def sourceMilnorNumber (A : ResolutionSectionAssembly g hd hi) : ℕ :=
  Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation)

end ResolutionSectionAssembly

namespace ResolutionSectionLevel

variable {A : ResolutionSectionAssembly g hd hi}

/-- The properties of one nearby level `L`, target cutoff `ε` and coordinate
disks `D` supplied by `exists_targetSectionCriticalExterior`. -/
structure ExteriorHypotheses (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (ε : ℝ) : Prop where
  pos : 0 < ε
  analytic : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius)
  injOn : InjOn A.H (closedBall (0 : Source 2) L.radius)
  parameter_lt : ‖L.parameter‖ < ε / 2
  disjoint : Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
  disk_inside : ∀ j, ∀ w ∈ (D j).closedDisk,
    (EuclideanSpace.equiv (Fin 2) ℂ) w ∈ ball 0 L.radius ∧
    ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
      (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w))‖ < ε / 2
  confinement : ∀ x ∈ closedBall (0 : Source 2) L.radius,
    ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ ≤ ε → x ∈ ball 0 (L.radius / 2)
  submersion : ∀ x ∈ closedBall (0 : Source 2) L.radius, A.H x 0 = L.parameter →
    ε / 2 ≤ ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ →
    Surjective (fderiv ℝ (planeMapTargetRadialPair A.H) x)
  cut_homology : HasCurveRatHomology ↥(targetSectionCut A.H L.radius ε L.parameter)
    (1 - (A.sourceMilnorNumber : ℤ))
  cut_rank_zero :
    Module.finrank ℚ (ratH ↥(targetSectionCut A.H L.radius ε L.parameter) 0) = 1
  cut_rank_one :
    Module.finrank ℚ (ratH ↥(targetSectionCut A.H L.radius ε L.parameter) 1) =
      A.sourceMilnorNumber
  cut_compact : IsCompact (targetSectionCut A.H L.radius ε L.parameter)
  cut_pathConnected : IsPathConnected (targetSectionCut A.H L.radius ε L.parameter)

namespace ExteriorHypotheses

variable {L : ResolutionSectionLevel A} {D : (j : L.points) → L.PointCoordinateDisk j}
  {ε : ℝ}

theorem disk_mem_ball (hL : L.ExteriorHypotheses D ε) (j : L.points) :
    ∀ w ∈ (D j).closedDisk, (EuclideanSpace.equiv (Fin 2) ℂ) w ∈ ball 0 L.radius :=
  fun w hw => (hL.disk_inside j w hw).1

/-- Every closed coordinate disk lies in the target cut. -/
theorem closedDisk_subset_cut (hL : L.ExteriorHypotheses D ε) (j : L.points) :
    (D j).closedDisk ⊆ targetSectionCut A.H L.radius ε L.parameter := by
  intro z hz
  exact (mem_targetSectionCut_iff hL.pos.le).mpr
    ⟨⟨ball_subset_closedBall (hL.disk_inside j z hz).1, (D j).closedDisk_subset_level hz⟩,
      ((hL.disk_inside j z hz).2.trans (half_lt_self hL.pos)).le⟩

/-- Every point of the target cut lies in the open source ball. -/
theorem mem_ball_of_mem_cut (hL : L.ExteriorHypotheses D ε) {z : CollarPlane}
    (hz : z ∈ targetSectionCut A.H L.radius ε L.parameter) :
    (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ ball 0 L.radius := by
  have hz' := (mem_targetSectionCut_iff hL.pos.le).mp hz
  exact ball_subset_ball (half_lt_self L.radius_pos).le (hL.confinement _ hz'.1.1 hz'.2)

theorem isCompact_diskExterior (hL : L.ExteriorHypotheses D ε) :
    IsCompact (L.diskExterior D ε) :=
  L.isCompact_diskExterior D hL.cut_compact

theorem isClosed_diskExterior (hL : L.ExteriorHypotheses D ε) :
    IsClosed (L.diskExterior D ε) :=
  hL.isCompact_diskExterior.isClosed

theorem diskExterior_subset_cut (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (ε : ℝ) :
    L.diskExterior D ε ⊆ targetSectionCut A.H L.radius ε L.parameter :=
  sdiff_subset

/-- The exterior meets each closed disk exactly in its coordinate circle. -/
theorem diskExterior_inter_closedDisk (hL : L.ExteriorHypotheses D ε) (j : L.points) :
    L.diskExterior D ε ∩ (D j).closedDisk = (D j).boundaryCircle :=
  L.diskExterior_inter_closedDisk D hL.disjoint hL.closedDisk_subset_cut j

theorem boundaryCircle_subset_diskExterior (hL : L.ExteriorHypotheses D ε) (j : L.points) :
    (D j).boundaryCircle ⊆ L.diskExterior D ε := by
  rw [← hL.diskExterior_inter_closedDisk j]
  exact inter_subset_left

/-- The outer target boundary lies in the exterior. -/
theorem targetSectionBoundary_subset (hL : L.ExteriorHypotheses D ε) :
    targetSectionBoundary A.H L.radius ε L.parameter ⊆ L.diskExterior D ε :=
  L.targetSectionBoundary_subset_diskExterior D hL.pos.le (half_lt_self hL.pos).le
    (fun j z hz => (hL.disk_inside j z hz).2)

/-- The target cut is the union of the exterior and the closed disks. -/
theorem cut_eq_union (hL : L.ExteriorHypotheses D ε) :
    targetSectionCut A.H L.radius ε L.parameter =
      L.diskExterior D ε ∪ ⋃ j, (D j).closedDisk := by
  apply Subset.antisymm
  · intro z hz
    by_cases hE : z ∈ L.diskExterior D ε
    · exact Or.inl hE
    · have : z ∈ ⋃ j, (D j).openDisk := by
        by_contra hn
        exact hE ⟨hz, hn⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp this
      exact Or.inr (mem_iUnion.mpr ⟨j, (D j).openDisk_subset_closedDisk hj⟩)
  · rintro z (hz | hz)
    · exact hz.1
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      exact hL.closedDisk_subset_cut j hj

/-- The actual section map is a closed embedding of the exterior. -/
theorem closedEmbedding (hL : L.ExteriorHypotheses D ε) :
    Topology.IsClosedEmbedding ((L.diskExterior D ε).domRestrict (euclideanSectionMap A.H)) :=
  L.diskExterior_closedEmbedding D hL.analytic hL.cut_compact

end ExteriorHypotheses

end ResolutionSectionLevel

namespace ResolutionSectionAssembly

/-- **The standing hypotheses hold.** One source radius `R` and every
sufficiently small target cutoff `ε` have a nearby level at radius `R` and
coordinate disks satisfying `ExteriorHypotheses`. -/
theorem exists_exteriorHypotheses (A : ResolutionSectionAssembly g hd hi) :
    ∃ R ε₀ : ℝ, 0 < R ∧ R < A.radius ∧ 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ L : ResolutionSectionLevel A, L.radius = R ∧
        ∃ D : (j : L.points) → L.PointCoordinateDisk j, L.ExteriorHypotheses D ε := by
  obtain ⟨R, ε₀, hR, hRA, hε₀, ha, hinj, hlevel⟩ := A.exists_targetSectionCriticalExterior
  refine ⟨R, ε₀, hR, hRA, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨L, hLR, hs, hh, hzero, hone, hc, hp, -, hconf, hsub, -, D, hdisj, hD, -⟩ :=
    hlevel ε hε hεε₀
  subst hLR
  exact ⟨L, rfl, D, ⟨hε, ha, hinj, hs, hdisj, hD, hconf, hsub, hh, hzero, hone, hc, hp⟩⟩

end ResolutionSectionAssembly

end OnLeConjecture.Analytic
