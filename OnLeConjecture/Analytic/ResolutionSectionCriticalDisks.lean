/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionCoordinateDisk

/-! # Disjoint source disks around the complete critical-point list

The disks are chosen for the same nearby section and lie strictly inside
the chosen target cut. Finite Hausdorff separation is used before the
holomorphic coordinate disks are shrunk.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- A coordinate disk centered at one of the actual critical points,
expressed in Euclidean source coordinates. -/
abbrev PointCoordinateDisk (L : ResolutionSectionLevel A) (j : L.points) :=
  PlaneLevelCoordinateDisk (euclideanEquation (fun x => A.H x 0)) L.parameter
    ((EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))

/-- Pairwise disjoint source coordinate disks can be chosen around every
listed critical point, strictly inside the prescribed target norm bound. -/
theorem exists_disjoint_pointCoordinateDisks (L : ResolutionSectionLevel A)
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius)) {η : ℝ}
    (hinner : ∀ x ∈ L.points, ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ < η) :
    ∃ D : (j : L.points) → L.PointCoordinateDisk j,
      Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk) ∧
      ∀ j, ∀ z ∈ (D j).closedDisk,
        (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ ball 0 L.radius ∧
        ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
          (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) z))‖ < η := by
  classical
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let f : CollarPlane → ℂ := euclideanEquation (fun x => A.H x 0)
  let Q : CollarPlane → EuclideanSpace ℂ (Fin 3) :=
    fun z => (EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H (e z))
  let P : Set CollarPlane := e.symm '' (L.points : Set (Source 2))
  obtain ⟨U, hU, hsep⟩ := (L.points.finite_toSet.image e.symm).t2_separation
  let S (j : L.points) : Set CollarPlane :=
    U (e.symm j) ∩ (e ⁻¹' ball 0 L.radius ∩ {z | ‖Q z‖ < η})
  have hD (j : L.points) : ∃ D : L.PointCoordinateDisk j, D.closedDisk ⊆ S j := by
    have hj := (L.points_iff j).mp j.property
    let z : CollarPlane := e.symm j
    have hez : e z = (j : Source 2) := e.apply_symm_apply _
    have hH : AnalyticAt ℂ A.H (e z) := by
      rw [hez]
      exact ha j (ball_subset_closedBall hj.1)
    have hf : AnalyticAt ℂ f z := ((analyticAt_pi_iff.mp hH) 0).comp (e.analyticAt z)
    have hfz : f z = L.parameter := by change A.H (e z) 0 = _; rw [hez]; exact hj.2.1
    have hdf : fderiv ℂ f z =
        (fderiv ℂ (fun x => A.H x 0) (e z)).comp e.toContinuousLinearMap :=
      (((analyticAt_pi_iff.mp hH) 0).differentiableAt.hasFDerivAt.comp z e.hasFDerivAt).fderiv
    have hfn : fderiv ℂ f z ≠ 0 := by
      intro hn
      have hzero : fderiv ℂ (fun x => A.H x 0) (e z) = 0 := by
        ext v
        have he := DFunLike.congr_fun hn (e.symm v)
        simpa only [hdf, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply, zero_apply] using he
      rw [hez] at hzero
      exact (L.regular j hj.1 hj.2.1).1 hzero
    have hSn : S j ∈ 𝓝 z := by
      have he : ContinuousAt e z := e.continuous.continuousAt
      have hQ : ContinuousAt Q z :=
        (((EuclideanSpace.equiv (Fin 3) ℂ).symm.analyticAt _).comp
          (hH.comp (e.analyticAt z))).continuousAt
      have hsource : e ⁻¹' ball 0 L.radius ∈ 𝓝 z :=
        he.preimage_mem_nhds (isOpen_ball.mem_nhds (hez.symm ▸ hj.1))
      have hnorm : {w : CollarPlane | ‖Q w‖ < η} ∈ 𝓝 z := by
        apply (hQ.norm.eventually (gt_mem_nhds ?_))
        change ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H (e z))‖ < η
        rw [hez]
        exact hinner j j.property
      exact inter_mem ((hU z).2.mem_nhds (hU z).1) (inter_mem hsource hnorm)
    exact exists_planeLevelCoordinateDisk f hf hfz hfn hSn
  choose D hD using hD
  refine ⟨D, ?_, fun j z hz => (hD j hz).2⟩
  intro j k hjk
  have hpj : e.symm (j : Source 2) ∈ P := ⟨j, j.property, rfl⟩
  have hpk : e.symm (k : Source 2) ∈ P := ⟨k, k.property, rfl⟩
  have hne : e.symm (j : Source 2) ≠ e.symm (k : Source 2) := by
    intro he
    exact hjk (Subtype.ext (e.symm.injective he))
  exact (hsep hpj hpk hne).mono (fun z hz => (hD j hz).1) (fun z hz => (hD k hz).1)

end ResolutionSectionLevel

end OnLeConjecture.Analytic
