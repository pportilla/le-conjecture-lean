/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionHoleNeighborhood

/-! # Oriented half-plane charts of the same disk exterior

Each chosen hole circle has an oriented real analytic chart whose upper
half-plane is exactly the literal exterior in that chart. Its real axis
is exactly the chosen circle, and its tangent has clockwise sign in the
retained holomorphic disk coordinate.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff ComplexConjugate

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- The actual hole boundary admits an oriented half-plane chart, with
literal membership and relative-neighborhood conclusions for the same
compact exterior. The sign is negative in the holomorphic disk coordinate. -/
theorem exists_diskExterior_holeChart (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) {ε : ℝ}
    (hε : 0 < ε) (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    (hdisj : Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk))
    (hD : ∀ j, ∀ w ∈ (D j).closedDisk,
      (EuclideanSpace.equiv (Fin 2) ℂ) w ∈ ball 0 L.radius ∧
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
        (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w))‖ < ε / 2)
    (j : L.points) {z : CollarPlane} (hz : z ∈ (D j).boundaryCircle) :
    ∃ (O : Set CollarPlane) (_ : IsOpen O) (_ : z ∈ O)
      (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
        (D j).holeRadius O z),
      (∀ t ∈ C.W, C.φ t ∈ L.diskExterior D ε ↔ 0 ≤ t.im) ∧
      (∀ t ∈ C.W, C.φ t ∈ (D j).boundaryCircle ↔ t.im = 0) ∧
      MapsTo C.φ C.model (L.diskExterior D ε) ∧
      C.φ '' C.model ∈ 𝓝[L.diskExterior D ε] z ∧
      (∀ t ∈ C.W, Injective (fderiv ℝ C.φ t)) ∧
      fderiv ℂ (euclideanEquation (fun x => A.H x 0)) z (fderiv ℝ C.φ 0 1) = 0 ∧
      (conj ((D j).coordinate (z - (EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))) *
        (D j).coordinate (fderiv ℝ C.φ 0 1)).re = 0 ∧
      (conj ((D j).coordinate (z - (EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))) *
        (D j).coordinate (fderiv ℝ C.φ 0 1)).im < 0 := by
  obtain ⟨u, hu, rfl⟩ := hz
  have huW := (D j).closedBall_subset (sphere_subset_closedBall hu)
  have hzD : (D j).ψ u ∈ (D j).closedDisk := ⟨u, sphere_subset_closedBall hu, rfl⟩
  have hzC : (D j).ψ u ∈ (D j).boundaryCircle := ⟨u, hu, rfl⟩
  have hlevel := (D j).level_eq u huW
  obtain ⟨hf, hfn⟩ := L.euclidean_level_analytic_regular ha (hD j _ hzD).1 hlevel
  obtain ⟨O, hOprop, hO, hzO⟩ := _root_.eventually_nhds_iff.mp
    (L.eventually_diskExterior_hole_iff D hε ha hdisj hD j hzC)
  have hu0 : u ≠ 0 := by
    intro hn
    have he := mem_sphere_zero_iff_norm.mp hu
    rw [hn, norm_zero] at he
    exact (ne_of_gt (D j).radius_pos) he.symm
  obtain ⟨C⟩ := nonempty_sectionRadiusBoundaryChart _ (D j).holeRadius O hO hzO hf
    (fun _ _ => (D j).contDiff_holeRadius.contDiffAt)
    ((D j).holeRadius_pair_surjective huW hu0 hf hfn)
  have hext : ∀ t ∈ C.W, C.φ t ∈ L.diskExterior D ε ↔ 0 ≤ t.im := by
    intro t ht
    rw [(hOprop _ (C.mapsTo ht)).1, C.level_eq t ht, hlevel, and_iff_right rfl,
      C.radius_eq t ht]
    constructor <;> intro h <;> linarith
  have hcircle : ∀ t ∈ C.W, C.φ t ∈ (D j).boundaryCircle ↔ t.im = 0 := by
    intro t ht
    rw [(hOprop _ (C.mapsTo ht)).2, C.level_eq t ht, hlevel, and_iff_right rfl]
    exact C.boundary_iff ht
  have hmaps : MapsTo C.φ C.model (L.diskExterior D ε) :=
    fun t ht => (hext t ht.1).mpr ht.2
  have hOn : ∀ᶠ w in 𝓝 ((D j).ψ u), w ∈ O := hO.mem_nhds hzO
  have hnhds : C.φ '' C.model ∈ 𝓝[L.diskExterior D ε] ((D j).ψ u) := by
    filter_upwards [C.local_inverse.filter_mono nhdsWithin_le_nhds,
      hOn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with w hw hwO hwE
    have hwf := ((hOprop _ hwO).1.mp hwE).1
    obtain ⟨hwW, he⟩ := hw (hwf.trans hlevel.symm)
    refine ⟨C.χ w, ⟨hwW, ?_⟩, he⟩
    change 0 ≤ (C.χ w).im
    rw [C.inverse_im]
    exact sub_nonneg.mpr (((hOprop _ hwO).1.mp hwE).2)
  exact ⟨O, hO, hzO, C, hext, hcircle, hmaps, hnhds,
    fun t ht => C.immersion hO ht, (D j).holeRadius_chart_tangent C hf.differentiableAt⟩

end ResolutionSectionLevel
end OnLeConjecture.Analytic
