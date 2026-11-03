/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibreCover
public import OnLeConjecture.DifferentialTopology.BranchedSquareHomology

/-!
# Rational homology of polydisc fibres

Let `P' = polydiscFibre H η ρ s` satisfy `GoodPolydisc`, and let `0 < η₀ < η`.
If every branch value of the base projection over the closed square of radius
`η₀` belongs to a finite set `B` of points of the open square, then the
polydisc fibre `P = polydiscFibre H η₀ ρ s` has rational homology concentrated
in degrees zero and one, with Euler characteristic
`d − ∑_{b ∈ B} (d − n_b)`, where `n_b` is the number of points of `P'` over `b`.
This is the Riemann–Hurwitz count, proved by Mayer–Vietoris over rectangles.

When `B` is the set of base points of the ramification points `R`, the defect
`∑_{b ∈ B} (d − n_b)` equals `∑_{z ∈ R} (e_z − 1)`, where `e_z` is the
multiplicity of `z 0` as a root of `t ↦ H (t, z 1) − s`.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.DifferentialTopology OnLeConjecture.Analytic.Germ

theorem convex_openRect (a₁ a₂ c₁ c₂ : ℝ) : Convex ℝ (openRect a₁ a₂ c₁ c₂) := by
  have h : openRect a₁ a₂ c₁ c₂ =
      Complex.reLm ⁻¹' Set.Ioo a₁ a₂ ∩ Complex.imLm ⁻¹' Set.Ioo c₁ c₂ := by
    ext x
    simp only [openRect, mem_ofPred_eq, mem_inter_iff, mem_preimage, Complex.reLm_coe,
      Complex.imLm_coe, mem_Ioo]
    tauto
  rw [h]
  exact ((convex_Ioo a₁ a₂).linear_preimage _).inter ((convex_Ioo c₁ c₂).linear_preimage _)

namespace GoodPolydisc

variable {H : Source 2 → ℂ} {η ρ : ℝ} {s : ℂ} {d : ℕ}

/-- **Riemann–Hurwitz count for polydisc fibres.** -/
theorem hasCurveRatHomology (hP : GoodPolydisc H η ρ s d) {η₀ : ℝ} (hη₀pos : 0 < η₀)
    (hη₀ : η₀ < η) (B : Finset ℂ)
    (hBram : ∀ x, squareNorm x ≤ η₀ → x ∈ ramBase H η ρ s → x ∈ B)
    (hB : ∀ b ∈ B, squareNorm b < η₀) :
    HasCurveRatHomology ↥(polydiscFibre H η₀ ρ s)
      ((d : ℤ) - ∑ b ∈ B, ((d : ℤ) - (proj H η ρ s ⁻¹' {b}).ncard)) := by
  refine hasCurveRatHomology_of_branchedSquare baseProj continuous_baseProj
    (polydiscFibre H η₀ ρ s) η₀ hη₀pos (fun z hz => hz.1) B hB d
    (fun b => (proj H η ρ s ⁻¹' {b}).ncard) ?_ ?_
  · intro a₁ a₂ c₁ c₂ hne hnot
    exact hP.hasDiscreteRatHomology_cell hη₀ (convex_openRect a₁ a₂ c₁ c₂) hne
      (fun x hx hxr => hnot x (hBram x hx.2 hxr) hx.1)
  · intro b hb
    obtain ⟨δ, hδ, hcell⟩ := hP.exists_local_cell hη₀ (hB b hb)
    exact ⟨δ, hδ, fun a₁ a₂ c₁ c₂ hbM hMb => hcell _ hbM (convex_openRect a₁ a₂ c₁ c₂) hMb⟩

/-- The branch defect over the base points of the ramification points is the
total ramification. -/
theorem sum_branch_defect (hP : GoodPolydisc H η ρ s d) (R : Finset (Source 2))
    (hR : ∀ z, z ∈ R ↔ z ∈ polydiscFibre H η ρ s ∧ fibreDerivative H z = 0) :
    ∑ b ∈ R.image (fun z => z 1), ((d : ℤ) - (proj H η ρ s ⁻¹' {b}).ncard) =
      ∑ z ∈ R, (((rootOrder H s (z 0) (z 1)).toNat : ℤ) - 1) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun z : Source 2 => z 1)
    (t := R.image (fun z => z 1)) (fun z hz => Finset.mem_image_of_mem _ hz)]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨z₀, hz₀R, hz₀b⟩ := Finset.mem_image.mp hb
  have hbη : squareNorm b ≤ η := hz₀b ▸ ((hR z₀).mp hz₀R).1.1
  obtain ⟨Z, hZ, hZr, -, hZsum⟩ := hP.roots b hbη
  obtain ⟨-, hcard⟩ := hP.fibre_finite_ncard hbη hZ hZr
  rw [hcard]
  have hleft : (d : ℤ) - Z.card = ∑ y ∈ Z, (((rootOrder H s y b).toNat : ℤ) - 1) := by
    rw [Finset.sum_sub_distrib, ← hZsum]
    push_cast
    simp
  rw [hleft]
  set Rb := R.filter (fun z => z 1 = b) with hRb
  have hinj : Set.InjOn (fun z : Source 2 => z 0) ↑Rb := by
    intro z hz z' hz' hzz
    have h1 : z 1 = b := (Finset.mem_filter.mp hz).2
    have h2 : z' 1 = b := (Finset.mem_filter.mp hz').2
    rw [← planePoint_eta z, ← planePoint_eta z', h1, h2]
    exact congrArg (fun y => planePoint y b) hzz
  have himg : Rb.image (fun z => z 0) ⊆ Z := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hzR, hz1⟩ := Finset.mem_filter.mp hz
    have hzP := ((hR z).mp hzR).1
    rw [← hZ (z 0) hzP.2.1, ← hz1, planePoint_eta]
    exact hzP.2.2
  rw [← Finset.sum_subset himg, Finset.sum_image hinj]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
  · intro y hyZ hyimg
    have hmem := hP.planePoint_mem hbη hZ hZr hyZ
    have hd : fibreDerivative H (planePoint y b) ≠ 0 := by
      intro h0
      apply hyimg
      refine Finset.mem_image.mpr ⟨planePoint y b, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨(hR _).mpr ⟨hmem, h0⟩, rfl⟩
    rw [rootOrder_eq_one_of_fibreDerivative_ne_zero (hP.analyticAt_of_mem hmem) hmem.2.2 hd]
    simp

end GoodPolydisc

end OnLeConjecture.Analytic
