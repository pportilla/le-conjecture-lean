/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibreCover
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Path connectedness and degree zero homology

The rational homology in degree zero of a space has dimension one exactly when
the space is path connected:

* a path connected space has `H₀ ≅ ℚ`;
* if `H₀` is finite dimensional of dimension one, then the space is path
  connected, since `H₀` is free on the set of path components.

Polydisc fibres are locally path connected: at each point, a level chart
identifies a neighbourhood with a star-shaped subset of a disc.
-/

@[expose] public noncomputable section

open Filter Metric Set CategoryTheory CategoryTheory.Limits DirectSum
open scoped Topology

namespace OnLeConjecture.DifferentialTopology

variable {X : Type} [TopologicalSpace X]

/-- Rational `H₀` is free on the set of path components. -/
def ratHZeroEquiv : ratH X 0 ≃ₗ[ℚ] (ZerothHomotopy X →₀ ℚ) := by
  classical
  exact ((TopCat.of X).singularHomology₀Iso (ModuleCat.of ℚ ℚ) ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : ZerothHomotopy (TopCat.of X) => ModuleCat.of ℚ ℚ)
    ).toLinearEquiv.trans (finsuppLEquivDirectSum ℚ ℚ (ZerothHomotopy X)).symm

/-- A path connected space has one-dimensional rational `H₀`. -/
theorem finrank_ratH_zero_of_pathConnected [PathConnectedSpace X] :
    Module.Finite ℚ (ratH X 0) ∧ Module.finrank ℚ (ratH X 0) = 1 := by
  classical
  obtain ⟨hne, hsub⟩ := pathConnectedSpace_iff_zerothHomotopy.mp ‹PathConnectedSpace X›
  have : Unique (ZerothHomotopy X) := ⟨⟨Classical.choice hne⟩, fun a => Subsingleton.elim _ _⟩
  have : Fintype (ZerothHomotopy X) := inferInstance
  have e := (ratHZeroEquiv (X := X))
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_finsupp_self, Fintype.card_unique]

/-- A space with one-dimensional rational `H₀` is path connected. -/
theorem pathConnectedSpace_of_finrank_ratH_zero (hfin : Module.Finite ℚ (ratH X 0))
    (h1 : Module.finrank ℚ (ratH X 0) = 1) : PathConnectedSpace X := by
  classical
  have e₂ := ratHZeroEquiv (X := X)
  have hfinT : Module.Finite ℚ (ZerothHomotopy X →₀ ℚ) := Module.Finite.equiv e₂
  have hrank : Module.finrank ℚ (ZerothHomotopy X →₀ ℚ) = 1 := by rw [← e₂.finrank_eq, h1]
  rcases Module.finite_finsupp_iff.mp hfinT with hT | hT | ⟨-, hT⟩
  · have : Subsingleton (ZerothHomotopy X →₀ ℚ) := inferInstance
    rw [Module.finrank_zero_of_subsingleton] at hrank
    exact absurd hrank zero_ne_one
  · exact absurd hT (not_subsingleton ℚ)
  · have : Fintype (ZerothHomotopy X) := Fintype.ofFinite _
    rw [Module.finrank_finsupp_self] at hrank
    obtain ⟨t, ht⟩ := Fintype.card_eq_one_iff.mp hrank
    rw [pathConnectedSpace_iff_zerothHomotopy]
    exact ⟨⟨t⟩, ⟨fun a b => (ht a).trans (ht b).symm⟩⟩

end OnLeConjecture.DifferentialTopology

namespace OnLeConjecture.Analytic

open OnLeConjecture.DifferentialTopology OnLeConjecture.Analytic.Germ

namespace GoodPolydisc

variable {H : Source 2 → ℂ} {η ρ : ℝ} {s : ℂ} {d : ℕ}

/-- **Local path connectedness of polydisc fibres.** -/
theorem locallyPathConnectedSpace (hP : GoodPolydisc H η ρ s d) {η₀ : ℝ} (hη₀ : η₀ < η) :
    LocallyPathConnectedSpace ↥(polydiscFibre H η₀ ρ s) := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  rintro ⟨w, hw⟩ u hu hwu
  have hwP : w ∈ polydiscFibre H η ρ s := polydiscFibre_mono H hη₀.le ρ s hw
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨ru, hru, hball⟩ := Metric.isOpen_iff.mp hO w hwu
  have hwsq : squareNorm (w 1) < η := hw.1.trans_lt hη₀
  have hr₀ : 0 < min ru (min (ρ / 2) (η - squareNorm (w 1))) :=
    lt_min hru (lt_min (half_pos hP.radius_pos) (by linarith))
  obtain ⟨k, hk, -, hch⟩ := exists_levelChart H (hP.analyticAt_of_mem hwP) (hP.grad _ hwP)
    (by simp only [update_zero_eq_planePoint, hwP.2.2]; exact hP.rootOrder_ne_top hwP)
  obtain ⟨N, hNo, hwN, hNball, r, hr, τ, hτ⟩ := hch _ hr₀
  have hNsub : N ∩ {z | H z = H w} ⊆ polydiscFibre H η ρ s :=
    hP.chart_subset hwP (hNball.trans (ball_subset_ball (min_le_right _ _)))
  set P₀ := polydiscFibre H η₀ ρ s with hP₀
  set V : Set ↥P₀ := {y | (y : Source 2) ∈ N} with hV
  have hVnhds : V ∈ 𝓝 (⟨w, hw⟩ : ↥P₀) := (hNo.preimage continuous_subtype_val).mem_nhds hwN
  have hVu : V ⊆ Subtype.val ⁻¹' O := fun y hy =>
    hball (mem_ball.mpr ((mem_ball.mp (hNball hy)).trans_le (min_le_left _ _)))
  -- the chart identifies `V` with a star-shaped set
  set A := P₀ ∩ N with hA
  have hAD : A ⊆ N ∩ {z | H z = H w} := by
    rintro z ⟨hzP, hzN⟩
    exact ⟨hzN, hzP.2.2.trans hwP.2.2.symm⟩
  set S : Set ℂ := {t | t ∈ ball (0 : ℂ) r ∧ w 1 + t ^ k ∈ closedSquare η₀} with hS
  have hSball : S ⊆ ball (0 : ℂ) r := fun t ht => ht.1
  have e1 : ↥V ≃ₜ ↥A := (Homeomorph.setCongr (by
      ext y
      simp only [V, A, mem_ofPred_eq, mem_inter_iff]
      exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩)).trans
    (nestedSubtypeHomeomorph (inter_subset_left : A ⊆ P₀))
  have e2 : ↥A ≃ₜ {u : ↥(N ∩ {z | H z = H w}) // (u : Source 2) 1 ∈ closedSquare η₀} :=
    (nestedSubtypeHomeomorph hAD).symm.trans (Homeomorph.setCongr (by
      ext u
      simp only [mem_ofPred_eq, A, P₀, mem_inter_iff]
      have huP := hNsub u.2
      constructor
      · rintro ⟨⟨h, -, -⟩, -⟩
        exact h
      · intro h
        exact ⟨⟨h, huP.2.1, huP.2.2⟩, u.2.1⟩))
  have e3 : {u : ↥(N ∩ {z | H z = H w}) // (u : Source 2) 1 ∈ closedSquare η₀} ≃ₜ
      {t : ↥(ball (0 : ℂ) r) // w 1 + (t : ℂ) ^ k ∈ closedSquare η₀} :=
    τ.subtype (fun u => by rw [hτ u])
  have e4 : {t : ↥(ball (0 : ℂ) r) // w 1 + (t : ℂ) ^ k ∈ closedSquare η₀} ≃ₜ ↥S :=
    (Homeomorph.setCongr (by
      ext t
      simp only [mem_ofPred_eq, S]
      exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩)).trans (nestedSubtypeHomeomorph hSball)
  have hSpc : IsPathConnected S := by
    refine StarConvex.isPathConnected
      (starConvex_pow_preimage k r ((convex_closedSquare η₀).starConvex hw.1)) ?_
    refine ⟨mem_ball_self hr, ?_⟩
    rw [zero_pow hk.ne', add_zero]
    exact hw.1
  have hSspace : PathConnectedSpace ↥S := isPathConnected_iff_pathConnectedSpace.mp hSpc
  have hVspace : PathConnectedSpace ↥V :=
    (e1.trans (e2.trans (e3.trans e4))).symm.surjective.pathConnectedSpace
      (e1.trans (e2.trans (e3.trans e4))).symm.continuous
  have hVpc : IsPathConnected V := isPathConnected_iff_pathConnectedSpace.mpr hVspace
  exact Filter.mem_of_superset hVnhds (hVpc.subset_pathComponentIn hwN hVu)

end GoodPolydisc

end OnLeConjecture.Analytic
