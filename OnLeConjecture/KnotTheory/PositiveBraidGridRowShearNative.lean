/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRowShear

/-! # Native smoothness and immersion of the row deformation

The row shear is applied to the same cylinder coordinates as the closed rounded
carrier. Its Euclidean extension commutes with the cylinder inclusion, which
transfers the proved derivative injection to the native cylinder manifold.
-/

@[expose] public noncomputable section
open Set Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

local instance rowShearRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance rowShearRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- The literal inclusion of the cylinder into two complex coordinates. -/
def positiveGridCylinderCoordinates (p : Circle × ℂ) : ℂ × ℂ := ((p.1 : ℂ), p.2)

theorem positiveGridCylinderCoordinates_contMDiff :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ × ℂ) ∞ positiveGridCylinderCoordinates := by
  have hco : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun x : Circle => (x : ℂ)) :=
    contMDiff_coe_sphere (E := ℂ) (n := 1)
  exact (hco.comp contMDiff_fst).prodMk_space contMDiff_snd

set_option backward.isDefEq.respectTransparency false in
theorem positiveGridCylinderCoordinates_mfderiv_injective (p : Circle × ℂ) :
    Function.Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ × ℂ)
      positiveGridCylinderCoordinates p) := by
  unfold positiveGridCylinderCoordinates
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  change Function.Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
    (Prod.map (fun x : Circle => (x : ℂ)) id) p)
  have hco : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun x : Circle => (x : ℂ)) :=
    contMDiff_coe_sphere (E := ℂ) (n := 1)
  rw [mfderiv_prodMap (hco.mdifferentiableAt (by simp)) mdifferentiableAt_id, mfderiv_id]
  have hc : Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun x : Circle => (x : ℂ)) p.1) := by
    convert! injective_mvfderiv_subtypeVal_sphere p.1
  exact hc.prodMap Function.injective_id

theorem positiveGridRowShearCylinder_contMDiff {q : ℂ × ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContMDiff (((𝓡 1).prod 𝓘(ℝ, ℂ)).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
      (fun p : (Circle × ℂ) × ℝ => positiveGridRowShearCylinder q p.2 p.1) := by
  have hs : ContMDiff (((𝓡 1).prod 𝓘(ℝ, ℂ)).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ × ℂ) ∞
      (fun p : (Circle × ℂ) × ℝ =>
        positiveGridRowShear q p.2 (positiveGridCylinderCoordinates p.1)) :=
    (positiveGridRowShear_contDiff hq).contMDiff.comp
      (contMDiff_snd.prodMk_space (positiveGridCylinderCoordinates_contMDiff.comp contMDiff_fst))
  exact (contMDiff_fst.comp contMDiff_fst).prodMk
    ((ContinuousLinearMap.snd ℝ ℂ ℂ).contDiff.contMDiff.comp hs)

set_option backward.isDefEq.respectTransparency false in
theorem positiveGridRowShearCylinder_mfderiv_injective {q : ℂ × ℝ → ℝ}
    (hqs : ContDiff ℝ ∞ q) (hq : LipschitzWith (1 / 2) q) (s : ℝ) (p : Circle × ℂ) :
    Function.Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℂ)) ((𝓡 1).prod 𝓘(ℝ, ℂ))
      (positiveGridRowShearCylinder q s) p) := by
  let E := positiveGridCylinderCoordinates
  let H := positiveGridRowShearCylinder q s
  let Ψ := positiveGridRowShear q s
  have hE : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ × ℂ) ∞ E :=
    positiveGridCylinderCoordinates_contMDiff
  have hH : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ H :=
    (positiveGridRowShearCylinder_contMDiff hqs).comp (contMDiff_id.prodMk contMDiff_const)
  have hΨ : ContDiff ℝ ∞ Ψ :=
    (positiveGridRowShear_contDiff hqs).comp (contDiff_const.prodMk contDiff_id)
  have hcomm : E ∘ H = Ψ ∘ E := rfl
  have hleft := mfderiv_comp p (hE.mdifferentiableAt (by simp)) (hH.mdifferentiableAt (by simp))
  have hright := mfderiv_comp p (hΨ.contMDiff.mdifferentiableAt (by simp))
    (hE.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hright
  intro v w hvw
  apply positiveGridCylinderCoordinates_mfderiv_injective p
  apply positiveGridRowShear_fderiv_injective hqs hq s (E p)
  have hh : (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ × ℂ) (E ∘ H) p) v =
      (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ × ℂ) (E ∘ H) p) w := by
    rw [hleft]
    exact congrArg (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ × ℂ) E (H p)) hvw
  rw [hcomm, hright] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
/-- The selected-coordinate solid-torus map has an injective native derivative. -/
theorem positiveGridSolidTorus_mfderiv_injective (i : Fin 2) (p : Circle × ℂ) :
    Function.Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℂ))
      𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) (planeSolidTorusMap i) p) := by
  let e := planeSolidTorusCoordinateEquiv i
  have he : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
      𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ e := e.contDiff.contMDiff
  rw [planeSolidTorusMap_eq_coordinateEquiv,
    mfderiv_comp p (he.mdifferentiableAt (by simp))
      (complexSolidTorusMap_contMDiff.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, e.fderiv]
  exact e.injective.comp (complexSolidTorusMap_mfderiv_injective p)

/-- A smooth embedded cylinder circle remains smoothly embedded throughout the
constructed row shear, and the sphere endpoints admit a native ambient diffeotopy. -/
theorem exists_positiveGridRowShear_sphere_diffeotopy (i : Fin 2)
    {F : Circle → Circle × ℂ}
    (hF : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ F)
    (hFi : Function.Injective F)
    (hFd : ∀ u, Function.Injective (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) F u))
    {q : ℂ × ℝ → ℝ} (hqs : ContDiff ℝ ∞ q) (hq : LipschitzWith (1 / 2) q) :
    ∃ (A B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
      (∀ v, (A v : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (F v)) ∧
      (∀ v, (B v : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q 1 (F v))) ∧
      ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        ∀ v, Φ.final (A v) = B v := by
  let H : Circle × ℝ → Circle × ℂ := fun p => positiveGridRowShearCylinder q p.2 (F p.1)
  have hH : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ H :=
    (positiveGridRowShearCylinder_contMDiff hqs).comp
      ((hF.comp contMDiff_fst).prodMk contMDiff_snd)
  have hHs (s : ℝ) : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ (fun v => H (v, s)) :=
    hH.comp (contMDiff_id.prodMk contMDiff_const)
  have hHi (s : ℝ) : Function.Injective (fun v => H (v, s)) :=
    (positiveGridRowShearCylinder_injective hq s).comp hFi
  have hHd (s : ℝ) (u : Circle) : Function.Injective
      (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) (fun v => H (v, s)) u) := by
    have hrow : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
        (positiveGridRowShearCylinder q s) :=
      (positiveGridRowShearCylinder_contMDiff hqs).comp (contMDiff_id.prodMk contMDiff_const)
    change Function.Injective (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ))
      (positiveGridRowShearCylinder q s ∘ F) u)
    rw [mfderiv_comp u (hrow.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))]
    exact (positiveGridRowShearCylinder_mfderiv_injective hqs hq s _).comp (hFd u)
  let K : Circle × ℝ → EuclideanSpace ℂ (Fin 2) := fun p => planeSolidTorusMap i (H p)
  have hK := (planeSolidTorusMap_isSmoothEmbedding i).contMDiff.comp hH
  have hKd (s : ℝ) (u : Circle) : Function.Injective
      (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) (fun v => K (v, s)) u) := by
    change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
      (planeSolidTorusMap i ∘ (fun v => H (v, s))) u)
    rw [mfderiv_comp u ((planeSolidTorusMap_isSmoothEmbedding i).contMDiff.mdifferentiableAt
      (by simp)) ((hHs s).mdifferentiableAt (by simp))]
    exact (positiveGridSolidTorus_mfderiv_injective i _).comp (hHd s u)
  obtain ⟨A, B, hA, hB, Φ, hΦ⟩ := exists_plane_sphere_family_endpoint_diffeotopy K
    (fun _ _ => planeSolidTorusMap_norm i _) hK hKd
    (fun s => (planeSolidTorusMap_isSmoothEmbedding i).isEmbedding.comp
      (((hHs s).continuous.isClosedEmbedding (hHi s)).isEmbedding))
  refine ⟨A, B, ?_, hB, Φ, hΦ⟩
  intro v
  simpa only [K, H, positiveGridRowShearCylinder, positiveGridRowShear_zero] using hA v

end OnLeConjecture.KnotTheory
