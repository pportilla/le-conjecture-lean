/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.Geometry.Manifold.Immersion.FiniteDimensional
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A complex solid torus in the unit three-sphere

The map sends (u,w) to (u,w)/sqrt(1+‖w‖²). Its first coordinate never
vanishes. Dividing both coordinates by the norm of the first recovers
(u,w), which proves embedding and differential injectivity.
-/

@[expose] public noncomputable section

open Set Manifold
open scoped ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.DifferentialTopology

/-- The normalization factor for the complex solid torus. -/
def complexSolidTorusScale (w : ℂ) : ℝ := (Real.sqrt (1 + ‖w‖ ^ 2))⁻¹

theorem complexSolidTorusScale_pos (w : ℂ) : 0 < complexSolidTorusScale w := by
  unfold complexSolidTorusScale
  positivity

/-- The concrete solid-torus map into real Euclidean four-space. -/
def complexSolidTorusMap (p : Circle × ℂ) : EuclideanSpace ℂ (Fin 2) :=
  complexSolidTorusScale p.2 • (EuclideanSpace.equiv (Fin 2) ℂ).symm ![(p.1 : ℂ), p.2]

@[simp] theorem complexSolidTorusMap_fst (p : Circle × ℂ) :
    complexSolidTorusMap p 0 = complexSolidTorusScale p.2 • (p.1 : ℂ) := rfl

@[simp] theorem complexSolidTorusMap_snd (p : Circle × ℂ) :
    complexSolidTorusMap p 1 = complexSolidTorusScale p.2 • p.2 := rfl

theorem complexSolidTorusMap_norm (p : Circle × ℂ) : ‖complexSolidTorusMap p‖ = 1 := by
  have hs := complexSolidTorusScale_pos p.2
  have hsq : ‖complexSolidTorusMap p‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp only [complexSolidTorusMap_fst, complexSolidTorusMap_snd, norm_smul,
      Real.norm_eq_abs, abs_of_pos hs, Circle.norm_coe, mul_one, mul_pow]
    have h : 0 < 1 + ‖p.2‖ ^ 2 := by positivity
    unfold complexSolidTorusScale
    rw [inv_pow, Real.sq_sqrt h.le]
    field_simp
  nlinarith [norm_nonneg (complexSolidTorusMap p)]

theorem complexSolidTorusMap_fst_norm (p : Circle × ℂ) :
    ‖complexSolidTorusMap p 0‖ = complexSolidTorusScale p.2 := by
  rw [complexSolidTorusMap_fst, norm_smul, Real.norm_eq_abs,
    abs_of_pos (complexSolidTorusScale_pos p.2), Circle.norm_coe, mul_one]

theorem complexSolidTorusMap_fst_ne_zero (p : Circle × ℂ) :
    complexSolidTorusMap p 0 ≠ 0 := by
  apply norm_pos_iff.mp
  rw [complexSolidTorusMap_fst_norm]
  exact complexSolidTorusScale_pos p.2

/-- Recovery of both unnormalized coordinates wherever the first coordinate is nonzero. -/
def complexSolidTorusRecovery (z : EuclideanSpace ℂ (Fin 2)) : ℂ × ℂ :=
  (‖z 0‖⁻¹ • z 0, ‖z 0‖⁻¹ • z 1)

@[simp] theorem complexSolidTorusRecovery_map (p : Circle × ℂ) :
    complexSolidTorusRecovery (complexSolidTorusMap p) = ((p.1 : ℂ), p.2) := by
  unfold complexSolidTorusRecovery
  rw [complexSolidTorusMap_fst_norm]
  simp only [complexSolidTorusMap_fst, complexSolidTorusMap_snd, smul_smul,
    inv_mul_cancel₀ (complexSolidTorusScale_pos p.2).ne', one_smul]

/-- The phase of the first coordinate is the original circle parameter. -/
theorem complexSolidTorusMap_phase (p : Circle × ℂ) :
    ‖complexSolidTorusMap p 0‖⁻¹ • complexSolidTorusMap p 0 = (p.1 : ℂ) :=
  congrArg Prod.fst (complexSolidTorusRecovery_map p)

theorem complexSolidTorusScale_contDiff : ContDiff ℝ ∞ complexSolidTorusScale := by
  apply ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun w => by positivity)).inv
  intro w
  positivity

theorem complexSolidTorusMap_contMDiff :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      complexSolidTorusMap := by
  have hvec : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, Fin 2 → ℂ) ∞
      (fun p : Circle × ℂ => ![(p.1 : ℂ), p.2]) := by
    apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · exact (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp contMDiff_fst
    · exact contMDiff_snd
  have he : ContDiff ℝ ∞ (EuclideanSpace.equiv (Fin 2) ℂ).symm :=
    (EuclideanSpace.equiv (Fin 2) ℂ).symm.contDiff.restrict_scalars ℝ
  exact (complexSolidTorusScale_contDiff.contMDiff.comp contMDiff_snd).smul
    (he.contMDiff.comp hvec)

/-- Coordinate recovery is smooth off the axis where the first coordinate vanishes. -/
theorem complexSolidTorusRecovery_contDiffAt {z : EuclideanSpace ℂ (Fin 2)}
    (hz : z 0 ≠ 0) : ContDiffAt ℝ ∞ complexSolidTorusRecovery z := by
  have he : ContDiff ℝ ∞ (EuclideanSpace.equiv (Fin 2) ℂ) :=
    (EuclideanSpace.equiv (Fin 2) ℂ).contDiff.restrict_scalars ℝ
  have hc (i : Fin 2) : ContDiff ℝ ∞ (fun z : EuclideanSpace ℂ (Fin 2) => z i) :=
    (contDiff_apply ℝ ℂ i).comp he
  have hn := (hc 0).contDiffAt.norm ℂ hz
  have hinv := hn.inv (norm_ne_zero_iff.mpr hz)
  exact (hinv.smul (hc 0).contDiffAt).prodMk (hinv.smul (hc 1).contDiffAt)

/-- The concrete map is an embedding in the ambient real four-space. -/
theorem complexSolidTorusMap_isEmbedding : Topology.IsEmbedding complexSolidTorusMap := by
  let S := {z : EuclideanSpace ℂ (Fin 2) | z 0 ≠ 0}
  let f : Circle × ℂ → S := fun p => ⟨complexSolidTorusMap p, complexSolidTorusMap_fst_ne_zero p⟩
  let g : S → ℂ × ℂ := fun z => complexSolidTorusRecovery z
  have hf : Continuous f := complexSolidTorusMap_contMDiff.continuous.subtype_mk _
  have hg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (complexSolidTorusRecovery_contDiffAt z.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  have hgf : g ∘ f = Prod.map (Subtype.val : Circle → ℂ) id := by
    funext p
    exact complexSolidTorusRecovery_map p
  have he : Topology.IsEmbedding (g ∘ f) := by
    rw [hgf]
    exact Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id
  exact Topology.IsEmbedding.subtypeVal.comp (Topology.IsEmbedding.of_comp hf hg he)

set_option backward.isDefEq.respectTransparency false in
/-- The differential of the solid-torus map is injective at every point. -/
theorem complexSolidTorusMap_mfderiv_injective (p : Circle × ℂ) :
    Function.Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℂ))
      𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) complexSolidTorusMap p) := by
  have hcoe : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun u : Circle => (u : ℂ)) p.1 :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)).mdifferentiableAt
      (by simp) (x := p.1)
  have hcoeinj : Function.Injective
      (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun u : Circle => (u : ℂ)) p.1) := by
    convert! injective_mvfderiv_subtypeVal_sphere p.1
  have hinc : Function.Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℂ))
      𝓘(ℝ, ℂ × ℂ) (Prod.map (fun u : Circle => (u : ℂ)) id) p) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    erw [mfderiv_prodMap hcoe mdifferentiableAt_id, mfderiv_id]
    intro v w h
    change EuclideanSpace ℝ (Fin 1) × ℂ at v w
    apply Prod.ext
    · exact hcoeinj (congrArg (fun q : ℂ × ℂ => q.1) h)
    · exact congrArg (fun q : ℂ × ℂ => q.2) h
  have hchain := mfderiv_comp p
    ((complexSolidTorusRecovery_contDiffAt
      (complexSolidTorusMap_fst_ne_zero p)).contMDiffAt.mdifferentiableAt
      (by simp))
    (complexSolidTorusMap_contMDiff.mdifferentiableAt (by simp) (x := p))
  have heq : complexSolidTorusRecovery ∘ complexSolidTorusMap =
      Prod.map (fun u : Circle => (u : ℂ)) id := funext complexSolidTorusRecovery_map
  rw [heq] at hchain
  intro v w hvw
  apply hinc
  erw [hchain]
  exact congrArg (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) 𝓘(ℝ, ℂ × ℂ)
    complexSolidTorusRecovery (complexSolidTorusMap p)) hvw

/-- The specified normalization is a native smooth embedding. -/
theorem complexSolidTorusMap_isSmoothEmbedding :
    IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      complexSolidTorusMap :=
  complexSolidTorusMap_contMDiff.isSmoothEmbedding_of_injective_mfderiv (by simp)
    complexSolidTorusMap_mfderiv_injective complexSolidTorusMap_isEmbedding

end OnLeConjecture.DifferentialTopology
