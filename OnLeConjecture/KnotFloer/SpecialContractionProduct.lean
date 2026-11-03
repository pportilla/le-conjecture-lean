/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.Algebra.Homology.Contraction.Linear
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel

/-!
# Products and coordinate transport of special contractions

These elementary constructions retain the specified inclusion, projection, and homotopy.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.SpecialContraction

open TauCeti

variable {S M N P Q : Type*} [CommRing S]
  [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q]
  {dM : Module.End S M} {dN : Module.End S N}

/-- Take the product of a specified contraction and the identity contraction on another complex. -/
noncomputable def prodIdentity (c : LinearSpecialContraction dM dN) (dP : Module.End S P) :
    LinearSpecialContraction (dM.prodMap dP) (dN.prodMap dP) where
  incl := c.incl.prodMap LinearMap.id
  proj := c.proj.prodMap LinearMap.id
  homotopy := c.homotopy.prodMap 0
  dM_comp_incl := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    exact Prod.ext (c.dM_incl_apply x) rfl
  proj_comp_dM := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    exact Prod.ext (c.proj_dM_apply x) rfl
  proj_comp_incl := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    exact Prod.ext (c.proj_incl_apply x) rfl
  dM_comp_homotopy_add_homotopy_comp_dM := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext
    · exact LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM x
    · change dP 0 + 0 = y - y
      simp
  homotopy_comp_incl := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    exact Prod.ext (c.homotopy_incl_apply x) rfl
  proj_comp_homotopy := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    exact Prod.ext (c.proj_homotopy_apply x) rfl
  homotopy_comp_homotopy := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    exact Prod.ext (c.homotopy_homotopy_apply x) rfl

/-- Change source coordinates by the specified linear equivalence. -/
noncomputable def transportSource (c : LinearSpecialContraction dM dN) (e : Q ≃ₗ[S] M) :
    LinearSpecialContraction
      (e.symm.toLinearMap ∘ₗ dM ∘ₗ e.toLinearMap) dN where
  incl := e.symm.toLinearMap ∘ₗ c.incl
  proj := c.proj ∘ₗ e.toLinearMap
  homotopy := e.symm.toLinearMap ∘ₗ c.homotopy ∘ₗ e.toLinearMap
  dM_comp_incl := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, c.dM_incl_apply]
  proj_comp_dM := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, c.proj_dM_apply]
  proj_comp_incl := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, c.proj_incl_apply, LinearMap.id_apply]
  dM_comp_homotopy_add_homotopy_comp_dM := by
    apply LinearMap.ext
    intro x
    have h := congrArg e.symm (LinearMap.congr_fun
      c.dM_comp_homotopy_add_homotopy_comp_dM (e x))
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
      LinearMap.sub_apply, LinearMap.id_apply, map_add, map_sub] using h
  homotopy_comp_incl := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, c.homotopy_incl_apply, map_zero, LinearMap.zero_apply]
  proj_comp_homotopy := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, c.proj_homotopy_apply, LinearMap.zero_apply]
  homotopy_comp_homotopy := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, c.homotopy_homotopy_apply, map_zero, LinearMap.zero_apply]

/-- The triangular differential with connecting map `K`. -/
def triangularDifferential (dM : Module.End S M) (dP : Module.End S P) (K : P →ₗ[S] M) :
    Module.End S (M × P) :=
  (dM ∘ₗ LinearMap.fst S M P + K ∘ₗ LinearMap.snd S M P).prod
    (dP ∘ₗ LinearMap.snd S M P)

/-- A connecting map killed by the retraction can be removed by its specified homotopy. -/
noncomputable def triangular (c : LinearSpecialContraction dM dN) (dP : Module.End S P)
    (K : P →ₗ[S] M) (hK : dM ∘ₗ K + K ∘ₗ dP = 0) (hpK : c.proj ∘ₗ K = 0) :
    LinearSpecialContraction (triangularDifferential dM dP K) (dN.prodMap dP) where
  incl := (c.incl ∘ₗ LinearMap.fst S N P -
    c.homotopy ∘ₗ K ∘ₗ LinearMap.snd S N P).prod (LinearMap.snd S N P)
  proj := c.proj.prodMap LinearMap.id
  homotopy := c.homotopy.prodMap 0
  dM_comp_incl := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext
    · change dM (c.incl x - c.homotopy (K y)) + K y =
        c.incl (dN x) - c.homotopy (K (dP y))
      have hk := LinearMap.congr_fun hK y
      change dM (K y) + K (dP y) = 0 at hk
      have hp := LinearMap.congr_fun hpK y
      change c.proj (K y) = 0 at hp
      have hc := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM (K y)
      change dM (c.homotopy (K y)) + c.homotopy (dM (K y)) =
        K y - c.incl (c.proj (K y)) at hc
      rw [hp, map_zero, sub_zero] at hc
      have hk' : c.homotopy (dM (K y)) + c.homotopy (K (dP y)) = 0 := by
        rw [← map_add, hk, map_zero]
      rw [eq_neg_of_add_eq_zero_left hk', ← sub_eq_add_neg] at hc
      rw [map_sub, c.dM_incl_apply]
      rw [sub_eq_iff_eq_add.mp hc]
      abel
    · rfl
  proj_comp_dM := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext
    · change c.proj (dM x + K y) = dN (c.proj x)
      rw [map_add, c.proj_dM_apply]
      have hp := LinearMap.congr_fun hpK y
      change c.proj (K y) = 0 at hp
      rw [hp, add_zero]
    · rfl
  proj_comp_incl := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext
    · change c.proj (c.incl x - c.homotopy (K y)) = x
      simp only [map_sub, c.proj_incl_apply, c.proj_homotopy_apply, sub_zero]
    · rfl
  dM_comp_homotopy_add_homotopy_comp_dM := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext
    · change dM (c.homotopy x) + K 0 + c.homotopy (dM x + K y) =
        x - (c.incl (c.proj x) - c.homotopy (K y))
      have hc := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM x
      change dM (c.homotopy x) + c.homotopy (dM x) = x - c.incl (c.proj x) at hc
      rw [map_zero, add_zero, map_add, ← add_assoc, hc]
      abel
    · change dP 0 + 0 = y - y
      simp
  homotopy_comp_incl := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext
    · change c.homotopy (c.incl x - c.homotopy (K y)) = 0
      simp only [map_sub, c.homotopy_incl_apply, c.homotopy_homotopy_apply, sub_self]
    · rfl
  proj_comp_homotopy := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    exact Prod.ext (c.proj_homotopy_apply x) rfl
  homotopy_comp_homotopy := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    exact Prod.ext (c.homotopy_homotopy_apply x) rfl

end OnLeConjecture.KnotFloer.SpecialContraction
