/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ImageRing
public import OnLeConjecture.Analytic.Equivalence
public import OnLeConjecture.Analytic.Residue
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Pullback by analytic equivalence germs

Pullback reverses composition. Consequently, an invertible pointed analytic
germ induces an equivalence of analytic local rings.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace PointedMapGerm

/-- Pullback reverses composition of pointed analytic map germs. -/
theorem pullbackRingHom_comp {l n m : ℕ}
    (g : PointedMapGerm n m) (h : PointedMapGerm l n) :
    (g.comp h).pullbackRingHom =
      h.pullbackRingHom.comp g.pullbackRingHom := by
  ext q
  rcases q with ⟨q, hq⟩
  rcases g with ⟨⟨g, hg⟩, hg0⟩
  rcases h with ⟨⟨h, hh⟩, hh0⟩
  induction q using Filter.Germ.inductionOn with
  | _ q =>
      induction g using Filter.Germ.inductionOn with
      | _ g =>
          induction h using Filter.Germ.inductionOn with
          | _ h =>
              rfl

/-- Pullback by the identity germ is the identity homomorphism. -/
theorem pullbackRingHom_identity (n : ℕ) :
    (PointedMapGerm.identity n).pullbackRingHom = RingHom.id (Germ n) := by
  ext q
  rcases q with ⟨q, hq⟩
  induction q using Filter.Germ.inductionOn with
  | _ q =>
      rfl

end PointedMapGerm

namespace PointedEquivGerm

/-- Pullback by an invertible pointed analytic germ is an equivalence of
analytic local rings. -/
@[expose] noncomputable def pullbackRingEquiv {n : ℕ}
    (e : PointedEquivGerm n) :
    Germ n ≃+* Germ n where
  toFun := e.forward.pullbackRingHom
  invFun := e.inverse.pullbackRingHom
  map_add' := e.forward.pullbackRingHom.map_add
  map_mul' := e.forward.pullbackRingHom.map_mul
  left_inv q := by
    have hid := congrArg
      (fun f : PointedMapGerm n n ↦ f.pullbackRingHom)
      e.forward_inverse
    rw [PointedMapGerm.pullbackRingHom_comp,
      PointedMapGerm.pullbackRingHom_identity] at hid
    exact DFunLike.congr_fun hid q
  right_inv q := by
    have hid := congrArg
      (fun f : PointedMapGerm n n ↦ f.pullbackRingHom)
      e.inverse_forward
    rw [PointedMapGerm.pullbackRingHom_comp,
      PointedMapGerm.pullbackRingHom_identity] at hid
    exact DFunLike.congr_fun hid q

@[simp]
theorem pullbackRingEquiv_apply {n : ℕ} (e : PointedEquivGerm n)
    (q : Germ n) :
    e.pullbackRingEquiv q = e.forward.pullbackRingHom q :=
  rfl

@[simp]
theorem pullbackRingEquiv_symm_apply {n : ℕ} (e : PointedEquivGerm n)
    (q : Germ n) :
    e.pullbackRingEquiv.symm q = e.inverse.pullbackRingHom q :=
  rfl

/-- Pullback by an invertible pointed analytic germ is an equivalence of
complex algebras. -/
@[expose] noncomputable def pullbackAlgEquiv {n : ℕ}
    (e : PointedEquivGerm n) :
    Germ n ≃ₐ[ℂ] Germ n :=
  AlgEquiv.ofRingEquiv (f := e.pullbackRingEquiv) fun c ↦ by
    change e.pullbackRingEquiv (Germ.constRingHom n c) =
      Germ.constRingHom n c
    rw [pullbackRingEquiv_apply, PointedMapGerm.pullback_constRingHom]

@[simp]
theorem pullbackAlgEquiv_apply {n : ℕ} (e : PointedEquivGerm n)
    (q : Germ n) :
    e.pullbackAlgEquiv q = e.pullbackRingEquiv q :=
  rfl

/-- Pullback by an analytic equivalence preserves the maximal ideal. -/
theorem map_maximalIdeal_pullbackRingEquiv {n : ℕ}
    (e : PointedEquivGerm n) :
    Ideal.map e.pullbackRingEquiv.toRingHom (Germ.maximalIdeal n) =
      Germ.maximalIdeal n := by
  have hmax :
      (Ideal.map e.pullbackRingEquiv.toRingHom
        (Germ.maximalIdeal n)).IsMaximal :=
    (Germ.maximalIdeal_isMaximal n).map_bijective
      e.pullbackRingEquiv.toRingHom e.pullbackRingEquiv.bijective
  exact (IsLocalRing.eq_maximalIdeal hmax).trans
    (Germ.maximalIdeal_eq_isLocalRing n).symm

end PointedEquivGerm

namespace PointedMapGerm

/-- The image ring after a source coordinate change is the image of the old
image ring under the induced equivalence of source local rings. -/
theorem map_imageRing_pullbackRingEquiv {n m : ℕ}
    (f : PointedMapGerm n m) (e : PointedEquivGerm n) :
    Subring.map e.pullbackRingEquiv.toRingHom f.ImageRing =
      (f.comp e.forward).ImageRing := by
  have hφ : e.pullbackRingEquiv.toRingHom =
      e.forward.pullbackRingHom := by
    ext q
    rfl
  rw [hφ, RingHom.map_range]
  rw [← PointedMapGerm.pullbackRingHom_comp]

/-- A source coordinate change carries the coordinate ideal to the coordinate
ideal of the transformed map. -/
theorem map_coordinateIdeal_pullbackRingEquiv {n m : ℕ}
    (f : PointedMapGerm n m) (e : PointedEquivGerm n) :
    Ideal.map e.pullbackRingEquiv.toRingHom f.1.coordinateIdeal =
      (f.comp e.forward).1.coordinateIdeal := by
  rw [← f.map_maximalIdeal_eq_coordinateIdeal,
    ← (f.comp e.forward).map_maximalIdeal_eq_coordinateIdeal,
    Ideal.map_map]
  have hφ : e.pullbackRingEquiv.toRingHom =
      e.forward.pullbackRingHom := by
    ext q
    rfl
  rw [hφ, ← PointedMapGerm.pullbackRingHom_comp]

/-- The analytic image rings before and after a source coordinate change are
isomorphic. -/
noncomputable def imageRingSourceEquiv {n m : ℕ}
    (f : PointedMapGerm n m) (e : PointedEquivGerm n) :
    f.ImageRing ≃+* (f.comp e.forward).ImageRing :=
  e.pullbackRingEquiv.subringMap.trans
    (RingEquiv.subringCongr (f.map_imageRing_pullbackRingEquiv e))

@[simp]
theorem coe_imageRingSourceEquiv_apply {n m : ℕ}
    (f : PointedMapGerm n m) (e : PointedEquivGerm n)
    (q : f.ImageRing) :
    ((f.imageRingSourceEquiv e q :
      (f.comp e.forward).ImageRing) : Germ n) =
        e.forward.pullbackRingHom (q : Germ n) := by
  rfl

/-- Finiteness at the origin is preserved by a source coordinate change. -/
theorem isFiniteAtOrigin_sourceEquiv_comp_iff {n m : ℕ}
    (f : PointedMapGerm n m) (e : PointedEquivGerm n) :
    (f.comp e.forward).IsFiniteAtOrigin ↔ f.IsFiniteAtOrigin := by
  constructor
  · intro hfinite
    let _ : Module.Finite (f.comp e.forward).ImageRing (Germ n) := hfinite
    apply Module.Finite.of_equiv_equiv
      (f.imageRingSourceEquiv e).symm e.pullbackRingEquiv.symm
    ext q
    rfl
  · intro hfinite
    let _ : Module.Finite f.ImageRing (Germ n) := hfinite
    apply Module.Finite.of_equiv_equiv
      (f.imageRingSourceEquiv e) e.pullbackRingEquiv
    ext q
    rfl

/-- A target coordinate change does not change the analytic image subring. -/
theorem imageRing_targetEquiv_comp {n m : ℕ}
    (f : PointedMapGerm n m) (e : PointedEquivGerm m) :
    (e.forward.comp f).ImageRing = f.ImageRing := by
  ext q
  constructor
  · rintro ⟨r, hr⟩
    rw [PointedMapGerm.pullbackRingHom_comp] at hr
    exact ⟨e.forward.pullbackRingHom r, hr⟩
  · rintro ⟨r, hr⟩
    rcases e.pullbackRingEquiv.surjective r with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [PointedMapGerm.pullbackRingHom_comp]
    change f.pullbackRingHom (e.forward.pullbackRingHom s) = q
    have hs' : e.forward.pullbackRingHom s = r := by
      simpa only [PointedEquivGerm.pullbackRingEquiv_apply] using hs
    rw [hs']
    exact hr

/-- A target coordinate change leaves the extended coordinate ideal
unchanged. -/
theorem coordinateIdeal_targetEquiv_comp {n m : ℕ}
    (f : PointedMapGerm n m) (e : PointedEquivGerm m) :
    (e.forward.comp f).1.coordinateIdeal = f.1.coordinateIdeal := by
  rw [← (e.forward.comp f).map_maximalIdeal_eq_coordinateIdeal,
    ← f.map_maximalIdeal_eq_coordinateIdeal,
    PointedMapGerm.pullbackRingHom_comp, ← Ideal.map_map]
  have hφ : e.pullbackRingEquiv.toRingHom =
      e.forward.pullbackRingHom := by
    ext q
    rfl
  rw [← hφ, e.map_maximalIdeal_pullbackRingEquiv]

/-- Finiteness at the origin is preserved by a target coordinate change. -/
theorem isFiniteAtOrigin_targetEquiv_comp_iff {n m : ℕ}
    (f : PointedMapGerm n m) (e : PointedEquivGerm m) :
    (e.forward.comp f).IsFiniteAtOrigin ↔ f.IsFiniteAtOrigin := by
  rw [IsFiniteAtOrigin, IsFiniteAtOrigin, f.imageRing_targetEquiv_comp e]

end PointedMapGerm

/-- Right left equivalence preserves finiteness at the origin. -/
theorem PointedMapGerm.RightLeftEquivalent.isFiniteAtOrigin_iff
    {n m : ℕ} {f g : PointedMapGerm n m}
    (hfg : f.RightLeftEquivalent g) :
    g.IsFiniteAtOrigin ↔ f.IsFiniteAtOrigin := by
  rcases hfg with ⟨source, target, rfl⟩
  rw [PointedMapGerm.isFiniteAtOrigin_targetEquiv_comp_iff,
    PointedMapGerm.isFiniteAtOrigin_sourceEquiv_comp_iff]

/-- Under a right left equivalence, the source equivalence carries the first
coordinate ideal to the second coordinate ideal. -/
theorem PointedMapGerm.RightLeftEquivalent.exists_map_coordinateIdeal
    {n m : ℕ} {f g : PointedMapGerm n m}
    (hfg : f.RightLeftEquivalent g) :
    ∃ source : PointedEquivGerm n,
      Ideal.map source.pullbackRingEquiv.toRingHom f.1.coordinateIdeal =
        g.1.coordinateIdeal := by
  rcases hfg with ⟨source, target, rfl⟩
  refine ⟨source, ?_⟩
  rw [PointedMapGerm.coordinateIdeal_targetEquiv_comp]
  exact f.map_coordinateIdeal_pullbackRingEquiv source

end OnLeConjecture.Analytic
