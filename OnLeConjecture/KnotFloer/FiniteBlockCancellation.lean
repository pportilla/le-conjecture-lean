/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.SpecialContractionProduct
import Mathlib.Tactic.Abel

/-!
# Cancellation of an invertible differential block

The three coordinates are retained generators, matching sources, and matching
targets. The inverse of the actual source-to-target block determines the
homotopy, corrected maps, and transferred differential. No filtration bound
or identification of the transferred differential is part of this algebra.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.FiniteBlockCancellation
open TauCeti

variable {S N P : Type*} [CommRing S]
  [AddCommGroup N] [Module S N] [AddCommGroup P] [Module S P]

abbrev ThreeBlocks (N P : Type*) := N × (P × P)

def retainedInclusion : N →ₗ[S] ThreeBlocks N P where
  toFun c := (c, (0, 0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def retainedProjection : ThreeBlocks N P →ₗ[S] N := LinearMap.fst _ _ _

def sourceInclusion : P →ₗ[S] ThreeBlocks N P where
  toFun s := (0, (s, 0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def targetProjection : ThreeBlocks N P →ₗ[S] P :=
  LinearMap.snd _ _ _ ∘ₗ LinearMap.snd _ _ _

variable (D : Module.End S (ThreeBlocks N P)) (B : P ≃ₗ[S] P)

/-- Reverse the actual invertible matching block. -/
def homotopy : Module.End S (ThreeBlocks N P) :=
  sourceInclusion ∘ₗ B.symm.toLinearMap ∘ₗ targetProjection

def correctedInclusion : N →ₗ[S] ThreeBlocks N P :=
  (LinearMap.id - homotopy B ∘ₗ D) ∘ₗ retainedInclusion

def correctedProjection : ThreeBlocks N P →ₗ[S] N :=
  retainedProjection ∘ₗ (LinearMap.id - D ∘ₗ homotopy B)

/-- The direct retained block minus the paths through the inverse matching block. -/
def transferredDifferential : Module.End S N :=
  retainedProjection ∘ₗ D ∘ₗ correctedInclusion D B

@[simp] theorem homotopy_apply (v : ThreeBlocks N P) :
    homotopy B v = (0, (B.symm v.2.2, 0)) := rfl

theorem homotopy_comp_self : homotopy (N := N) B ∘ₗ homotopy B = 0 := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, homotopy_apply, LinearMap.zero_apply, map_zero, Prod.zero_eq_mk]

theorem homotopy_retainedInclusion :
    homotopy B ∘ₗ (retainedInclusion : N →ₗ[S] ThreeBlocks N P) = 0 := by
  apply LinearMap.ext
  intro v
  simp [LinearMap.comp_apply, retainedInclusion]

theorem retainedProjection_homotopy :
    (retainedProjection : ThreeBlocks N P →ₗ[S] N) ∘ₗ homotopy B = 0 := by
  apply LinearMap.ext
  intro v
  simp [LinearMap.comp_apply, retainedProjection]

/-- The transferred operator is the exact Schur complement of the matching block. -/
theorem transferredDifferential_eq_schur :
    transferredDifferential D B =
      retainedProjection ∘ₗ D ∘ₗ retainedInclusion -
        retainedProjection ∘ₗ D ∘ₗ homotopy B ∘ₗ D ∘ₗ retainedInclusion := by
  apply LinearMap.ext
  intro c
  simp only [transferredDifferential, correctedInclusion, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub]

variable (hB : ∀ s, (D (0, (s, 0))).2.2 = B s)
include hB

theorem homotopy_D_source (s : P) :
    homotopy B (D (0, (s, 0))) = (0, (s, 0)) := by
  simp [hB]

theorem target_corrected (v : ThreeBlocks N P) :
    (v - D (homotopy B v)).2.2 = 0 := by
  simp only [homotopy_apply, Prod.snd_sub]
  rw [hB, B.apply_symm_apply, sub_self]

theorem homotopy_D_homotopy :
    homotopy B ∘ₗ D ∘ₗ homotopy (N := N) B = homotopy B := by
  apply LinearMap.ext
  intro v
  simp [LinearMap.comp_apply, hB]

omit hB in
theorem projection_inclusion :
    correctedProjection D B ∘ₗ correctedInclusion D B = LinearMap.id := by
  apply LinearMap.ext
  intro c
  simp only [correctedProjection, correctedInclusion, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.id_apply, retainedInclusion, homotopy_apply,
    retainedProjection, LinearMap.fst_apply, LinearMap.coe_mk, AddHom.coe_mk,
    map_sub, map_zero, zero_sub]
  abel

variable (hD : D ∘ₗ D = 0)
include hD

theorem inclusion_projection :
    correctedInclusion D B ∘ₗ correctedProjection D B =
      LinearMap.id - (D ∘ₗ homotopy B + homotopy B ∘ₗ D) := by
  let f : Module.End S (ThreeBlocks N P) := LinearMap.id - D ∘ₗ homotopy B
  let q : Module.End S (ThreeBlocks N P) := LinearMap.id - homotopy B ∘ₗ D
  have hzero (s : P) : q (sourceInclusion (S := S) (N := N) s) = 0 := by
    change (0, (s, 0)) - homotopy B (D (0, (s, 0))) = 0
    rw [homotopy_D_source D B hB, sub_self]
  have hdecomp (v : ThreeBlocks N P) :
      f v = retainedInclusion (S := S) ((f v).1) + sourceInclusion (S := S) ((f v).2.1) := by
    have ht := target_corrected D B hB v
    change (f v).2.2 = 0 at ht
    apply Prod.ext
    · simp [retainedInclusion, sourceInclusion]
    · apply Prod.ext
      · simp [retainedInclusion, sourceInclusion]
      · simpa [retainedInclusion, sourceInclusion] using ht
  have heq : correctedInclusion D B ∘ₗ correctedProjection D B = q ∘ₗ f := by
    apply LinearMap.ext
    intro v
    change q (retainedInclusion (S := S) ((f v).1)) = q (f v)
    have hh := congrArg q (hdecomp v)
    simp only [map_add, hzero, add_zero] at hh
    exact hh.symm
  rw [heq]
  apply LinearMap.ext
  intro v
  have hDD (x : ThreeBlocks N P) : D (D x) = 0 := LinearMap.congr_fun hD x
  simp only [q, f, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.id_apply, map_sub, hDD, map_zero, sub_zero]
  abel

omit hB hD in
theorem homotopy_correctedInclusion :
    homotopy B ∘ₗ correctedInclusion D B = 0 := by
  apply LinearMap.ext
  intro c
  simp [correctedInclusion, LinearMap.comp_apply, retainedInclusion, Prod.zero_eq_mk]

omit hB hD in
theorem correctedProjection_homotopy :
    correctedProjection D B ∘ₗ homotopy B = 0 := by
  apply LinearMap.ext
  intro v
  have hh := LinearMap.congr_fun (homotopy_comp_self (N := N) B) v
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hh
  change retainedProjection (S := S) (homotopy B v - D (homotopy B (homotopy B v))) = 0
  rw [hh, map_zero, sub_zero]
  rfl

omit hD in
theorem homotopy_D_inclusion :
    homotopy B ∘ₗ D ∘ₗ correctedInclusion D B = 0 := by
  apply LinearMap.ext
  intro c
  simp only [correctedInclusion, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, LinearMap.zero_apply]
  have hh := LinearMap.congr_fun (homotopy_D_homotopy D B hB)
    (D (retainedInclusion (S := S) c))
  simp only [LinearMap.comp_apply] at hh
  rw [hh, sub_self]

omit hD in
theorem projection_D_inclusion :
    correctedProjection D B ∘ₗ D ∘ₗ correctedInclusion D B =
      transferredDifferential D B := by
  apply LinearMap.ext
  intro c
  have hh := LinearMap.congr_fun (homotopy_D_inclusion D B hB) c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hh
  change retainedProjection (S := S) (D (correctedInclusion D B c) -
      D (homotopy B (D (correctedInclusion D B c)))) =
    retainedProjection (S := S) (D (correctedInclusion D B c))
  rw [hh, map_zero, sub_zero]

private theorem D_projector_apply (v : ThreeBlocks N P) :
    D (correctedInclusion D B (correctedProjection D B v)) =
      correctedInclusion D B (correctedProjection D B (D v)) := by
  have hDD (x : ThreeBlocks N P) : D (D x) = 0 :=
    LinearMap.congr_fun hD x
  change (D ∘ₗ (correctedInclusion D B ∘ₗ correctedProjection D B)) v =
    ((correctedInclusion D B ∘ₗ correctedProjection D B) ∘ₗ D) v
  rw [inclusion_projection D B hB hD]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.id_apply, map_sub, map_add, hDD, map_zero, zero_add, add_zero]

theorem D_inclusion :
    D ∘ₗ correctedInclusion D B = correctedInclusion D B ∘ₗ transferredDifferential D B := by
  apply LinearMap.ext
  intro c
  have hi (x : N) : correctedProjection D B (correctedInclusion D B x) = x :=
    LinearMap.congr_fun (projection_inclusion D B) x
  have ht (x : N) : correctedProjection D B (D (correctedInclusion D B x)) =
      transferredDifferential D B x := LinearMap.congr_fun (projection_D_inclusion D B hB) x
  change D (correctedInclusion D B c) = correctedInclusion D B (transferredDifferential D B c)
  calc
    _ = D (correctedInclusion D B (correctedProjection D B (correctedInclusion D B c))) := by
      rw [hi]
    _ = correctedInclusion D B (correctedProjection D B (D (correctedInclusion D B c))) :=
      D_projector_apply D B hB hD _
    _ = _ := by rw [ht]

theorem projection_D :
    correctedProjection D B ∘ₗ D = transferredDifferential D B ∘ₗ correctedProjection D B := by
  apply LinearMap.ext
  intro v
  have hi (x : N) : correctedProjection D B (correctedInclusion D B x) = x :=
    LinearMap.congr_fun (projection_inclusion D B) x
  have ht (x : N) : correctedProjection D B (D (correctedInclusion D B x)) =
      transferredDifferential D B x := LinearMap.congr_fun (projection_D_inclusion D B hB) x
  change correctedProjection D B (D v) = transferredDifferential D B (correctedProjection D B v)
  calc
    _ = correctedProjection D B (correctedInclusion D B (correctedProjection D B (D v))) := by
      rw [hi]
    _ = correctedProjection D B (D (correctedInclusion D B (correctedProjection D B v))) :=
      congrArg (correctedProjection D B) (D_projector_apply D B hB hD v).symm
    _ = _ := ht _

theorem transferredDifferential_comp_self :
    transferredDifferential D B ∘ₗ transferredDifferential D B = 0 := by
  apply LinearMap.ext
  intro c
  have hi (x : N) : D (correctedInclusion D B x) =
      correctedInclusion D B (transferredDifferential D B x) :=
    LinearMap.congr_fun (D_inclusion D B hB hD) x
  have ht (x : N) : correctedProjection D B (D (correctedInclusion D B x)) =
      transferredDifferential D B x := LinearMap.congr_fun (projection_D_inclusion D B hB) x
  have hDD (x : ThreeBlocks N P) : D (D x) = 0 := LinearMap.congr_fun hD x
  change transferredDifferential D B (transferredDifferential D B c) = 0
  calc
    _ = correctedProjection D B (D (correctedInclusion D B (transferredDifferential D B c))) :=
      (ht _).symm
    _ = correctedProjection D B (D (D (correctedInclusion D B c))) := by rw [← hi]
    _ = 0 := by rw [hDD, map_zero]

/-- The actual invertible block supplies every special-contraction identity. -/
def toSpecialContraction : LinearSpecialContraction D (transferredDifferential D B) where
  incl := correctedInclusion D B
  proj := correctedProjection D B
  homotopy := homotopy B
  dM_comp_incl := D_inclusion D B hB hD
  proj_comp_dM := projection_D D B hB hD
  proj_comp_incl := projection_inclusion D B
  dM_comp_homotopy_add_homotopy_comp_dM := by
    rw [inclusion_projection D B hB hD]
    abel
  homotopy_comp_incl := homotopy_correctedInclusion D B
  proj_comp_homotopy := correctedProjection_homotopy D B
  homotopy_comp_homotopy := homotopy_comp_self B

end OnLeConjecture.KnotFloer.FiniteBlockCancellation
