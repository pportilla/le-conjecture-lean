/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.SpectralThreshold
public import Mathlib.Data.EReal.Operations
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Tactic.Linarith

/-!
# Filtration shifts and spectral comparison

A chain map that increases every filtration level by at most a real
constant increases the spectral threshold by at most that constant.
Maps in both directions which are inverse on a selected homology class
therefore give a two-sided comparison. For finite thresholds this is an
ordinary absolute-value bound.
-/

@[expose] public section

universe u v w

namespace OnLeConjecture.KnotFloer

open CategoryTheory HomologicalComplex

/-- Translation of the extended real line by a finite real constant. -/
noncomputable def realTranslate (r : ℝ) : EReal ≃o EReal where
  toFun x := x + (r : EReal)
  invFun x := x + ((-r : ℝ) : EReal)
  left_inv x := by dsimp only; rw [add_assoc, ← EReal.coe_add]; simp
  right_inv x := by dsimp only; rw [add_assoc, ← EReal.coe_add]; simp
  map_rel_iff' := (EReal.addLECancellable_coe r).add_le_add_iff_right

namespace RealFiltration

variable {R : Type u} [CommRing R] {ι : Type w} {c : ComplexShape ι}
variable {C D : HomologicalComplex (ModuleCat.{v} R) c}

/-- A chain map shifts filtration by at most `r`. -/
def Shifts (F : RealFiltration C) (G : RealFiltration D) (φ : C ⟶ D) (r : ℝ) : Prop :=
  ∀ s i x, x ∈ F.level s i → φ.f i x ∈ G.level (s + r) i

theorem shifts_zero_iff {F : RealFiltration C} {G : RealFiltration D} {φ : C ⟶ D} :
    F.Shifts G φ 0 ↔ F.Preserves G φ := by
  simp [Shifts, Preserves]

theorem RepresentedBelow.map_shift {F : RealFiltration C} {G : RealFiltration D}
    {φ : C ⟶ D} {r : ℝ} (hφ : F.Shifts G φ r)
    {i : ι} {ξ : C.homology i} {s : ℝ} (h : F.RepresentedBelow i ξ s) :
    G.RepresentedBelow i (homologyMap φ i ξ) (s + r) := by
  obtain ⟨z, hz, hξ⟩ := h
  refine ⟨cyclesMap φ i z, ?_, ?_⟩
  · have hcycles := congrArg (fun f : C.cycles i ⟶ D.X i => f z) (cyclesMap_i φ i)
    change D.iCycles i (cyclesMap φ i z) = φ.f i (C.iCycles i z) at hcycles
    rw [hcycles]
    exact hφ s i _ hz
  · have hhomology := congrArg (fun f : C.cycles i ⟶ D.homology i => f z)
      (homologyπ_naturality φ i)
    exact hhomology.symm.trans (congrArg (homologyMap φ i) hξ)

/-- A filtration shift bounds the change in spectral threshold, including
infinite thresholds and infima which are not attained. -/
theorem spectralThreshold_map_le_add {F : RealFiltration C} {G : RealFiltration D}
    {φ : C ⟶ D} {r : ℝ} (hφ : F.Shifts G φ r) (i : ι) (ξ : C.homology i) :
    G.spectralThreshold i (homologyMap φ i ξ) ≤ F.spectralThreshold i ξ + (r : EReal) := by
  change G.spectralThreshold i (homologyMap φ i ξ) ≤
    realTranslate r (sInf {a : EReal | ∃ s : ℝ, F.RepresentedBelow i ξ s ∧ a = (s : EReal)})
  rw [map_sInf]
  apply le_sInf
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  exact (spectralThreshold_le_of_representedBelow (hs.map_shift hφ) :
    G.spectralThreshold i (homologyMap φ i ξ) ≤ ((s + r : ℝ) : EReal))

/-- Shifting all filtration levels by a constant. -/
noncomputable def shift (F : RealFiltration C) (r : ℝ) : RealFiltration C where
  level s i := F.level (s - r) i
  mono i _ _ h := F.mono i (sub_le_sub_right h r)
  differential_mem s i j x hx := F.differential_mem (s - r) i j x hx

theorem spectralThreshold_shift (F : RealFiltration C) (r : ℝ) (i : ι) (ξ : C.homology i) :
    (F.shift r).spectralThreshold i ξ = F.spectralThreshold i ξ + (r : EReal) := by
  have hforward : F.Shifts (F.shift r) (𝟙 C) r := by
    intro s j x hx
    change x ∈ F.level (s + r - r) j
    simpa only [add_sub_cancel_right] using hx
  have hback : (F.shift r).Shifts F (𝟙 C) (-r) := by
    intro s j x hx
    exact hx
  have hle := spectralThreshold_map_le_add hforward i ξ
  have hge := spectralThreshold_map_le_add hback i ξ
  simp only [homologyMap_id, ModuleCat.id_apply] at hle hge
  apply le_antisymm hle
  have h : F.spectralThreshold i ξ + (r : EReal) ≤
      ((F.shift r).spectralThreshold i ξ + ((-r : ℝ) : EReal)) + (r : EReal) :=
    add_le_add hge le_rfl
  simpa only [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] using h

/-- Two shifted chain maps inverse on a homology class give a symmetric
comparison of its spectral thresholds. -/
theorem spectralThreshold_comparison_of_maps
    {F : RealFiltration C} {G : RealFiltration D} {φ : C ⟶ D} {ψ : D ⟶ C}
    {r : ℝ} (hφ : F.Shifts G φ r) (hψ : G.Shifts F ψ r)
    (i : ι) (ξ : C.homology i)
    (hinverse : homologyMap ψ i (homologyMap φ i ξ) = ξ) :
    G.spectralThreshold i (homologyMap φ i ξ) ≤ F.spectralThreshold i ξ + (r : EReal) ∧
      F.spectralThreshold i ξ ≤ G.spectralThreshold i (homologyMap φ i ξ) + (r : EReal) := by
  refine ⟨spectralThreshold_map_le_add hφ i ξ, ?_⟩
  have h := spectralThreshold_map_le_add hψ i (homologyMap φ i ξ)
  rwa [hinverse] at h

/-- For finite spectral thresholds, the symmetric comparison is the
usual absolute-value estimate. -/
theorem abs_sub_le_of_shifted_maps
    {F : RealFiltration C} {G : RealFiltration D} {φ : C ⟶ D} {ψ : D ⟶ C}
    {r : ℝ} (hφ : F.Shifts G φ r) (hψ : G.Shifts F ψ r)
    (i : ι) (ξ : C.homology i)
    (hinverse : homologyMap ψ i (homologyMap φ i ξ) = ξ)
    {a b : ℝ} (ha : F.spectralThreshold i ξ = (a : EReal))
    (hb : G.spectralThreshold i (homologyMap φ i ξ) = (b : EReal)) :
    |a - b| ≤ r := by
  obtain ⟨hab, hba⟩ := spectralThreshold_comparison_of_maps hφ hψ i ξ hinverse
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at hab hba
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end RealFiltration

end OnLeConjecture.KnotFloer
