/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Data.EReal.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Spectral thresholds of homology classes in filtered complexes

The filtration consists of increasing submodules preserved by the actual
chain differential. A class is represented below a level when a cycle in
that submodule maps to the class under the ordinary homology projection.
Its spectral threshold is the infimum of these levels in the extended real
numbers. This definition permits unbounded filtrations and unattained
infima. Filtered chain maps and chain homotopy equivalences control the
threshold by their induced maps on ordinary homology.

The construction is algebraic. It does not assert that a complex arises
from a knot, or supply knot invariance or a cobordism estimate.
-/

@[expose] public section

universe u v w

namespace OnLeConjecture.KnotFloer

open CategoryTheory HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type w} {c : ComplexShape ι}

/-- A real filtration by subcomplexes of an ordinary complex of modules. -/
structure RealFiltration (C : HomologicalComplex (ModuleCat.{v} R) c) where
  level : ℝ → ∀ i, Submodule R (C.X i)
  mono : ∀ i, Monotone (fun s => level s i)
  differential_mem : ∀ s i j x, x ∈ level s i → C.d i j x ∈ level s j

namespace RealFiltration

variable {C D E : HomologicalComplex (ModuleCat.{v} R) c}

/-- The complex at a specified filtration level. -/
noncomputable def subcomplex (F : RealFiltration C) (s : ℝ) :
    HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (F.level s i)
  d i j := ModuleCat.ofHom ((C.d i j).hom.restrict (F.differential_mem s i j))
  shape i j hij := by
    ext x
    exact congrArg (fun f : C.X i ⟶ C.X j => f x) (C.shape i j hij)
  d_comp_d' i j k _ _ := by
    ext x
    exact congrArg (fun f : C.X i ⟶ C.X k => f x) (C.d_comp_d i j k)

/-- The inclusion of the filtered subcomplex into the original complex. -/
noncomputable def inclusion (F : RealFiltration C) (s : ℝ) : F.subcomplex s ⟶ C where
  f i := ModuleCat.ofHom (F.level s i).subtype
  comm' _ _ _ := by ext; rfl

/-- A chain map preserves the real filtration if each component carries
every level into the same level. -/
def Preserves (F : RealFiltration C) (G : RealFiltration D) (φ : C ⟶ D) : Prop :=
  ∀ s i x, x ∈ F.level s i → φ.f i x ∈ G.level s i

theorem preserves_id (F : RealFiltration C) : F.Preserves F (𝟙 C) := by
  intro s i x hx
  exact hx

theorem Preserves.comp {F : RealFiltration C} {G : RealFiltration D}
    {H : RealFiltration E} {φ : C ⟶ D} {ψ : D ⟶ E}
    (hφ : F.Preserves G φ) (hψ : G.Preserves H ψ) : F.Preserves H (φ ≫ ψ) := by
  intro s i x hx
  exact hψ s i _ (hφ s i x hx)

/-- A homology class is represented below `s` if it has an actual cycle
representative in filtration level `s`. -/
def RepresentedBelow (F : RealFiltration C) (i : ι) (ξ : C.homology i) (s : ℝ) : Prop :=
  ∃ z : C.cycles i, C.iCycles i z ∈ F.level s i ∧ C.homologyπ i z = ξ

theorem RepresentedBelow.mono {F : RealFiltration C} {i : ι} {ξ : C.homology i}
    {s t : ℝ} (h : F.RepresentedBelow i ξ s) (hst : s ≤ t) :
    F.RepresentedBelow i ξ t := by
  obtain ⟨z, hz, hξ⟩ := h
  exact ⟨z, F.mono i hst hz, hξ⟩

theorem representedBelow_zero (F : RealFiltration C) (i : ι) (s : ℝ) :
    F.RepresentedBelow i 0 s := by
  refine ⟨0, ?_, ?_⟩ <;> simp

/-- The cycle description is exactly the image of homology of the
filtered subcomplex under its inclusion into the full complex. -/
theorem representedBelow_iff_mem_range (F : RealFiltration C) (i : ι)
    (ξ : C.homology i) (s : ℝ) :
    F.RepresentedBelow i ξ s ↔
      ξ ∈ LinearMap.range (homologyMap (F.inclusion s) i).hom := by
  constructor
  · rintro ⟨z, hz, hξ⟩
    let x : (F.subcomplex s).X i := ⟨C.iCycles i z, hz⟩
    have hx : (F.subcomplex s).d i (c.next i) x = 0 := by
      apply Subtype.ext
      exact congrArg (fun f : C.cycles i ⟶ C.X (c.next i) => f z) (C.iCycles_d i (c.next i))
    let w := (F.subcomplex s).cyclesMk x (c.next i) rfl hx
    have hw : (F.subcomplex s).iCycles i w = x := (F.subcomplex s).i_cyclesMk x _ rfl hx
    have hcycles : cyclesMap (F.inclusion s) i w = z := by
      apply (ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance
      have h := congrArg (fun f : (F.subcomplex s).cycles i ⟶ C.X i => f w)
        (cyclesMap_i (F.inclusion s) i)
      change C.iCycles i (cyclesMap (F.inclusion s) i w) =
        (F.inclusion s).f i ((F.subcomplex s).iCycles i w) at h
      rw [hw] at h
      exact h
    refine ⟨(F.subcomplex s).homologyπ i w, ?_⟩
    have h := congrArg (fun f : (F.subcomplex s).cycles i ⟶ C.homology i => f w)
      (homologyπ_naturality (F.inclusion s) i)
    change homologyMap (F.inclusion s) i ((F.subcomplex s).homologyπ i w) =
      C.homologyπ i (cyclesMap (F.inclusion s) i w) at h
    exact h.trans (by rw [hcycles, hξ])
  · rintro ⟨η, hη⟩
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((F.subcomplex s).homologyπ i)).mp
      inferInstance η
    refine ⟨cyclesMap (F.inclusion s) i z, ?_, ?_⟩
    · have h := congrArg (fun f : (F.subcomplex s).cycles i ⟶ C.X i => f z)
        (cyclesMap_i (F.inclusion s) i)
      change C.iCycles i (cyclesMap (F.inclusion s) i z) =
        (F.inclusion s).f i ((F.subcomplex s).iCycles i z) at h
      rw [h]
      exact ((F.subcomplex s).iCycles i z).property
    · have h := congrArg (fun f : (F.subcomplex s).cycles i ⟶ C.homology i => f z)
        (homologyπ_naturality (F.inclusion s) i)
      change homologyMap (F.inclusion s) i ((F.subcomplex s).homologyπ i z) =
        C.homologyπ i (cyclesMap (F.inclusion s) i z) at h
      exact h.symm.trans (by rw [hz]; exact hη)

/-- The extended-real spectral threshold of a fixed homology class. -/
noncomputable def spectralThreshold (F : RealFiltration C) (i : ι) (ξ : C.homology i) : EReal :=
  sInf {a : EReal | ∃ s : ℝ, F.RepresentedBelow i ξ s ∧ a = (s : EReal)}

theorem spectralThreshold_le_of_representedBelow {F : RealFiltration C}
    {i : ι} {ξ : C.homology i} {s : ℝ} (h : F.RepresentedBelow i ξ s) :
    F.spectralThreshold i ξ ≤ (s : EReal) :=
  sInf_le ⟨s, h, rfl⟩

theorem le_spectralThreshold {F : RealFiltration C} {i : ι} {ξ : C.homology i}
    {a : EReal} (h : ∀ s : ℝ, F.RepresentedBelow i ξ s → a ≤ (s : EReal)) :
    a ≤ F.spectralThreshold i ξ := by
  apply le_sInf
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

/-- Exhaustivity ensures every homology class has a representative at
some finite filtration level. -/
theorem exists_representedBelow_of_exhaustive (F : RealFiltration C) (i : ι)
    (hexhaustive : ∀ x : C.X i, ∃ s : ℝ, x ∈ F.level s i) (ξ : C.homology i) :
    ∃ s : ℝ, F.RepresentedBelow i ξ s := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ i)).mp inferInstance ξ
  obtain ⟨s, hs⟩ := hexhaustive (C.iCycles i z)
  exact ⟨s, z, hs, hz⟩

theorem spectralThreshold_lt_top_of_exhaustive (F : RealFiltration C) (i : ι)
    (hexhaustive : ∀ x : C.X i, ∃ s : ℝ, x ∈ F.level s i) (ξ : C.homology i) :
    F.spectralThreshold i ξ < ⊤ := by
  obtain ⟨s, hs⟩ := F.exists_representedBelow_of_exhaustive i hexhaustive ξ
  exact (spectralThreshold_le_of_representedBelow hs).trans_lt (EReal.coe_lt_top s)

/-- Vanishing of all chain groups below a specified level gives a lower
bound for the threshold of each nonzero homology class. -/
theorem le_spectralThreshold_of_level_eq_bot (F : RealFiltration C) (i : ι)
    (ξ : C.homology i) (hξ : ξ ≠ 0) (a : ℝ)
    (hlevel : ∀ s : ℝ, s < a → F.level s i = ⊥) :
    (a : EReal) ≤ F.spectralThreshold i ξ := by
  apply le_spectralThreshold
  intro s hs
  apply EReal.coe_le_coe
  by_contra h
  obtain ⟨z, hz, hclass⟩ := hs
  rw [hlevel s (lt_of_not_ge h), Submodule.mem_bot] at hz
  have hz0 : z = 0 := (ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance
    (by simpa using hz)
  exact hξ (by simpa [hz0] using hclass.symm)

/-- An exhaustive filtration bounded below in the selected chain degree
has a finite real threshold for every nonzero homology class. -/
theorem exists_real_spectralThreshold (F : RealFiltration C) (i : ι)
    (ξ : C.homology i) (hξ : ξ ≠ 0)
    (hexhaustive : ∀ x : C.X i, ∃ s : ℝ, x ∈ F.level s i)
    (a : ℝ) (hlevel : ∀ s : ℝ, s < a → F.level s i = ⊥) :
    ∃ b : ℝ, F.spectralThreshold i ξ = (b : EReal) := by
  have htop := F.spectralThreshold_lt_top_of_exhaustive i hexhaustive ξ
  have hbot : ⊥ < F.spectralThreshold i ξ :=
    (EReal.bot_lt_coe a).trans_le (F.le_spectralThreshold_of_level_eq_bot i ξ hξ a hlevel)
  exact ⟨(F.spectralThreshold i ξ).toReal, (EReal.coe_toReal htop.ne hbot.ne').symm⟩

/-- A filtered chain map sends a filtered cycle representative to a
filtered representative of the induced homology class. -/
theorem RepresentedBelow.map {F : RealFiltration C} {G : RealFiltration D}
    {φ : C ⟶ D} (hφ : F.Preserves G φ) {i : ι} {ξ : C.homology i} {s : ℝ}
    (h : F.RepresentedBelow i ξ s) :
    G.RepresentedBelow i (homologyMap φ i ξ) s := by
  obtain ⟨z, hz, hξ⟩ := h
  refine ⟨cyclesMap φ i z, ?_, ?_⟩
  · have hcycles := congrArg (fun f : C.cycles i ⟶ D.X i => f z) (cyclesMap_i φ i)
    change D.iCycles i (cyclesMap φ i z) = φ.f i (C.iCycles i z) at hcycles
    rw [hcycles]
    exact hφ s i _ hz
  · have hhomology := congrArg (fun f : C.cycles i ⟶ D.homology i => f z)
      (homologyπ_naturality φ i)
    exact hhomology.symm.trans (congrArg (homologyMap φ i) hξ)

/-- A filtration-preserving chain map cannot increase the threshold of
the class that it induces on homology. -/
theorem spectralThreshold_map_le {F : RealFiltration C} {G : RealFiltration D}
    {φ : C ⟶ D} (hφ : F.Preserves G φ) (i : ι) (ξ : C.homology i) :
    G.spectralThreshold i (homologyMap φ i ξ) ≤ F.spectralThreshold i ξ := by
  apply le_spectralThreshold
  intro s hs
  exact spectralThreshold_le_of_representedBelow (hs.map hφ)

/-- Filtration-preserving maps inverse on the selected homology class
give equal spectral thresholds. -/
theorem spectralThreshold_eq_of_maps
    {F : RealFiltration C} {G : RealFiltration D} {φ : C ⟶ D} {ψ : D ⟶ C}
    (hφ : F.Preserves G φ) (hψ : G.Preserves F ψ)
    (i : ι) (ξ : C.homology i)
    (hinverse : homologyMap ψ i (homologyMap φ i ξ) = ξ) :
    G.spectralThreshold i (homologyMap φ i ξ) = F.spectralThreshold i ξ := by
  apply le_antisymm (spectralThreshold_map_le hφ i ξ)
  have h := spectralThreshold_map_le hψ i (homologyMap φ i ξ)
  rwa [hinverse] at h

/-- A chain homotopy equivalence whose two chain maps preserve filtration
preserves the spectral threshold. No assumption about homotopy filtration
is needed for this conclusion about ordinary homology classes. -/
theorem spectralThreshold_eq_of_homotopyEquiv
    {F : RealFiltration C} {G : RealFiltration D}
    (e : HomotopyEquiv C D) (he : F.Preserves G e.hom) (heinv : G.Preserves F e.inv)
    (i : ι) (ξ : C.homology i) :
    G.spectralThreshold i (homologyMap e.hom i ξ) = F.spectralThreshold i ξ := by
  apply spectralThreshold_eq_of_maps he heinv i ξ
  have h := e.toHomologyIso i |>.hom_inv_id
  exact congrArg (fun f : C.homology i ⟶ C.homology i => f ξ) h

end RealFiltration

/-- An increasing bifiltration of the chain modules preserved by the
differential. -/
structure Bifiltration (C : HomologicalComplex (ModuleCat.{v} R) c) where
  level : ℝ → ℝ → ∀ i, Submodule R (C.X i)
  mono : ∀ i a b a' b', a ≤ a' → b ≤ b' → level a b i ≤ level a' b' i
  differential_mem : ∀ a b i j x, x ∈ level a b i → C.d i j x ∈ level a b j

namespace Bifiltration

variable {C : HomologicalComplex (ModuleCat.{v} R) c}

/-- The real filtration obtained by taking spans of bifiltered elements
with weighted level `(1 - t/2) a + (t/2) b ≤ s`. In the Upsilon convention,
the parameter lies in `[0,2]`. The construction itself is defined for all
real parameters. -/
noncomputable def weighted (F : Bifiltration C) (t : ℝ) : RealFiltration C where
  level s i := Submodule.span R {x | ∃ a b : ℝ,
    x ∈ F.level a b i ∧ (1 - t / 2) * a + (t / 2) * b ≤ s}
  mono i s u hsu := Submodule.span_mono (by
    rintro x ⟨a, b, hx, hbound⟩
    exact ⟨a, b, hx, hbound.trans hsu⟩)
  differential_mem s i j x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, b, hx, hbound⟩ := hx
      exact Submodule.subset_span ⟨a, b, F.differential_mem a b i j x hx, hbound⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

end Bifiltration

end OnLeConjecture.KnotFloer
