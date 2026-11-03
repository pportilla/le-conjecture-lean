/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.SpectralShift

/-!
# Weighted spectral functions of bifiltered complexes

The algebraic class-Upsilon function is minus twice the spectral threshold
of a specified homology class under the weighted real filtration. This
file proves its invariance under bifiltration-preserving chain homotopy
equivalences by mapping actual cycle representatives.

No knot complex, distinguished knot homology generator, or relation with
a geometric cobordism is asserted here. Those constructions are separate
requirements for interpreting this algebraic function as a knot invariant.
-/

@[expose] public section

universe u v w

namespace OnLeConjecture.KnotFloer.Bifiltration

open CategoryTheory HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type w} {c : ComplexShape ι}
variable {C D : HomologicalComplex (ModuleCat.{v} R) c}

/-- A chain map preserves both filtration coordinates. -/
def Preserves (F : Bifiltration C) (G : Bifiltration D) (φ : C ⟶ D) : Prop :=
  ∀ a b i x, x ∈ F.level a b i → φ.f i x ∈ G.level a b i

/-- Preservation of the two filtrations preserves every weighted real
filtration because a linear chain map carries each spanning generator to
one with the same admissible pair of filtration coordinates. -/
theorem Preserves.weighted {F : Bifiltration C} {G : Bifiltration D}
    {φ : C ⟶ D} (hφ : F.Preserves G φ) (t : ℝ) :
    (F.weighted t).Preserves (G.weighted t) φ := by
  intro s i x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, hx, hbound⟩ := hx
    exact Submodule.subset_span ⟨a, b, hφ a b i x hx, hbound⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

/-- The class-Upsilon function of a bifiltered complex and a fixed ordinary
homology class. For the knot-theoretic convention the class must be the
specified nonzero generator, and the parameter lies in `[0,2]`. -/
noncomputable def classUpsilon (F : Bifiltration C) (i : ι) (ξ : C.homology i)
    (t : ℝ) : EReal :=
  -(2 * (F.weighted t).spectralThreshold i ξ)

/-- The weighted spectral thresholds are invariant under a bifiltered
chain homotopy equivalence. -/
theorem weighted_spectralThreshold_eq_of_homotopyEquiv
    {F : Bifiltration C} {G : Bifiltration D}
    (e : HomotopyEquiv C D) (he : F.Preserves G e.hom) (heinv : G.Preserves F e.inv)
    (i : ι) (ξ : C.homology i) (t : ℝ) :
    (G.weighted t).spectralThreshold i (homologyMap e.hom i ξ) =
      (F.weighted t).spectralThreshold i ξ :=
  RealFiltration.spectralThreshold_eq_of_homotopyEquiv e (he.weighted t) (heinv.weighted t) i ξ

/-- Invariance of the algebraic class-Upsilon function follows from the
proved invariance of the weighted spectral thresholds. -/
theorem classUpsilon_eq_of_homotopyEquiv
    {F : Bifiltration C} {G : Bifiltration D}
    (e : HomotopyEquiv C D) (he : F.Preserves G e.hom) (heinv : G.Preserves F e.inv)
    (i : ι) (ξ : C.homology i) (t : ℝ) :
    G.classUpsilon i (homologyMap e.hom i ξ) t = F.classUpsilon i ξ t := by
  unfold classUpsilon
  rw [weighted_spectralThreshold_eq_of_homotopyEquiv e he heinv]

end OnLeConjecture.KnotFloer.Bifiltration
