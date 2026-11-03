/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullBifiltration
public import OnLeConjecture.KnotFloer.GridFullMaslovComplex

/-!
# The bifiltration of the integer-graded full grid complex

Restricting the two monomial-coordinate bounds to the Maslov homogeneous pieces supplies
a bifiltration of the genuine integer-graded full polynomial grid complex over the base ring.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R]

/-- The two-coordinate submodule in a fixed Maslov degree. -/
noncomputable def maslovBifiltrationLevel (a b : ℝ) (m : ℤ) :
    Submodule R (maslovPiece G R m) :=
  ((bifiltrationLevel G R a b).restrictScalars R).comap (maslovPiece G R m).subtype

/-- Exact coefficient bounds for a homogeneous chain at a bifiltration level. -/
theorem mem_maslovBifiltrationLevel_iff (a b : ℝ) (m : ℤ) (c : maslovPiece G R m) :
    c ∈ maslovBifiltrationLevel G R a b m ↔
      ∀ x e, e ∈ ((c : GridChainMinus R n) x).support →
        -(exponentSize e : ℝ) ≤ a ∧ (G.alexander x : ℝ) - exponentSize e ≤ b :=
  mem_bifiltrationLevel_iff G R a b c

variable [CharP R 2]

/-- Identify a native Maslov complex object with its homogeneous polynomial chain submodule. -/
noncomputable def maslovChainEquiv (m : ℤ) :
    (maslovComplex G R).X m ≃ₗ[R] maslovPiece G R m :=
  (eqToIso (maslovComplex_X G R m)).toLinearEquiv

/-- The native graded differential is the full rectangle map on the underlying chains. -/
theorem maslovChainEquiv_d (m : ℤ) (c : (maslovComplex G R).X (m + 1)) :
    (maslovChainEquiv G R m ((maslovComplex G R).d (m + 1) m c) : GridChainMinus R n) =
      differential G R (maslovChainEquiv G R (m + 1) c) := by
  have h : maslovChainEquiv G R m ((maslovComplex G R).d (m + 1) m c) =
      gradedDifferential G R m (maslovChainEquiv G R (m + 1) c) := by
    change (eqToHom (maslovComplex_X G R m)) ((maslovComplex G R).d (m + 1) m c) =
      gradedDifferential G R m ((eqToHom (maslovComplex_X G R (m + 1))) c)
    rw [maslovComplex_d]
    simp only [ModuleCat.comp_apply]
    rw [← ModuleCat.comp_apply, Category.assoc, eqToHom_trans]
    simp
  exact congrArg Subtype.val h

/-- The full polynomial grid complex with its Maslov grading and both filtration coordinates. -/
noncomputable def maslovBifiltration : Bifiltration (maslovComplex G R) where
  level a b m := (maslovBifiltrationLevel G R a b m).comap
    (maslovChainEquiv G R m).toLinearMap
  mono m _ _ _ _ ha hb := Submodule.comap_mono
    (Submodule.comap_mono (bifiltrationLevel_mono G R ha hb))
  differential_mem a b i j c hc := by
    by_cases h : j + 1 = i
    · subst i
      change (maslovChainEquiv G R j ((maslovComplex G R).d (j + 1) j c) :
        GridChainMinus R n) ∈ bifiltrationLevel G R a b
      rw [maslovChainEquiv_d]
      exact differential_mem_bifiltrationLevel G R a b (maslovChainEquiv G R (j + 1) c) hc
    · have hrel : ¬ (ComplexShape.down ℤ).Rel i j := by
        simpa only [ComplexShape.down_Rel] using h
      rw [(maslovComplex G R).shape i j hrel]
      exact Submodule.zero_mem _

/-- Every homogeneous chain lies in a finite bifiltration level. -/
theorem maslovBifiltration_exhaustive (m : ℤ) (c : (maslovComplex G R).X m) :
    ∃ a b : ℝ, c ∈ (maslovBifiltration G R).level a b m :=
  ⟨0, alexanderBound G, mem_bifiltrationLevel_bound G R (maslovChainEquiv G R m c)⟩

end OnLeConjecture.KnotFloer.GridFull
