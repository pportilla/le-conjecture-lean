/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationHomotopy
import Mathlib.Tactic.LinearCombination

/-!
# Filtered chain homotopy equivalence under adjacent column commutation

The full pentagon maps in both directions and the geometric hexagon homotopies give an
explicit homotopy equivalence of the integer-graded Laurent complexes. Both maps and both
homotopies preserve the two real filtration coordinates. Each homology class therefore has
the same weighted spectral threshold and algebraic class-Upsilon value after commutation.

These statements concern a validated column commutation and every specified homology class.
They do not select a distinguished knot class or prove stabilization invariance.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The geometric hexagon component, extended by zero off degree one. -/
noncomputable def laurentMaslovHexagonComponent (C : GridDiagram.ColumnCommutationData G)
    (i j : ℤ) : (laurentMaslovComplex G R).X i ⟶ (laurentMaslovComplex G R).X j :=
  if h : j = i + 1 then by
    subst j
    exact ModuleCat.ofHom (laurentCommutationHexagonPieceMap G R C i)
  else 0

@[simp]
theorem laurentMaslovHexagonComponent_succ (C : GridDiagram.ColumnCommutationData G) (i : ℤ) :
    laurentMaslovHexagonComponent G R C i (i + 1) =
      ModuleCat.ofHom (laurentCommutationHexagonPieceMap G R C i) := by
  simp [laurentMaslovHexagonComponent]

/-- On adjacent degrees, the native component is the concrete full geometric hexagon map. -/
theorem laurentMaslovChainEquiv_hexagon (C : GridDiagram.ColumnCommutationData G) (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovChainEquiv G R (m + 1)
      (laurentMaslovHexagonComponent G R C m (m + 1) c) : LaurentChain R n) =
        laurentCommutationHexagonMap G R C (laurentMaslovChainEquiv G R m c) := by
  rw [laurentMaslovHexagonComponent_succ]
  rfl

/-- The forward native chain map agrees with its concrete polygon count. -/
theorem laurentMaslovChainEquiv_commutation (C : GridDiagram.ColumnCommutationData G) (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovChainEquiv (G.swapColumns C.column (finRotate n C.column)) R m
      ((laurentMaslovCommutationHom G R C).f m c) : LaurentChain R n) =
        laurentCommutationMap G R C (laurentMaslovChainEquiv G R m c) := rfl

/-- The reverse native chain map agrees with the opposite-turn polygon count. -/
theorem laurentMaslovChainEquiv_reverseCommutation
    (C : GridDiagram.ColumnCommutationData G) (m : ℤ)
    (c : (laurentMaslovComplex (G.swapColumns C.column (finRotate n C.column)) R).X m) :
    (laurentMaslovChainEquiv G R m
      ((laurentMaslovReverseCommutationHom G R C).f m c) : LaurentChain R n) =
        laurentReverseCommutationMap G R C
          (laurentMaslovChainEquiv (G.swapColumns C.column (finRotate n C.column)) R m c) := rfl

/-- Off the reversed chain shape, the geometric homotopy component is zero. -/
theorem laurentMaslovHexagonComponent_zero (C : GridDiagram.ColumnCommutationData G)
    (i j : ℤ) (h : ¬(ComplexShape.down ℤ).Rel j i) :
    laurentMaslovHexagonComponent G R C i j = 0 := by
  simpa only [laurentMaslovHexagonComponent, ComplexShape.down_Rel, eq_comm] using
    (dif_neg (show ¬ j = i + 1 by simpa only [ComplexShape.down_Rel, eq_comm] using h) :
      laurentMaslovHexagonComponent G R C i j = 0)

/-- Every native geometric hexagon component preserves both filtration bounds. -/
theorem laurentMaslovHexagonComponent_mem_level (C : GridDiagram.ColumnCommutationData G)
    (a b : ℝ) (i j : ℤ) (c : (laurentMaslovComplex G R).X i)
    (hc : c ∈ (laurentMaslovBifiltration G R).level a b i) :
    laurentMaslovHexagonComponent G R C i j c ∈
      (laurentMaslovBifiltration G R).level a b j := by
  by_cases h : j = i + 1
  · subst j
    rw [laurentMaslovHexagonComponent_succ]
    change (laurentCommutationHexagonMap G R C
      (laurentMaslovChainEquiv G R i c) : LaurentChain R n) ∈
        laurentBifiltrationLevel G R a b
    exact laurentCommutationHexagonMap_mem_bifiltrationLevel G R C hc
  · rw [laurentMaslovHexagonComponent, dif_neg h]
    exact Submodule.zero_mem _

/-- The source inverse-homotopy equation on each native homogeneous component. -/
theorem laurentMaslovCommutation_source_component (C : GridDiagram.ColumnCommutationData G)
    (m : ℤ) :
    (laurentMaslovCommutationHom G R C ≫ laurentMaslovReverseCommutationHom G R C).f (m + 1) =
      (laurentMaslovComplex G R).d (m + 1) m ≫
          laurentMaslovHexagonComponent G R C m (m + 1) +
        laurentMaslovHexagonComponent G R C (m + 1) ((m + 1) + 1) ≫
          (laurentMaslovComplex G R).d ((m + 1) + 1) (m + 1) +
        𝟙 ((laurentMaslovComplex G R).X (m + 1)) := by
  simp only [laurentMaslovHexagonComponent_succ, laurentMaslovComplex_d]
  ext c : 2
  apply Subtype.ext
  let c' : LaurentChain R n := laurentMaslovChainEquiv G R (m + 1) c
  change laurentReverseCommutationMap G R C (laurentCommutationMap G R C c') =
    laurentCommutationHexagonMap G R C (laurentDifferential G R c') +
      laurentDifferential G R (laurentCommutationHexagonMap G R C c') + c' 
  apply Finsupp.ext
  intro y
  have h := congrArg (fun z : LaurentChain R n => z y)
    (laurentCommutation_source_homotopy G R C c')
  simp only [Finsupp.add_apply] at h ⊢
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h

/-- The actual geometric hexagon count gives the source native chain homotopy. -/
noncomputable def laurentMaslovCommutation_sourceHomotopy
    (C : GridDiagram.ColumnCommutationData G) :
    Homotopy (laurentMaslovCommutationHom G R C ≫ laurentMaslovReverseCommutationHom G R C)
      (𝟙 (laurentMaslovComplex G R)) where
  hom := laurentMaslovHexagonComponent G R C
  zero := laurentMaslovHexagonComponent_zero G R C
  comm i := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = i := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel ((m + 1) + 1) (m + 1) from rfl)]
    exact laurentMaslovCommutation_source_component G R C m

/-- The target inverse-homotopy equation on each native homogeneous component. -/
theorem laurentMaslovCommutation_target_component (C : GridDiagram.ColumnCommutationData G)
    (m : ℤ) :
    (laurentMaslovReverseCommutationHom G R C ≫ laurentMaslovCommutationHom G R C).f (m + 1) =
      (laurentMaslovComplex (G.swapColumns C.column (finRotate n C.column)) R).d (m + 1) m ≫
          laurentMaslovHexagonComponent
            (G.swapColumns C.column (finRotate n C.column)) R C.reverse m (m + 1) +
        laurentMaslovHexagonComponent
          (G.swapColumns C.column (finRotate n C.column)) R C.reverse (m + 1) ((m + 1) + 1) ≫
          (laurentMaslovComplex (G.swapColumns C.column (finRotate n C.column)) R).d
            ((m + 1) + 1) (m + 1) +
        𝟙 ((laurentMaslovComplex (G.swapColumns C.column (finRotate n C.column)) R).X (m + 1)) := by
  simp only [laurentMaslovHexagonComponent_succ, laurentMaslovComplex_d]
  ext c : 2
  apply Subtype.ext
  let G' := G.swapColumns C.column (finRotate n C.column)
  let c' : LaurentChain R n := laurentMaslovChainEquiv G' R (m + 1) c
  change laurentCommutationMap G R C (laurentReverseCommutationMap G R C c') =
    laurentCommutationHexagonMap G' R C.reverse (laurentDifferential G' R c') +
      laurentDifferential G' R (laurentCommutationHexagonMap G' R C.reverse c') + c'
  apply Finsupp.ext
  intro y
  have h := congrArg (fun z : LaurentChain R n => z y)
    (laurentCommutation_target_homotopy G R C c')
  dsimp only [G'] at h ⊢
  simp only [Finsupp.add_apply] at h ⊢
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h

/-- The reverse geometric hexagon count gives the target native chain homotopy. -/
noncomputable def laurentMaslovCommutation_targetHomotopy
    (C : GridDiagram.ColumnCommutationData G) :
    Homotopy (laurentMaslovReverseCommutationHom G R C ≫ laurentMaslovCommutationHom G R C)
      (𝟙 (laurentMaslovComplex (G.swapColumns C.column (finRotate n C.column)) R)) where
  hom := laurentMaslovHexagonComponent
    (G.swapColumns C.column (finRotate n C.column)) R C.reverse
  zero := laurentMaslovHexagonComponent_zero
    (G.swapColumns C.column (finRotate n C.column)) R C.reverse
  comm i := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = i := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel ((m + 1) + 1) (m + 1) from rfl)]
    exact laurentMaslovCommutation_target_component G R C m

/-- Validated adjacent column commutation gives an explicit native chain homotopy equivalence. -/
noncomputable def laurentMaslovCommutationHomotopyEquiv
    (C : GridDiagram.ColumnCommutationData G) :
    HomotopyEquiv (laurentMaslovComplex G R)
      (laurentMaslovComplex (G.swapColumns C.column (finRotate n C.column)) R) where
  hom := laurentMaslovCommutationHom G R C
  inv := laurentMaslovReverseCommutationHom G R C
  homotopyHomInvId := laurentMaslovCommutation_sourceHomotopy G R C
  homotopyInvHomId := laurentMaslovCommutation_targetHomotopy G R C

/-- The source inverse homotopy preserves both filtration coordinates in every component. -/
theorem laurentMaslovCommutation_sourceHomotopy_mem_level
    (C : GridDiagram.ColumnCommutationData G) (a b : ℝ) (i j : ℤ)
    (c : (laurentMaslovComplex G R).X i)
    (hc : c ∈ (laurentMaslovBifiltration G R).level a b i) :
    (laurentMaslovCommutation_sourceHomotopy G R C).hom i j c ∈
      (laurentMaslovBifiltration G R).level a b j :=
  laurentMaslovHexagonComponent_mem_level G R C a b i j c hc

/-- The target inverse homotopy preserves both filtration coordinates in every component. -/
theorem laurentMaslovCommutation_targetHomotopy_mem_level
    (C : GridDiagram.ColumnCommutationData G) (a b : ℝ) (i j : ℤ)
    (c : (laurentMaslovComplex (G.swapColumns C.column (finRotate n C.column)) R).X i)
    (hc : c ∈ (laurentMaslovBifiltration
      (G.swapColumns C.column (finRotate n C.column)) R).level a b i) :
    (laurentMaslovCommutation_targetHomotopy G R C).hom i j c ∈
      (laurentMaslovBifiltration
        (G.swapColumns C.column (finRotate n C.column)) R).level a b j :=
  laurentMaslovHexagonComponent_mem_level
    (G.swapColumns C.column (finRotate n C.column)) R C.reverse a b i j c hc

/-- Adjacent column commutation preserves the weighted threshold of each native homology class. -/
theorem spectralThreshold_laurentMaslovCommutation (C : GridDiagram.ColumnCommutationData G)
    (m : ℤ) (ξ : (laurentMaslovComplex G R).homology m) (t : ℝ) :
    ((laurentMaslovBifiltration
        (G.swapColumns C.column (finRotate n C.column)) R).weighted t).spectralThreshold m
      (homologyMap (laurentMaslovCommutationHom G R C) m ξ) =
        ((laurentMaslovBifiltration G R).weighted t).spectralThreshold m ξ :=
  Bifiltration.weighted_spectralThreshold_eq_of_homotopyEquiv
    (laurentMaslovCommutationHomotopyEquiv G R C)
    (laurentMaslovCommutationHom_preserves G R C)
    (laurentMaslovReverseCommutationHom_preserves G R C) m ξ t

/-- The algebraic class-Upsilon function is invariant under adjacent column commutation. -/
theorem classUpsilon_laurentMaslovCommutation (C : GridDiagram.ColumnCommutationData G)
    (m : ℤ) (ξ : (laurentMaslovComplex G R).homology m) (t : ℝ) :
    (laurentMaslovBifiltration
        (G.swapColumns C.column (finRotate n C.column)) R).classUpsilon m
      (homologyMap (laurentMaslovCommutationHom G R C) m ξ) t =
        (laurentMaslovBifiltration G R).classUpsilon m ξ t :=
  Bifiltration.classUpsilon_eq_of_homotopyEquiv
    (laurentMaslovCommutationHomotopyEquiv G R C)
    (laurentMaslovCommutationHom_preserves G R C)
    (laurentMaslovReverseCommutationHom_preserves G R C) m ξ t

end OnLeConjecture.KnotFloer.GridFull
