/-
Copyright (c) 2026 The Tau Ceti contributors and Pablo Portilla Cuadrado.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: The Tau Ceti contributors, Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullDifferentialBasic

/-!
# Off-diagonal cancellation for the full grid differential

Pairs of empty rectangles with different initial and final states cancel
by commuting disjoint sides or recutting one common side. The proof allows
rectangles crossing X markings. It adapts the pairing in TauCeti's
`Grid/Differential/Square/Zero.lean` at commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`, retaining its actual rectangle
geometry and omitting the marking-avoidance condition from membership.

The diagonal terms are annuli and require a separate proof.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ}

/-- Commuting disjoint sides preserves emptiness of both rectangles. -/
theorem commute_mem_emptyDecompositions_iff {x z : GridState n}
    (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    D.commute h ∈ emptyDecompositions x z ↔ D ∈ emptyDecompositions x z := by
  have hforward : ∀ (E : GridRectangleDecomposition x z) (hE : E.HasDisjointSides),
      E ∈ emptyDecompositions x z → E.commute hE ∈ emptyDecompositions x z := by
    intro E hE hmem
    obtain ⟨h₁, h₂⟩ := (mem_emptyDecompositions E).mp hmem
    exact (mem_emptyDecompositions _).mpr
      ⟨E.isEmpty_commute_first hE h₁ h₂, E.isEmpty_commute_second hE h₁ h₂⟩
  constructor
  · intro hD
    simpa only [D.commute_commute h] using
      hforward (D.commute h) (D.hasDisjointSides_commute h) hD
  · exact hforward D h

/-- A function on all empty two-rectangle decompositions has zero sum
between different states when each of the two geometric pairings reverses
its contribution. -/
theorem sum_emptyDecompositions_eq_zero {M : Type*} [AddCommMonoid M]
    {x z : GridState n} (hzx : z ≠ x) (f : GridRectangleDecomposition x z → M)
    (hcommute : ∀ D ∈ emptyDecompositions x z, ∀ h : D.HasDisjointSides,
      f D + f (D.commute h) = 0)
    (hrecut : ∀ D ∈ emptyDecompositions x z, ∀ (hone : D.HasOneCommonSide)
      (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty),
      f D + f (D.recut hone hfirst hsecond) = 0) :
    ∑ D ∈ emptyDecompositions x z, f D = 0 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (emptyDecompositions x z)
      (fun D => D.HasDisjointSides) f]
  have hdisjoint : ∑ D ∈ (emptyDecompositions x z).filter
      (fun D => D.HasDisjointSides), f D = 0 := by
    refine Finset.sum_involution
      (fun D hD => D.commute (Finset.mem_filter.mp hD).2) (fun D hD => ?_)
      (fun D hD _ => ?_) (fun D hD => ?_) (fun D hD => ?_)
    · exact hcommute D (Finset.mem_filter.mp hD).1 _
    · exact D.commute_ne _
    · exact Finset.mem_filter.mpr
        ⟨(commute_mem_emptyDecompositions_iff D _).mpr (Finset.mem_filter.mp hD).1,
          D.hasDisjointSides_commute _⟩
    · exact D.commute_commute _
  have hone : ∀ D ∈ (emptyDecompositions x z).filter
      (fun D => ¬D.HasDisjointSides), D.HasOneCommonSide := fun D hD =>
    (D.hasDisjointSides_or_hasOneCommonSide_of_ne hzx).resolve_left
      (Finset.mem_filter.mp hD).2
  have hmem : ∀ D ∈ (emptyDecompositions x z).filter (fun D => ¬D.HasDisjointSides),
      D.first.IsEmpty ∧ D.second.IsEmpty :=
    fun D hD => (mem_emptyDecompositions D).mp (Finset.mem_filter.mp hD).1
  have hcommon : ∑ D ∈ (emptyDecompositions x z).filter
      (fun D => ¬D.HasDisjointSides), f D = 0 := by
    refine Finset.sum_involution
      (fun D hD => D.recut (hone D hD) (hmem D hD).1 (hmem D hD).2)
      (fun D hD => ?_) (fun D hD _ => ?_) (fun D hD => ?_) (fun D hD => ?_)
    · exact hrecut D (Finset.mem_filter.mp hD).1 _ _ _
    · exact D.recut_ne _ _ _
    · have hrecut := D.isRecut_recut (hone D hD) (hmem D hD).1 (hmem D hD).2
      refine Finset.mem_filter.mpr ⟨(mem_emptyDecompositions _).mpr
        ⟨hrecut.isEmpty_first, hrecut.isEmpty_second⟩, ?_⟩
      exact GridRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide _
        (D.hasOneCommonSide_recut _ _ _)
    · exact D.recut_recut _ _ _
  rw [hdisjoint, hcommon, add_zero]

/-- The O-weighted off-diagonal entries cancel in characteristic two,
with no restriction on X markings inside the rectangles. -/
theorem sum_emptyDecompositionWeight_eq_zero_of_ne
    (G : GridDiagram n) (R : Type*) [CommSemiring R] [CharP R 2]
    {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ emptyDecompositions x z, G.unblockedDecompositionWeight R D = 0 := by
  refine sum_emptyDecompositions_eq_zero hzx _ (fun D _ h => ?_)
    (fun D _ hone hfirst hsecond => ?_)
  · rw [G.unblockedDecompositionWeight_commute R D]
    exact CharTwo.add_self_eq_zero _
  · rw [G.unblockedDecompositionWeight_recut R D]
    exact CharTwo.add_self_eq_zero _

end OnLeConjecture.KnotFloer.GridFull
