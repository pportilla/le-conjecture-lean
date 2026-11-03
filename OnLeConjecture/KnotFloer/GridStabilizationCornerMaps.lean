/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridCanonicalMoves

/-!
# Native maps for all stabilization corners

For grid diagrams `G` and `H` of sizes `n` and `k` and a real number `b`, the proposition
`GridCanonicalTransport G H b` states the following. If `2 ≤ n` and `2 ≤ k`, then some chain map
`laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2)` has filtration shifts
`(0, b)` and sends `gridCanonicalClass G` to `gridCanonicalClass H`. The relation holds from
every grid to itself with `b = 0`. Two instances compose, with the sum of the second shifts,
provided the intermediate grid has size at least two whenever the source grid has.

The following native maps give the relation with `b = 0` in both directions.

* The cyclic row and column isomorphisms and their inverses.
* The transposition and half-turn isomorphisms and their inverses.
* The pentagon map of a validated column commutation and its opposite map. Composed with
  transposition, they treat every elementary row or column commutation.
* The first-summand inclusion `stabilizationCanonicalInclusion` and projection
  `stabilizationCanonicalProjection` of the `X`-stabilization whose new `O`-marking is the
  south-west corner of the new block.
* For the `X`-stabilization `G'` of `G` whose new `O`-marking is the north-east corner, the
  composite of the half-turn isomorphism of `G`, the south-west corner inclusion of `G.rotate`,
  and the inverse half-turn isomorphism of `G'`. It is well defined because
  `GridDiagram.rotate_stabilizeX_succ` identifies `G'.rotate` with a south-west corner
  stabilization of `G.rotate`. The reverse composite uses the corresponding projection.

The vendored reduction `GridDiagram.IsStabilization.exists_commutationMovesTo` connects every
elementary stabilization to one of these two corner stabilizations by cyclic permutations and
commutations. Composing the maps above along that reduction gives maps in both directions for
every elementary stabilization (`gridCanonicalTransport_of_isStabilization`).

These statements concern native grid complexes over `ZMod 2` and their normalized classes. They do
not identify grid diagrams with geometric links.
-/
@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable {n m k : ℕ}

/-- The proposition that, if `G` and `H` both have size at least two, some chain map
`laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2)` has filtration shifts
`(0, b)` and sends `gridCanonicalClass G` to `gridCanonicalClass H`. -/
def GridCanonicalTransport (G : GridDiagram n) (H : GridDiagram k) (b : ℝ) : Prop :=
  ∀ (hn : 2 ≤ n) (hk : 2 ≤ k),
    ∃ φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2),
      (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2))
          φ 0 b ∧
        homologyMap φ 0 (gridCanonicalClass G hn) = gridCanonicalClass H hk

namespace GridCanonicalTransport

/-- The identity chain map gives `GridCanonicalTransport G G 0`. -/
theorem refl (G : GridDiagram n) : GridCanonicalTransport G G 0 := by
  intro hn _
  refine ⟨𝟙 _, ?_, ?_⟩
  · intro a b i x hx
    rw [add_zero, add_zero]
    exact hx
  · rw [homologyMap_id, CategoryTheory.id_apply]

/-- If `b = b'`, then `GridCanonicalTransport G H b` implies `GridCanonicalTransport G H b'`. -/
theorem of_eq_shift {G : GridDiagram n} {H : GridDiagram k} {b b' : ℝ}
    (h : GridCanonicalTransport G H b) (hb : b = b') : GridCanonicalTransport G H b' :=
  hb ▸ h

/-- Composition of chain maps gives `GridCanonicalTransport G K (b₁ + b₂)` from
`GridCanonicalTransport G H b₁` and `GridCanonicalTransport H K b₂`, provided `H` has size at least
two whenever `G` has. -/
theorem trans {G : GridDiagram n} {H : GridDiagram m} {K : GridDiagram k} {b₁ b₂ : ℝ}
    (h₁ : GridCanonicalTransport G H b₁) (h₂ : GridCanonicalTransport H K b₂)
    (hm : 2 ≤ n → 2 ≤ m) : GridCanonicalTransport G K (b₁ + b₂) := by
  intro hn hk
  obtain ⟨φ, hφ, hφξ⟩ := h₁ hn (hm hn)
  obtain ⟨ψ, hψ, hψξ⟩ := h₂ (hm hn) hk
  refine ⟨φ ≫ ψ, ?_, ?_⟩
  · simpa only [add_zero] using hφ.comp hψ
  · rw [homologyMap_comp, CategoryTheory.comp_apply, hφξ, hψξ]

/-- For grids `G`, `H` and `K` of one size, `GridCanonicalTransport G H b₁` and
`GridCanonicalTransport H K b₂` imply `GridCanonicalTransport G K (b₁ + b₂)`. -/
theorem trans_of_size_eq {G H K : GridDiagram n} {b₁ b₂ : ℝ}
    (h₁ : GridCanonicalTransport G H b₁) (h₂ : GridCanonicalTransport H K b₂) :
    GridCanonicalTransport G K (b₁ + b₂) :=
  h₁.trans h₂ id

/-- For grids `G`, `H` and `K` of one size, `GridCanonicalTransport G H 0` and
`GridCanonicalTransport H K 0` imply `GridCanonicalTransport G K 0`. -/
theorem trans_zero {G H K : GridDiagram n}
    (h₁ : GridCanonicalTransport G H 0) (h₂ : GridCanonicalTransport H K 0) :
    GridCanonicalTransport G K 0 :=
  (h₁.trans_of_size_eq h₂).of_eq_shift (add_zero 0)

/-- A native homotopy equivalence whose forward map has filtration shifts `(0, b)` gives
`GridCanonicalTransport G H b`, with that forward map. -/
theorem of_homotopyEquiv {G : GridDiagram n} {H : GridDiagram k} {b : ℝ}
    (e : HomotopyEquiv (laurentMaslovComplex G (ZMod 2)) (laurentMaslovComplex H (ZMod 2)))
    (he : (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2))
      e.hom 0 b) :
    GridCanonicalTransport G H b :=
  fun hn hk => ⟨e.hom, he, gridCanonicalClass_homotopyEquiv G H hn hk e b he⟩

/-- A native homotopy equivalence whose forward map preserves both filtrations gives
`GridCanonicalTransport G H 0`, with that forward map. -/
theorem of_homotopyEquiv_preserves {G : GridDiagram n} {H : GridDiagram k}
    (e : HomotopyEquiv (laurentMaslovComplex G (ZMod 2)) (laurentMaslovComplex H (ZMod 2)))
    (he : (laurentMaslovBifiltration G (ZMod 2)).Preserves (laurentMaslovBifiltration H (ZMod 2))
      e.hom) :
    GridCanonicalTransport G H 0 :=
  of_homotopyEquiv e (Bifiltration.shifts_zero_zero_iff.mpr he)

/-- A native isomorphism whose forward map preserves both filtrations gives
`GridCanonicalTransport G H 0`, with that forward map. -/
theorem of_iso_hom {G : GridDiagram n} {H : GridDiagram k}
    (e : laurentMaslovComplex G (ZMod 2) ≅ laurentMaslovComplex H (ZMod 2))
    (he : (laurentMaslovBifiltration G (ZMod 2)).Preserves (laurentMaslovBifiltration H (ZMod 2))
      e.hom) :
    GridCanonicalTransport G H 0 :=
  of_homotopyEquiv_preserves (HomotopyEquiv.ofIso e) he

/-- A native isomorphism whose inverse map preserves both filtrations gives
`GridCanonicalTransport H G 0`, with that inverse map. -/
theorem of_iso_inv {G : GridDiagram n} {H : GridDiagram k}
    (e : laurentMaslovComplex G (ZMod 2) ≅ laurentMaslovComplex H (ZMod 2))
    (he : (laurentMaslovBifiltration H (ZMod 2)).Preserves (laurentMaslovBifiltration G (ZMod 2))
      e.inv) :
    GridCanonicalTransport H G 0 :=
  of_homotopyEquiv_preserves (HomotopyEquiv.ofIso e.symm) he

end GridCanonicalTransport

/-! ### Symmetries and commutations -/

/-- The cyclic row isomorphism `laurentMaslovCyclicRowsIso` gives
`GridCanonicalTransport G (G.relabelRows (finRotate n)) 0`. -/
theorem gridCanonicalTransport_cyclicRows (G : GridDiagram n) :
    GridCanonicalTransport G (G.relabelRows (finRotate n)) 0 :=
  .of_iso_hom _ (laurentMaslovCyclicRows_preserves G (ZMod 2))

/-- The inverse of `laurentMaslovCyclicRowsIso` gives
`GridCanonicalTransport (G.relabelRows (finRotate n)) G 0`. -/
theorem gridCanonicalTransport_cyclicRows_symm (G : GridDiagram n) :
    GridCanonicalTransport (G.relabelRows (finRotate n)) G 0 :=
  .of_iso_inv _ (laurentMaslovCyclicRows_inv_preserves G (ZMod 2))

/-- The cyclic column isomorphism `laurentMaslovCyclicColumnsIso` gives
`GridCanonicalTransport G (G.relabelColumns (finRotate n)) 0`. -/
theorem gridCanonicalTransport_cyclicColumns (G : GridDiagram n) :
    GridCanonicalTransport G (G.relabelColumns (finRotate n)) 0 :=
  .of_iso_hom _ (laurentMaslovCyclicColumns_preserves G (ZMod 2))

/-- The inverse of `laurentMaslovCyclicColumnsIso` gives
`GridCanonicalTransport (G.relabelColumns (finRotate n)) G 0`. -/
theorem gridCanonicalTransport_cyclicColumns_symm (G : GridDiagram n) :
    GridCanonicalTransport (G.relabelColumns (finRotate n)) G 0 :=
  .of_iso_inv _ (laurentMaslovCyclicColumns_inv_preserves G (ZMod 2))

/-- The transposition isomorphism `laurentMaslovTransposeIso` gives
`GridCanonicalTransport G G.transpose 0`. -/
theorem gridCanonicalTransport_transpose (G : GridDiagram n) :
    GridCanonicalTransport G G.transpose 0 :=
  .of_iso_hom _ (laurentMaslovTranspose_preserves G (ZMod 2))

/-- The inverse of `laurentMaslovTransposeIso` gives
`GridCanonicalTransport G.transpose G 0`. -/
theorem gridCanonicalTransport_transpose_symm (G : GridDiagram n) :
    GridCanonicalTransport G.transpose G 0 :=
  .of_iso_inv _ (laurentMaslovTranspose_inv_preserves G (ZMod 2))

/-- The half-turn isomorphism `laurentMaslovHalfTurnIso` gives
`GridCanonicalTransport G G.rotate 0`. -/
theorem gridCanonicalTransport_halfTurn (G : GridDiagram n) :
    GridCanonicalTransport G G.rotate 0 :=
  .of_iso_hom _ (laurentMaslovHalfTurn_preserves G (ZMod 2))

/-- The inverse of `laurentMaslovHalfTurnIso` gives `GridCanonicalTransport G.rotate G 0`. -/
theorem gridCanonicalTransport_halfTurn_symm (G : GridDiagram n) :
    GridCanonicalTransport G.rotate G 0 :=
  .of_iso_inv _ (laurentMaslovHalfTurn_inv_preserves G (ZMod 2))

/-- The pentagon map `laurentMaslovCommutationHom` of validated column commutation data `C` gives
`GridCanonicalTransport G (G.swapColumns C.column (finRotate n C.column)) 0`. -/
theorem gridCanonicalTransport_columnCommutation (G : GridDiagram n)
    (C : GridDiagram.ColumnCommutationData G) :
    GridCanonicalTransport G (G.swapColumns C.column (finRotate n C.column)) 0 :=
  .of_homotopyEquiv_preserves (laurentMaslovCommutationHomotopyEquiv G (ZMod 2) C)
    (laurentMaslovCommutationHom_preserves G (ZMod 2) C)

/-- The opposite pentagon map `laurentMaslovReverseCommutationHom` of validated column
commutation data `C` gives
`GridCanonicalTransport (G.swapColumns C.column (finRotate n C.column)) G 0`. -/
theorem gridCanonicalTransport_columnCommutation_symm (G : GridDiagram n)
    (C : GridDiagram.ColumnCommutationData G) :
    GridCanonicalTransport (G.swapColumns C.column (finRotate n C.column)) G 0 :=
  .of_homotopyEquiv_preserves (laurentMaslovCommutationHomotopyEquiv G (ZMod 2) C).symm
    (laurentMaslovReverseCommutationHom_preserves G (ZMod 2) C)

/-- An elementary column commutation from `G` to `H` gives `GridCanonicalTransport G H 0`. -/
theorem gridCanonicalTransport_of_isColumnCommutation {G H : GridDiagram n}
    (h : GridDiagram.IsColumnCommutation G H) : GridCanonicalTransport G H 0 := by
  obtain ⟨C, rfl⟩ := GridDiagram.isColumnCommutation_iff_exists_columnCommutationData.mp h
  exact gridCanonicalTransport_columnCommutation G C

/-- An elementary row commutation from `G` to `H` gives `GridCanonicalTransport G H 0`. The map
is the column commutation map of the transposed grids, conjugated by transposition. -/
theorem gridCanonicalTransport_of_isRowCommutation {G H : GridDiagram n}
    (h : GridDiagram.IsRowCommutation G H) : GridCanonicalTransport G H 0 :=
  ((gridCanonicalTransport_transpose G).trans_zero
    (gridCanonicalTransport_of_isColumnCommutation
      ((GridDiagram.isColumnCommutation_transpose G H).mpr h))).trans_zero
    (gridCanonicalTransport_transpose_symm H)

/-- An elementary commutation from `G` to `H` gives `GridCanonicalTransport G H 0`. -/
theorem gridCanonicalTransport_of_isCommutation {G H : GridDiagram n}
    (h : GridDiagram.IsCommutation G H) : GridCanonicalTransport G H 0 :=
  ((GridDiagram.isCommutation_iff G H).mp h).elim gridCanonicalTransport_of_isRowCommutation
    gridCanonicalTransport_of_isColumnCommutation

/-- If cyclic permutations and commutations connect `G` to `H`, then
`GridCanonicalTransport G H 0` and `GridCanonicalTransport H G 0` hold. -/
theorem gridCanonicalTransport_of_commutationMovesTo {G H : GridDiagram n}
    (h : GridDiagram.CommutationMovesTo G H) :
    GridCanonicalTransport G H 0 ∧ GridCanonicalTransport H G 0 :=
  h.induction_on
    (motive := fun G H => GridCanonicalTransport G H 0 ∧ GridCanonicalTransport H G 0)
    (fun G => ⟨gridCanonicalTransport_cyclicRows G, gridCanonicalTransport_cyclicRows_symm G⟩)
    (fun G => ⟨gridCanonicalTransport_cyclicColumns G,
      gridCanonicalTransport_cyclicColumns_symm G⟩)
    (fun h => ⟨gridCanonicalTransport_of_isCommutation h,
      gridCanonicalTransport_of_isCommutation (GridDiagram.isCommutation_comm.mp h)⟩)
    (fun G => ⟨.refl G, .refl G⟩)
    (fun _ ih => ⟨ih.2, ih.1⟩)
    (fun _ _ ih ih' => ⟨ih.1.trans_zero ih'.1, ih'.2.trans_zero ih.2⟩)

/-! ### The two corner stabilizations -/

/-- The first-summand inclusion `stabilizationCanonicalInclusion` gives
`GridCanonicalTransport G G' 0` for the `X`-stabilization `G'` of `G` whose new `O`-marking is the
south-west corner of the new block. -/
theorem gridCanonicalTransport_stabilizeX_castSucc (G : GridDiagram n) (s : Fin n) :
    GridCanonicalTransport G (G.stabilizeX s.castSucc (G.X s).castSucc s) 0 :=
  fun hn _ => ⟨stabilizationCanonicalInclusion (ZMod 2) G s,
    stabilizationCanonicalInclusion_shifts (ZMod 2) G s, gridCanonicalClass_stabilization G hn s⟩

/-- The first-summand projection `stabilizationCanonicalProjection` gives
`GridCanonicalTransport G' G 0` for the `X`-stabilization `G'` of `G` whose new `O`-marking is the
south-west corner of the new block. -/
theorem gridCanonicalTransport_stabilizeX_castSucc_symm (G : GridDiagram n) (s : Fin n) :
    GridCanonicalTransport (G.stabilizeX s.castSucc (G.X s).castSucc s) G 0 :=
  fun _ hn => ⟨stabilizationCanonicalProjection (ZMod 2) G s,
    stabilizationCanonicalProjection_shifts (ZMod 2) G s,
    gridCanonicalClass_stabilization_projection G hn s⟩

/-- For the `X`-stabilization `G'` of `G` whose new `O`-marking is the north-east corner of the
new block, `GridCanonicalTransport G G' 0` holds. The map is the half-turn isomorphism of `G`,
followed by the south-west corner inclusion of `G.rotate`, whose target is `G'.rotate` by
`GridDiagram.rotate_stabilizeX_succ`, and by the inverse half-turn isomorphism of `G'`. -/
theorem gridCanonicalTransport_stabilizeX_succ (G : GridDiagram n) (s : Fin n) :
    GridCanonicalTransport G (G.stabilizeX s.succ (G.X s).succ s) 0 := by
  have h := (gridCanonicalTransport_halfTurn G).trans
    (gridCanonicalTransport_stabilizeX_castSucc G.rotate s.rev) id
  rw [← G.rotate_stabilizeX_succ s, add_zero] at h
  exact (h.trans (gridCanonicalTransport_halfTurn_symm _) (fun _ => by omega)).of_eq_shift
    (add_zero 0)

/-- For the `X`-stabilization `G'` of `G` whose new `O`-marking is the north-east corner of the
new block, `GridCanonicalTransport G' G 0` holds. The map is the half-turn isomorphism of `G'`,
followed by the south-west corner projection of `G.rotate`, whose source is `G'.rotate` by
`GridDiagram.rotate_stabilizeX_succ`, and by the inverse half-turn isomorphism of `G`. -/
theorem gridCanonicalTransport_stabilizeX_succ_symm (G : GridDiagram n) (s : Fin n) :
    GridCanonicalTransport (G.stabilizeX s.succ (G.X s).succ s) G 0 := by
  have h := (gridCanonicalTransport_stabilizeX_castSucc_symm G.rotate s.rev).trans
    (gridCanonicalTransport_halfTurn_symm G) (fun _ => by
      have := grid_size_two_le_of_column G s
      omega)
  rw [← G.rotate_stabilizeX_succ s, add_zero] at h
  exact ((gridCanonicalTransport_halfTurn _).trans h id).of_eq_shift (add_zero 0)

/-! ### All stabilizations -/

/-- **Native maps for every stabilization.** If `H` is an elementary stabilization of `G`, then
`GridCanonicalTransport G H 0` and `GridCanonicalTransport H G 0` hold. The maps are composites of
the two corner maps with the cyclic permutation and commutation maps along the vendored reduction
`GridDiagram.IsStabilization.exists_commutationMovesTo`. -/
theorem gridCanonicalTransport_of_isStabilization {G : GridDiagram n}
    {H : GridDiagram (n + 1)} (h : GridDiagram.IsStabilization G H) :
    GridCanonicalTransport G H 0 ∧ GridCanonicalTransport H G 0 := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · obtain ⟨h₁, h₂⟩ := gridCanonicalTransport_of_commutationMovesTo hs
    exact ⟨((gridCanonicalTransport_stabilizeX_castSucc G s).trans h₂
        (fun _ => by omega)).of_eq_shift (add_zero 0),
      (h₁.trans (gridCanonicalTransport_stabilizeX_castSucc_symm G s) id).of_eq_shift
        (add_zero 0)⟩
  · obtain ⟨h₁, h₂⟩ := gridCanonicalTransport_of_commutationMovesTo hs
    exact ⟨((gridCanonicalTransport_stabilizeX_succ G s).trans h₂
        (fun _ => by omega)).of_eq_shift (add_zero 0),
      (h₁.trans (gridCanonicalTransport_stabilizeX_succ_symm G s) id).of_eq_shift
        (add_zero 0)⟩

end OnLeConjecture.KnotFloer.GridFull
