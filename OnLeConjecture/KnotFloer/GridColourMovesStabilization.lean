/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridColourMovesSymmetry

/-!
# Colour transport along stabilizations

Let `A = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization of `G` whose new `O`
marking is the south-west corner of the new block. Its new column `s.castSucc` carries the new
`O` marking, and the old column `s` of `G` becomes the column `s.succ`. The component
permutation `π_A` of `A` sends the new column to `s.succ`, and it sends the embedded column
`s.castSucc.succAbove c` to `s.succ.succAbove (π c)`, where `π` is the component permutation of
`G` (`gridComponentPerm_stabilizeX_castSucc_new`,
`gridComponentPerm_stabilizeX_castSucc_succAbove`). Hence the new column lies on the component of
`s.succ`, and `s.predAbove`, which sends the new column to `s` and every embedded column to its
old column, is a component map from `A` to `G` (`componentMap_stabilizeX_castSucc`).

A component colouring `χ` of `G` therefore gives the component colouring `χ ∘ s.predAbove` of `A`,
in which the new `O` marking carries the colour of its component. The colour naturality of the
canonical inclusion and projection (`isNullHomotopic_stabilization_inclusion_colour` and
`isNullHomotopic_stabilization_projection_colour`, `GridStabilizationColourNatural`) gives colour
transport data in both directions. The side condition of the projection, that the new column
`s.castSucc` and the column `s.succ` have the same colour, holds for every colouring of the form
`χ ∘ s.predAbove`, since both columns are sent to `s`.

The stabilization whose new `O` marking is the north-east corner is reduced to the south-west
corner of `G.rotate` by the half-turn, as in `GridStabilizationCornerMaps`. Every elementary
stabilization is connected to one of the two corners by cyclic permutations and commutations
(`GridDiagram.IsStabilization.exists_commutationMovesTo`), which gives colour pullbacks in both
directions for every elementary stabilization (`colourPullback_of_isStabilization`).
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-! ### Components of the south-west corner stabilization -/

/-- The component permutation of the south-west corner stabilization sends the new column to the
column `s.succ` of the split `X` marking. -/
theorem gridComponentPerm_stabilizeX_castSucc_new :
    gridComponentPerm (G.stabilizeX s.castSucc (G.X s).castSucc s) s.castSucc = s.succ := by
  rw [gridComponentPerm, Equiv.trans_apply, Equiv.symm_apply_eq]
  rw [GridDiagram.stabilizeX_O, GridDiagram.stabilizeX_X, GridState.insertPoint_apply_newColumn,
    GridState.splitPoint_castSucc_apply_succ]

/-- The component permutation of the south-west corner stabilization sends the embedded column
`s.castSucc.succAbove c` to `s.succ.succAbove (π c)`. -/
theorem gridComponentPerm_stabilizeX_castSucc_succAbove (c : Fin n) :
    gridComponentPerm (G.stabilizeX s.castSucc (G.X s).castSucc s) (s.castSucc.succAbove c) =
      s.succ.succAbove (gridComponentPerm G c) := by
  rw [gridComponentPerm, Equiv.trans_apply, Equiv.symm_apply_eq]
  rw [GridDiagram.stabilizeX_O, GridDiagram.stabilizeX_X, GridState.insertPoint_apply_succAbove,
    GridState.splitPoint_castSucc_eq_insertPoint, GridState.insertPoint_apply_succAbove]
  congr 1
  simp [gridComponentPerm]

/-- The map `s.predAbove`, which sends the new column of the south-west corner stabilization to
`s` and every embedded column to its old column, is a component map. -/
theorem componentMap_stabilizeX_castSucc :
    ComponentMap G (G.stabilizeX s.castSucc (G.X s).castSucc s) s.predAbove := by
  set πA := gridComponentPerm (G.stabilizeX s.castSucc (G.X s).castSucc s) with hπA
  set π := gridComponentPerm G with hπ
  have hnew : πA s.castSucc = s.succ := gridComponentPerm_stabilizeX_castSucc_new G s
  have hold : ∀ c, πA (s.castSucc.succAbove c) = s.succ.succAbove (π c) :=
    gridComponentPerm_stabilizeX_castSucc_succAbove G s
  have hpe : ∀ c, s.predAbove (s.castSucc.succAbove c) = c := Fin.predAbove_succAbove s
  have hpe' : ∀ d, s.predAbove (s.succ.succAbove d) = d := by
    intro d
    rcases le_or_gt d s with h | h
    · rw [Fin.succAbove_succ_of_le _ _ h, Fin.predAbove_castSucc_of_le _ _ h]
    · rw [Fin.succAbove_succ_of_lt _ _ h, Fin.predAbove_succ_of_le _ _ h.le]
  have hone : ∀ x, πA.SameCycle x (πA x) := fun x => ⟨1, by simp⟩
  have hone' : ∀ a, π.SameCycle a (π a) := fun a => ⟨1, by simp⟩
  -- One step of `π_A` either fixes the image under `s.predAbove` or applies `π` to it.
  have hstep : ∀ x, s.predAbove (πA x) = s.predAbove x ∨
      s.predAbove (πA x) = π (s.predAbove x) := by
    intro x
    induction x using Fin.succAboveCases s.castSucc with
    | x =>
        left
        rw [hnew, Fin.predAbove_succ_self, Fin.predAbove_castSucc_self]
    | p c =>
        right
        rw [hold, hpe', hpe]
  -- The two embeddings of the columns of `G` agree up to the cycles of `π_A`.
  have hee : ∀ d, πA.SameCycle (s.succ.succAbove d) (s.castSucc.succAbove d) := by
    intro d
    rcases lt_trichotomy d s with h | rfl | h
    · rw [Fin.succAbove_succ_of_le _ _ h.le, Fin.succAbove_castSucc_of_lt _ _ h]
    · rw [Fin.succAbove_succ_self, Fin.succAbove_castSucc_self, ← hnew]
      exact hone _
    · rw [Fin.succAbove_succ_of_lt _ _ h, Fin.succAbove_castSucc_of_le _ _ h.le]
  have hadv : ∀ c, πA.SameCycle (s.castSucc.succAbove c) (s.castSucc.succAbove (π c)) := by
    intro c
    have h := hone (s.castSucc.succAbove c)
    rw [hold] at h
    exact h.trans (hee _)
  have hsec : ∀ x, πA.SameCycle x (s.castSucc.succAbove (s.predAbove x)) := by
    intro x
    induction x using Fin.succAboveCases s.castSucc with
    | x =>
        rw [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self, ← hnew]
        exact hone _
    | p c =>
        rw [hpe]
  have hemb : ∀ c d, π.SameCycle c d →
      πA.SameCycle (s.castSucc.succAbove c) (s.castSucc.succAbove d) := by
    intro c d hcd
    obtain ⟨i, rfl⟩ := hcd.exists_nat_pow_eq
    clear hcd
    induction i with
    | zero => exact .refl _ _
    | succ i ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact ih.trans (hadv _)
  refine ⟨fun c => ⟨_, hpe c⟩, fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩⟩
  · obtain ⟨i, rfl⟩ := hxy.exists_nat_pow_eq
    clear hxy
    induction i with
    | zero => exact .refl _ _
    | succ i ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases hstep ((πA ^ i) x) with h | h
        · rw [h]
          exact ih
        · rw [h]
          exact ih.trans (hone' _)
  · exact ((hsec x).trans (hemb _ _ hxy)).trans (hsec y).symm

/-! ### Colour transport data for the south-west corner -/

/-- The canonical stabilization inclusion gives colour transport data from `χ` to
`χ ∘ s.predAbove`. -/
theorem colourTransportData_stabilization_inclusion (χ : Fin n → ℕ) :
    ColourTransportData G χ (G.stabilizeX s.castSucc (G.X s).castSucc s) (χ ∘ s.predAbove) := by
  intro hn _
  have hinl := stabilizationTransferredDifferential_comp_inl G s (ZMod 2)
  set c := fullStabilizationTransferredRetraction G s (ZMod 2) with hc
  have hι' : (c.incl ∘ₗ LinearMap.inl (LaurentPolynomial (ZMod 2)) (LaurentChain (ZMod 2) n)
          (LaurentChain (ZMod 2) n)) ∘ₗ laurentDifferential G (ZMod 2) =
      laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) (ZMod 2) ∘ₗ
        (c.incl ∘ₗ LinearMap.inl (LaurentPolynomial (ZMod 2)) (LaurentChain (ZMod 2) n)
          (LaurentChain (ZMod 2) n)) := by
    rw [LinearMap.comp_assoc, ← hinl, ← LinearMap.comp_assoc, ← c.dM_comp_incl,
      LinearMap.comp_assoc]
  have hι := hι'.symm
  refine ⟨stabilizationCanonicalInclusion (ZMod 2) G s,
    c.incl ∘ₗ LinearMap.inl (LaurentPolynomial (ZMod 2)) (LaurentChain (ZMod 2) n)
      (LaurentChain (ZMod 2) n),
    fun m x => stabilizationCanonicalInclusion_apply (ZMod 2) G s m x, hι,
    stabilizationCanonicalInclusion_shifts (ZMod 2) G s,
    gridCanonicalClass_stabilization G hn s, fun v => ?_⟩
  have h := isNullHomotopic_stabilization_inclusion_colour G s (ZMod 2)
    (colourClass (χ ∘ s.predAbove) v)
  rw [colourClass_preimage _ _ s.castSucc.succAbove_right_injective,
    show (χ ∘ s.predAbove) ∘ s.castSucc.succAbove = χ from
      funext fun c => by simp [Fin.predAbove_succAbove]] at h
  have h' := h.neg
  rwa [neg_sub] at h'

/-- The canonical stabilization projection gives colour transport data from `χ ∘ s.predAbove` to
`χ`. The new column and the column `s.succ` have the same colour `χ s`. -/
theorem colourTransportData_stabilization_projection (χ : Fin n → ℕ) :
    ColourTransportData (G.stabilizeX s.castSucc (G.X s).castSucc s) (χ ∘ s.predAbove) G χ := by
  intro _ hn
  have hfst := fst_comp_stabilizationTransferredDifferential G s (ZMod 2)
  set c := fullStabilizationTransferredRetraction G s (ZMod 2) with hc
  have hπ : laurentDifferential G (ZMod 2) ∘ₗ
        (LinearMap.fst (LaurentPolynomial (ZMod 2)) (LaurentChain (ZMod 2) n)
          (LaurentChain (ZMod 2) n) ∘ₗ c.proj) =
      (LinearMap.fst (LaurentPolynomial (ZMod 2)) (LaurentChain (ZMod 2) n)
          (LaurentChain (ZMod 2) n) ∘ₗ c.proj) ∘ₗ
        laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) (ZMod 2) := by
    apply LinearMap.ext
    intro z
    have h1 := LinearMap.congr_fun c.proj_comp_dM z
    have h2 := LinearMap.congr_fun hfst (c.proj z)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  refine ⟨stabilizationCanonicalProjection (ZMod 2) G s,
    LinearMap.fst (LaurentPolynomial (ZMod 2)) (LaurentChain (ZMod 2) n)
      (LaurentChain (ZMod 2) n) ∘ₗ c.proj,
    fun m x => stabilizationCanonicalProjection_apply (ZMod 2) G s m x, hπ,
    stabilizationCanonicalProjection_shifts (ZMod 2) G s,
    gridCanonicalClass_stabilization_projection G hn s, fun v => ?_⟩
  have hP : s.castSucc ∈ colourClass (χ ∘ s.predAbove) v ↔
      s.succ ∈ colourClass (χ ∘ s.predAbove) v := by
    simp [colourClass]
  have h := isNullHomotopic_stabilization_projection_colour G s (ZMod 2)
    (colourClass (χ ∘ s.predAbove) v) hP
  rwa [colourClass_preimage _ _ s.castSucc.succAbove_right_injective,
    show (χ ∘ s.predAbove) ∘ s.castSucc.succAbove = χ from
      funext fun c => by simp [Fin.predAbove_succAbove]] at h

/-- The canonical inclusion gives a colour pullback from `G` to its south-west corner
stabilization. -/
theorem colourPullback_stabilizeX_castSucc :
    ColourPullback G (G.stabilizeX s.castSucc (G.X s).castSucc s) :=
  .of_componentMap (componentMap_stabilizeX_castSucc G s) fun χ _ =>
    colourTransportData_stabilization_inclusion G s χ

/-- The canonical projection gives a colour pullback from the south-west corner stabilization to
`G`. -/
theorem colourPullback_stabilizeX_castSucc_symm :
    ColourPullback (G.stabilizeX s.castSucc (G.X s).castSucc s) G :=
  .of_componentMap_symm (componentMap_stabilizeX_castSucc G s) fun χ _ =>
    colourTransportData_stabilization_projection G s χ

/-! ### The north-east corner -/

/-- The half-turn, the south-west corner inclusion of `G.rotate` and the inverse half-turn give a
colour pullback from `G` to its north-east corner stabilization. -/
theorem colourPullback_stabilizeX_succ :
    ColourPullback G (G.stabilizeX s.succ (G.X s).succ s) := by
  have h := (colourPullback_halfTurn G).1.trans (colourPullback_stabilizeX_castSucc G.rotate s.rev)
    _root_.id
  rw [← G.rotate_stabilizeX_succ s] at h
  exact h.trans (colourPullback_halfTurn _).2 (fun _ => by omega)

/-- The half-turn, the south-west corner projection of `G.rotate` and the inverse half-turn give a
colour pullback from the north-east corner stabilization of `G` to `G`. -/
theorem colourPullback_stabilizeX_succ_symm :
    ColourPullback (G.stabilizeX s.succ (G.X s).succ s) G := by
  have h := (colourPullback_stabilizeX_castSucc_symm G.rotate s.rev).trans
    (colourPullback_halfTurn G).2 (fun _ => by
      have := grid_size_two_le_of_column G s
      omega)
  rw [← G.rotate_stabilizeX_succ s] at h
  exact (colourPullback_halfTurn _).1.trans h _root_.id

/-! ### All stabilizations -/

variable {G} in
/-- **Colour pullbacks for every stabilization.** If `H` is an elementary stabilization of `G`,
then there are colour pullbacks from `G` to `H` and from `H` to `G`. -/
theorem colourPullback_of_isStabilization {H : GridDiagram (n + 1)}
    (h : GridDiagram.IsStabilization G H) : ColourPullback G H ∧ ColourPullback H G := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · obtain ⟨h₁, h₂⟩ := colourPullback_of_commutationMovesTo hs
    exact ⟨(colourPullback_stabilizeX_castSucc G s).trans h₂ (fun _ => by omega),
      h₁.trans (colourPullback_stabilizeX_castSucc_symm G s) _root_.id⟩
  · obtain ⟨h₁, h₂⟩ := colourPullback_of_commutationMovesTo hs
    exact ⟨(colourPullback_stabilizeX_succ G s).trans h₂ (fun _ => by omega),
      h₁.trans (colourPullback_stabilizeX_succ_symm G s) _root_.id⟩

end OnLeConjecture.KnotFloer.GridFull
