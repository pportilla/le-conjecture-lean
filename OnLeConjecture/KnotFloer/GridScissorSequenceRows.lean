/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorScissorSteps
public import OnLeConjecture.KnotTheory.PositiveWordGridMovesLabeled

/-!
# Row operations of the scissor phase

This file provides the row calculus used to build the scissor phase `ScissorPhase` of
`GridExteriorScissorSteps` (Section 9 of the written proof of Statement E,
`statement_E_complete_proof.tex`, subsection "Signed word grids and the scissor switches").

A grid diagram is determined by two permutations of its columns (`phaseGrid`): the permutation
`σ` sending a row `i` to the column of its `O` marking, and the component permutation `μ`
(`gridComponentPerm`), which sends a column `c` to the column of the `X` marking in the row of the
`O` marking of `c`. Every grid diagram has this form (`eq_phaseGrid`). In these coordinates

* a row commutation of the rows `u` and `v` replaces `σ` by `σ * swap u v` and keeps `μ`
  (`phaseGrid_swapRows`);
* an adjacent-row `X` switch replaces `μ` by `μ * swap (σ u) (σ v)` and keeps `σ`
  (`phaseGrid_xSwitch_X`);
* an adjacent-row `O` switch replaces both, `σ` by `σ * swap u v` and `μ` by
  `μ * swap (σ u) (σ v)` (`phaseGrid_oSwitch_O`).

Hence an `O` switch followed by the commutation of the same two rows has the same endpoint as the
`X` switch (`ScissorPhase.oSwitch_comm`). The rows are noninterleaving exactly when the four
columns `σ u, μ (σ u), σ v, μ (σ v)` are (`rowsNoninterleaving_phaseGrid`).

Row orders are described by lists of columns (`listPerm`). Exchanging two consecutive entries is a
row commutation (`isRowCommutation_listPerm`), and a block of consecutive entries whose rows are
pairwise noninterleaving can be put in any order by row commutations
(`reflTransGen_rowCommutation_perm`). The main result is the star rule of Section 9
(`ScissorPhase.star`): a center row `c` above a list of leaf rows exchanges its `X` marking with
each leaf in turn, using an `X` switch or an `O` switch followed by a row commutation, as
prescribed by a selection, and moves below each leaf after the exchange. All results are
unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory

variable {n : ℕ}

/-! ### Composition of scissor phases -/

namespace ScissorPhase

/-- Scissor phases compose. -/
theorem trans {G G₁ G₂ : GridDiagram n} {k k' : ℕ} {E E' : List (Fin n × Fin n)}
    (h₁ : ScissorPhase G G₁ k E) (h₂ : ScissorPhase G₁ G₂ k' E') :
    ScissorPhase G G₂ (k + k') (E ++ E') := by
  induction h₂ with
  | refl => simpa using h₁
  | xSwitch _ r hr hO hX ih => exact .xSwitch ih r hr hO hX
  | oSwitch _ r hr hO hX ih =>
    rw [← List.append_assoc]; exact .oSwitch ih r hr hO hX
  | rowCommutation _ hc ih => exact .rowCommutation ih hc
  | cyclicRows _ hc ih => exact .cyclicRows ih hc

/-- A scissor phase extends by any finite sequence of row commutations. -/
theorem of_rowCommutations {G G₁ G₂ : GridDiagram n} {k : ℕ} {E : List (Fin n × Fin n)}
    (h : ScissorPhase G G₁ k E) (hc : Relation.ReflTransGen GridDiagram.IsRowCommutation G₁ G₂) :
    ScissorPhase G G₂ k E := by
  induction hc with
  | refl => exact h
  | tail _ hc ih => exact .rowCommutation ih hc

end ScissorPhase

/-! ### Grids given by the row order of the `O` markings and the component permutation -/

/-- The grid whose row `i` carries the `O` marking of the column `σ i`, and whose `X` marking in
the row of the `O` marking of a column `c` lies in the column `μ c`. -/
def phaseGrid (σ μ : Equiv.Perm (Fin n)) (hμ : ∀ c, μ c ≠ c) : GridDiagram n where
  O := ⟨σ.symm⟩
  X := ⟨μ.symm.trans σ.symm⟩
  disjoint c h := by
    have h' : σ.symm c = σ.symm (μ.symm c) := h
    have e : c = μ.symm c := σ.symm.injective h'
    apply hμ c
    calc μ c = μ (μ.symm c) := by rw [← e]
      _ = c := Equiv.apply_symm_apply _ _

section PhaseGrid

variable (σ μ : Equiv.Perm (Fin n)) (hμ : ∀ c, μ c ≠ c)

@[simp] theorem phaseGrid_O_apply (c : Fin n) : (phaseGrid σ μ hμ).O c = σ.symm c := rfl

@[simp] theorem phaseGrid_X_apply (c : Fin n) : (phaseGrid σ μ hμ).X c = σ.symm (μ.symm c) := rfl

theorem phaseGrid_O_transpose (r : Fin n) : (phaseGrid σ μ hμ).O.transpose r = σ r := rfl

theorem phaseGrid_X_transpose (r : Fin n) : (phaseGrid σ μ hμ).X.transpose r = μ (σ r) := rfl

/-- The component permutation of `phaseGrid σ μ` is `μ`. -/
theorem gridComponentPerm_phaseGrid : gridComponentPerm (phaseGrid σ μ hμ) = μ := by
  refine Equiv.ext fun c => ?_
  change ((μ.symm.trans σ.symm).symm (σ.symm c)) = μ c
  simp

/-- Every grid diagram is the grid of the row order of its `O` markings and its component
permutation. -/
theorem gridComponentPerm_ne (G : GridDiagram n) (c : Fin n) : gridComponentPerm G c ≠ c := by
  intro h
  have h' : G.X.toPerm.symm (G.O.toPerm c) = c := h
  apply G.disjoint c
  conv_rhs => rw [← h']
  rw [Equiv.apply_symm_apply]

theorem eq_phaseGrid (G : GridDiagram n) :
    G = phaseGrid G.O.toPerm.symm (gridComponentPerm G) (gridComponentPerm_ne G) := by
  apply GridDiagram.ext
  · exact GridState.ext fun c => rfl
  · refine GridState.ext fun c => ?_
    change G.X.toPerm c = G.O.toPerm.symm.symm ((G.O.toPerm.trans G.X.toPerm.symm).symm c)
    simp

/-- Exchanging two rows of `phaseGrid σ μ` composes `σ` with their transposition. -/
theorem phaseGrid_swapRows (u v : Fin n) :
    (phaseGrid σ μ hμ).swapRows u v = phaseGrid (σ * Equiv.swap u v) μ hμ := by
  apply GridDiagram.ext
  · refine GridState.ext fun c => ?_
    change Equiv.swap u v (σ.symm c) = (σ * Equiv.swap u v).symm c
    simp [Equiv.Perm.mul_def, Equiv.symm_swap]
  · refine GridState.ext fun c => ?_
    change Equiv.swap u v (σ.symm (μ.symm c)) = (σ * Equiv.swap u v).symm (μ.symm c)
    simp [Equiv.Perm.mul_def, Equiv.symm_swap]

/-- Two rows of `phaseGrid σ μ` are noninterleaving exactly when the columns of their markings
are. -/
theorem rowsNoninterleaving_phaseGrid (u v : Fin n) :
    (phaseGrid σ μ hμ).RowsNoninterleaving u v ↔
      Grid.Noninterleaving (σ u) (μ (σ u)) (σ v) (μ (σ v)) := Iff.rfl

/-- Conjugating a transposition by `σ`. -/
theorem symm_swap_conj_apply (u v x : Fin n) :
    σ.symm (Equiv.swap (σ u) (σ v) x) = Equiv.swap u v (σ.symm x) := by
  rw [Equiv.swap_apply_apply]
  simp [Equiv.Perm.mul_apply]

/-- The `X` markings of the grid after an `X` switch of the rows `u` and `v`. -/
theorem phaseGrid_xSwitch_X (u v : Fin n)
    (hμ' : ∀ c, (μ * Equiv.swap (σ u) (σ v)) c ≠ c) :
    (phaseGrid σ (μ * Equiv.swap (σ u) (σ v)) hμ').X = (phaseGrid σ μ hμ).X.swapRows u v := by
  refine GridState.ext fun c => ?_
  rw [phaseGrid_X_apply, GridState.swapRows_apply, phaseGrid_X_apply]
  simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  exact symm_swap_conj_apply σ u v (μ.symm c)

/-- The `O` markings of the grid after an `O` switch of the rows `u` and `v`. -/
theorem phaseGrid_oSwitch_O (u v : Fin n) (hμ' : ∀ c, (μ * Equiv.swap (σ u) (σ v)) c ≠ c) :
    (phaseGrid (σ * Equiv.swap u v) (μ * Equiv.swap (σ u) (σ v)) hμ').O =
      (phaseGrid σ μ hμ).O.swapRows u v := by
  refine GridState.ext fun c => ?_
  change (σ * Equiv.swap u v).symm c = Equiv.swap u v (σ.symm c)
  simp [Equiv.Perm.mul_def, Equiv.symm_swap]

/-- The `X` markings of the grid after an `O` switch of the rows `u` and `v`. -/
theorem phaseGrid_oSwitch_X (u v : Fin n) (hμ' : ∀ c, (μ * Equiv.swap (σ u) (σ v)) c ≠ c) :
    (phaseGrid (σ * Equiv.swap u v) (μ * Equiv.swap (σ u) (σ v)) hμ').X =
      (phaseGrid σ μ hμ).X := by
  refine GridState.ext fun c => ?_
  rw [phaseGrid_X_apply, phaseGrid_X_apply]
  simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  rw [symm_swap_conj_apply, Equiv.swap_apply_self]

end PhaseGrid

/-! ### Row orders given by lists -/

section ListPerm

variable (l : List (Fin n)) (hnd : l.Nodup) (hl : l.length = n)

/-- The permutation sending a position to the entry of a list of distinct columns. -/
def listPerm : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i : Fin n => l[i.val]'(by rw [hl]; exact i.isLt))
    (Finite.injective_iff_bijective.mp (fun i j h => Fin.ext ((hnd.getElem_inj_iff).mp h)))

theorem listPerm_apply (i : Fin n) : listPerm l hnd hl i = l[i.val]'(by rw [hl]; exact i.isLt) :=
  rfl

include hnd hl in
/-- Every column is an entry of the list. -/
theorem mem_of_listPerm (c : Fin n) : c ∈ l := by
  obtain ⟨i, rfl⟩ := (listPerm l hnd hl).surjective c
  rw [listPerm_apply]
  exact List.getElem_mem _

/-- The list of the columns of the rows of a grid, from bottom to top. -/
def rowList (G : GridDiagram n) : List (Fin n) := (List.finRange n).map G.O.toPerm.symm

theorem rowList_nodup (G : GridDiagram n) : (rowList G).Nodup :=
  (List.nodup_finRange n).map G.O.toPerm.symm.injective

theorem rowList_length (G : GridDiagram n) : (rowList G).length = n := by simp [rowList]

theorem listPerm_rowList (G : GridDiagram n) :
    listPerm (rowList G) (rowList_nodup G) (rowList_length G) = G.O.toPerm.symm := by
  refine Equiv.ext fun i => ?_
  simp [listPerm_apply, rowList]

/-- `listPerm` depends only on the list. -/
theorem listPerm_congr {l l' : List (Fin n)} (h : l = l') (h₁ : l.Nodup) (h₂ : l.length = n)
    (h₁' : l'.Nodup) (h₂' : l'.length = n) : listPerm l h₁ h₂ = listPerm l' h₁' h₂' := by
  subst h; rfl

/-- `phaseGrid` depends only on the two permutations. -/
theorem phaseGrid_congr {σ σ' μ μ' : Equiv.Perm (Fin n)} (hσ : σ = σ') (hμ : μ = μ')
    (h : ∀ c, μ c ≠ c) (h' : ∀ c, μ' c ≠ c) : phaseGrid σ μ h = phaseGrid σ' μ' h' := by
  subst hσ hμ; rfl

end ListPerm

section Swap

variable {m₁ m₂ : List (Fin n)} {a b : Fin n}

theorem listPerm_swap (hnd : (m₁ ++ a :: b :: m₂).Nodup) (hl : (m₁ ++ a :: b :: m₂).length = n)
    (hnd' : (m₁ ++ b :: a :: m₂).Nodup) (hl' : (m₁ ++ b :: a :: m₂).length = n) :
    listPerm (m₁ ++ b :: a :: m₂) hnd' hl' =
      listPerm (m₁ ++ a :: b :: m₂) hnd hl *
        Equiv.swap ⟨m₁.length, by simp at hl; omega⟩ ⟨m₁.length + 1, by simp at hl; omega⟩ := by
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.mul_apply, listPerm_apply, listPerm_apply, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; simp
  · subst h2; simp
  · exact LabeledGrid.getElem_append_cons_cons_of_ne _ _ _ _ _ (fun he => h1 (Fin.ext he))
      (fun he => h2 (Fin.ext he)) _

theorem listPerm_at_left (hnd : (m₁ ++ a :: b :: m₂).Nodup)
    (hl : (m₁ ++ a :: b :: m₂).length = n) :
    listPerm (m₁ ++ a :: b :: m₂) hnd hl ⟨m₁.length, by simp at hl; omega⟩ = a := by
  simp [listPerm_apply]

theorem listPerm_at_right (hnd : (m₁ ++ a :: b :: m₂).Nodup)
    (hl : (m₁ ++ a :: b :: m₂).length = n) :
    listPerm (m₁ ++ a :: b :: m₂) hnd hl ⟨m₁.length + 1, by simp at hl; omega⟩ = b := by
  simp [listPerm_apply]

theorem finRotate_at (hl : (m₁ ++ a :: b :: m₂).length = n) :
    finRotate n ⟨m₁.length, by simp at hl; omega⟩ = ⟨m₁.length + 1, by simp at hl; omega⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hl; omega⟩
  exact GridMoves.finRotate_eq_of_val_eq_succ rfl

theorem ne_finRotate_at (hl : (m₁ ++ a :: b :: m₂).length = n) :
    (⟨m₁.length, by simp at hl; omega⟩ : Fin n) ≠
      finRotate n ⟨m₁.length, by simp at hl; omega⟩ := by
  rw [finRotate_at hl]
  intro h
  have := congrArg Fin.val h
  simp at this

/-- **Exchange of two consecutive rows.** If the rows of the consecutive entries `a` and `b` are
noninterleaving, exchanging them is a row commutation. -/
theorem isRowCommutation_listPerm (μ : Equiv.Perm (Fin n)) (hμ : ∀ c, μ c ≠ c)
    (hnd : (m₁ ++ a :: b :: m₂).Nodup) (hl : (m₁ ++ a :: b :: m₂).length = n)
    (hnd' : (m₁ ++ b :: a :: m₂).Nodup) (hl' : (m₁ ++ b :: a :: m₂).length = n)
    (hni : NonintN a.val (μ a).val b.val (μ b).val) :
    GridDiagram.IsRowCommutation (phaseGrid (listPerm _ hnd hl) μ hμ)
      (phaseGrid (listPerm _ hnd' hl') μ hμ) := by
  refine (GridDiagram.isRowCommutation_iff _ _).mpr ⟨_, ne_finRotate_at hl, ?_, ?_⟩
  · rw [finRotate_at hl, rowsNoninterleaving_phaseGrid, listPerm_at_left, listPerm_at_right,
      noninterleaving_iff_nonintN]
    exact hni
  · rw [finRotate_at hl, phaseGrid_swapRows, listPerm_swap hnd hl hnd' hl']

end Swap

/-! ### Reordering a block of pairwise noninterleaving rows -/

/-- **Reordering a block of rows.** If the rows of the entries of a block `M` of consecutive entries
are pairwise noninterleaving, the block can be put in the order of any permutation `M'` of it by
row commutations. -/
theorem reflTransGen_rowCommutation_perm (μ : Equiv.Perm (Fin n)) (hμ : ∀ c, μ c ≠ c)
    {M M' : List (Fin n)} (hp : M.Perm M')
    (hni : ∀ a ∈ M, ∀ b ∈ M, a ≠ b → NonintN a.val (μ a).val b.val (μ b).val) :
    ∀ (m₁ m₂ : List (Fin n)) (hnd : (m₁ ++ M ++ m₂).Nodup) (hl : (m₁ ++ M ++ m₂).length = n)
      (hnd' : (m₁ ++ M' ++ m₂).Nodup) (hl' : (m₁ ++ M' ++ m₂).length = n),
      Relation.ReflTransGen GridDiagram.IsRowCommutation (phaseGrid (listPerm _ hnd hl) μ hμ)
        (phaseGrid (listPerm _ hnd' hl') μ hμ) := by
  induction hp with
  | nil => intro m₁ m₂ _ _ _ _; exact Relation.ReflTransGen.refl
  | cons x _ ih =>
    intro m₁ m₂ hnd hl hnd' hl'
    have e : ∀ L : List (Fin n), m₁ ++ x :: L ++ m₂ = (m₁ ++ [x]) ++ L ++ m₂ := by simp
    have := ih (fun a ha b hb => hni a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      (m₁ ++ [x]) m₂ (by rw [← e]; exact hnd) (by rw [← e]; exact hl)
      (by rw [← e]; exact hnd') (by rw [← e]; exact hl')
    rwa [← listPerm_congr (e _) hnd hl, ← listPerm_congr (e _) hnd' hl'] at this
  | swap x y L =>
    intro m₁ m₂ hnd hl hnd' hl'
    have e1 : m₁ ++ y :: x :: L ++ m₂ = m₁ ++ y :: x :: (L ++ m₂) := by simp
    have e2 : m₁ ++ x :: y :: L ++ m₂ = m₁ ++ x :: y :: (L ++ m₂) := by simp
    have hxy : y ≠ x := by
      intro h; subst h
      have := (List.nodup_append.mp (e1 ▸ hnd)).2.1
      simp at this
    have h := isRowCommutation_listPerm μ hμ (m₁ := m₁) (m₂ := L ++ m₂) (a := y) (b := x)
      (by rw [← e1]; exact hnd) (by rw [← e1]; exact hl) (by rw [← e2]; exact hnd')
      (by rw [← e2]; exact hl') (hni y (by simp) x (by simp) hxy)
    apply Relation.ReflTransGen.single
    rwa [← listPerm_congr e1 hnd hl, ← listPerm_congr e2 hnd' hl'] at h
  | @trans L₁ L₂ L₃ h₁ h₂ ih₁ ih₂ =>
    intro m₁ m₂ hnd hl hnd' hl'
    have hnd₁ : (m₁ ++ L₂ ++ m₂).Nodup := by
      have := (List.Perm.append_right m₂ (List.Perm.append_left m₁ h₁)).nodup_iff.mp hnd
      exact this
    have hl₁ : (m₁ ++ L₂ ++ m₂).length = n :=
      ((List.Perm.append_right m₂ (List.Perm.append_left m₁ h₁)).length_eq).symm.trans hl
    exact (ih₁ hni m₁ m₂ hnd hl hnd₁ hl₁).trans
      (ih₂ (fun a ha b hb => hni a (h₁.symm.subset ha) b (h₁.symm.subset hb)) m₁ m₂ hnd₁ hl₁
        hnd' hl')

/-! ### The star rule -/

section Star

/-- One star stage: the center row `c` lies just above the leaf row `z`. Its `X` marking is
exchanged with that of `z`, by an `X` switch (`o = false`) or by an `O` switch followed by a row
commutation (`o = true`), and then the center row is moved below the leaf row. -/
theorem ScissorPhase.star_step {G : GridDiagram n} {k : ℕ} {E : List (Fin n × Fin n)}
    (μ : Equiv.Perm (Fin n)) (hμ : ∀ c, μ c ≠ c) {m₁ m₂ : List (Fin n)} {z c : Fin n}
    (hnd : (m₁ ++ z :: c :: m₂).Nodup) (hl : (m₁ ++ z :: c :: m₂).length = n)
    (hnd' : (m₁ ++ c :: z :: m₂).Nodup) (hl' : (m₁ ++ c :: z :: m₂).length = n)
    (hμ' : ∀ d, (μ * Equiv.swap z c) d ≠ d)
    (hni : NonintN c.val (μ z).val z.val (μ c).val) (o : Bool)
    (h : ScissorPhase G (phaseGrid (listPerm _ hnd hl) μ hμ) k E) :
    ScissorPhase G (phaseGrid (listPerm _ hnd' hl') (μ * Equiv.swap z c) hμ')
      (k + if o then 0 else 1) (E ++ if o then [(z, c)] else []) := by
  set u : Fin n := ⟨m₁.length, by simp at hl; omega⟩ with hu
  have hσu : listPerm _ hnd hl u = z := listPerm_at_left hnd hl
  have hσv : listPerm _ hnd hl (finRotate n u) = c := by
    rw [finRotate_at hl]
    exact listPerm_at_right hnd hl
  have hne := ne_finRotate_at hl (m₁ := m₁) (m₂ := m₂) (a := z) (b := c)
  -- The grid after the exchange, before the final row commutation.
  have hμ'' : ∀ d,
      (μ * Equiv.swap (listPerm _ hnd hl u) (listPerm _ hnd hl (finRotate n u))) d ≠ d :=
    by rw [hσu, hσv]; exact hμ'
  have hmid : ScissorPhase G (phaseGrid (listPerm _ hnd hl) (μ * Equiv.swap z c) hμ')
      (k + if o then 0 else 1) (E ++ if o then [(z, c)] else []) := by
    cases o with
    | false =>
      simp only [Bool.false_eq_true, if_false, List.append_nil]
      refine .xSwitch h u hne rfl ?_
      have := phaseGrid_xSwitch_X (listPerm _ hnd hl) μ hμ u (finRotate n u) hμ''
      simp only [hσu, hσv] at this
      exact this
    | true =>
      simp only [if_true, Nat.add_zero]
      -- the `O` switch
      have hO := ScissorPhase.oSwitch (G₂ := phaseGrid (listPerm _ hnd hl * Equiv.swap u
        (finRotate n u)) (μ * Equiv.swap z c) hμ') h u hne (by
          have := phaseGrid_oSwitch_O (listPerm _ hnd hl) μ hμ u (finRotate n u) hμ''
          simp only [hσu, hσv] at this
          exact this) (by
          have := phaseGrid_oSwitch_X (listPerm _ hnd hl) μ hμ u (finRotate n u) hμ''
          simp only [hσu, hσv] at this
          exact this)
      rw [phaseGrid_O_transpose, phaseGrid_O_transpose, hσu, hσv] at hO
      refine .rowCommutation hO ((GridDiagram.isRowCommutation_iff _ _).mpr ⟨u, hne, ?_, ?_⟩)
      · rw [rowsNoninterleaving_phaseGrid, noninterleaving_iff_nonintN]
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
        rw [hσu, hσv, Equiv.swap_apply_left, Equiv.swap_apply_right]
        exact hni
      · rw [phaseGrid_swapRows, mul_assoc, Equiv.swap_mul_self, mul_one]
  refine hmid.rowCommutation ?_
  convert isRowCommutation_listPerm (μ * Equiv.swap z c) hμ' hnd hl hnd' hl' ?_ using 1
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact nonintN_comm.mp hni

/-- The edges recorded by the star rule: the leaves selected for an `O` switch, each paired with
the center. -/
def starEdges (c : Fin n) (sel : Fin n → Bool) (L : List (Fin n)) : List (Fin n × Fin n) :=
  (L.filter sel).map fun z => (z, c)

/-- The number of `X` switches of the star rule. -/
def starXCount (sel : Fin n → Bool) (L : List (Fin n)) : ℕ := (L.filter fun z => !sel z).length

/-- The component permutation after the star rule. -/
def starPerm (μ : Equiv.Perm (Fin n)) (c : Fin n) (L : List (Fin n)) : Equiv.Perm (Fin n) :=
  μ * (L.map fun z => Equiv.swap z c).prod

/-- The consecutive pairs of a list headed by `c`. -/
def starPairs (c : Fin n) (L : List (Fin n)) : List (Fin n × Fin n) := (c :: L).zip L

theorem starPerm_cons (μ : Equiv.Perm (Fin n)) (c z : Fin n) (L : List (Fin n)) :
    starPerm μ c (z :: L) = starPerm (μ * Equiv.swap z c) c L := by
  simp [starPerm, mul_assoc]

/-- **The star rule.** The center row `c` lies above the leaf rows `L.reverse`, so that the first
leaf of `L` is just below `c`. For each leaf `z` in turn, the `X` markings of `c` and `z` are
exchanged, by an `X` switch or by an `O` switch and a row commutation as prescribed by `sel`, and
the center row is moved below `z`. The conditions are stated with the original component
permutation `μ`: when `z` is processed, the center row ends at `μ u`, where `u` is the previous
leaf (or `c` itself for the first leaf). -/
theorem ScissorPhase.star (c : Fin n) (sel : Fin n → Bool) :
    ∀ (L : List (Fin n)) (μ : Equiv.Perm (Fin n)) (hμ : ∀ d, μ d ≠ d)
      (_ : ∀ L₁ L₂ : List (Fin n), ∀ z, L = L₁ ++ z :: L₂ →
        ∀ d, starPerm μ c (L₁ ++ [z]) d ≠ d)
      (_ : ∀ L₁ L₂ : List (Fin n), ∀ z, L = L₁ ++ z :: L₂ →
        NonintN c.val (starPerm μ c L₁ z).val z.val (starPerm μ c L₁ c).val)
      {G : GridDiagram n} {k : ℕ} {E : List (Fin n × Fin n)} (m₁ m₂ : List (Fin n))
      (hnd : (m₁ ++ L.reverse ++ c :: m₂).Nodup) (hl : (m₁ ++ L.reverse ++ c :: m₂).length = n)
      (hnd' : (m₁ ++ c :: (L.reverse ++ m₂)).Nodup)
      (hl' : (m₁ ++ c :: (L.reverse ++ m₂)).length = n)
      (hfin : ∀ d, starPerm μ c L d ≠ d),
      ScissorPhase G (phaseGrid (listPerm _ hnd hl) μ hμ) k E →
        ScissorPhase G (phaseGrid (listPerm _ hnd' hl') (starPerm μ c L) hfin)
          (k + starXCount sel L) (E ++ starEdges c sel L) := by
  intro L
  induction L with
  | nil =>
    intro μ hμ _ _ G k E m₁ m₂ hnd hl hnd' hl' hfin h
    simp only [List.reverse_nil, List.append_nil, List.nil_append] at hnd hl ⊢
    simpa [starXCount, starEdges, starPerm] using h
  | cons z L ih =>
    intro μ hμ hfp hni G k E m₁ m₂ hnd hl hnd' hl' hfin h
    have e1 : m₁ ++ (z :: L).reverse ++ c :: m₂ = (m₁ ++ L.reverse) ++ z :: c :: m₂ := by simp
    have e2 : (m₁ ++ L.reverse) ++ c :: z :: m₂ = m₁ ++ L.reverse ++ c :: (z :: m₂) := by simp
    have e3 : m₁ ++ c :: ((z :: L).reverse ++ m₂) = m₁ ++ c :: (L.reverse ++ z :: m₂) := by simp
    have hnd₁ : ((m₁ ++ L.reverse) ++ z :: c :: m₂).Nodup := by rw [← e1]; exact hnd
    have hl₁ : ((m₁ ++ L.reverse) ++ z :: c :: m₂).length = n := by rw [← e1]; exact hl
    have hperm : ((m₁ ++ L.reverse) ++ z :: c :: m₂).Perm ((m₁ ++ L.reverse) ++ c :: z :: m₂) :=
      List.Perm.append_left _ (List.Perm.swap c z m₂)
    have hnd₂ : ((m₁ ++ L.reverse) ++ c :: z :: m₂).Nodup := hperm.nodup_iff.mp hnd₁
    have hl₂ : ((m₁ ++ L.reverse) ++ c :: z :: m₂).length = n := by rw [← hperm.length_eq, hl₁]
    have hμ₁ : ∀ d, (μ * Equiv.swap z c) d ≠ d := by
      have := hfp [] L z rfl; simpa [starPerm] using this
    have hstep := ScissorPhase.star_step μ hμ hnd₁ hl₁ hnd₂ hl₂ hμ₁
      (by have := hni [] L z rfl; simpa [starPerm] using this) (sel z)
      (by rwa [listPerm_congr e1 hnd hl hnd₁ hl₁] at h)
    have hih := ih (μ * Equiv.swap z c) hμ₁
      (fun L₁ L₂ z' hL d => by
        have := hfp (z :: L₁) L₂ z' (by rw [hL]; rfl) d
        rwa [List.cons_append, starPerm_cons] at this)
      (fun L₁ L₂ z' hL => by
        have := hni (z :: L₁) L₂ z' (by rw [hL]; rfl)
        rwa [starPerm_cons] at this)
      m₁ (z :: m₂) (by rw [← e2]; exact hnd₂) (by rw [← e2]; exact hl₂)
      (by rw [← e3]; exact hnd') (by rw [← e3]; exact hl')
      (by rw [← starPerm_cons]; exact hfin) hstep
    have hX : k + starXCount sel (z :: L) = (k + if sel z then 0 else 1) + starXCount sel L := by
      cases hz : sel z <;> simp [starXCount, hz]; omega
    have hE : E ++ starEdges c sel (z :: L) =
        (E ++ if sel z then [(z, c)] else []) ++ starEdges c sel L := by
      cases hz : sel z <;> simp [starEdges, hz]
    rw [hX, hE, phaseGrid_congr (listPerm_congr e3 hnd' hl' _ _) (starPerm_cons μ c z L) hfin _]
    exact hih

end Star

end OnLeConjecture.KnotFloer.GridFull
