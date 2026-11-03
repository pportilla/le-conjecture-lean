/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorFourMarkMap
public import OnLeConjecture.KnotFloer.GridColourMovesBasic

/-!
# Removing a tower of four-mark blocks

Let `K` be obtained from a grid `G₀` of size at least two by a tower of `k` four-mark insertions
(`FourMarkTower`, `GridExteriorScissorSteps`). Composing the removal maps of the blocks
(`fourMarkRemovalMap`, `GridExteriorFourMarkMap`) gives a Laurent chain map
`M : C(K) → C(G₀)` that raises the Maslov degree by `k` and the second filtration coordinate by
at most `k / 2` (`fourMarkTower_removal`). The blocks are components of `K`. Give the `i`-th
block the colour `i + 1` and every other column the colour `0`. This colouring `χ` is constant on
the components of `K`, and on total homology

  `M_* = Q ∘ Ψ_1 ∘ ⋯ ∘ Ψ_k`,

where `Ψ_v` is the colour derivative of the colour `v` and `Q` carries the canonical class of `K`
to the canonical class of `G₀`. This is the four-mark part of the complete operation count of the
written proof of Statement E (`statement_E_complete_proof.tex`, Section 12).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotFloer

/-! ### Products of operators -/

section Products

variable {R M N C : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- A linear map intertwining the factors intertwines the products. -/
theorem derivativeProduct_intertwine (L : M →ₗ[R] N) (Ψ : C → N →ₗ[R] N) (Ψ' : C → M →ₗ[R] M) :
    ∀ {m : ℕ} (c : Fin m → C), (∀ i, L ∘ₗ Ψ' (c i) = Ψ (c i) ∘ₗ L) →
      L ∘ₗ derivativeProduct Ψ' c = derivativeProduct Ψ c ∘ₗ L
  | 0, _, _ => by rw [derivativeProduct_zero, derivativeProduct_zero, LinearMap.comp_id,
      LinearMap.id_comp]
  | m + 1, c, h => by
    rw [derivativeProduct_succ, derivativeProduct_succ, ← LinearMap.comp_assoc, h 0,
      LinearMap.comp_assoc, derivativeProduct_intertwine L Ψ Ψ' (Fin.tail c)
        (fun i => h i.succ), LinearMap.comp_assoc]

/-- A product over the first `k + 1` values of a sequence is the product over the first `k`
values followed by the last factor applied first. -/
theorem derivativeProduct_val_succ (Ψ : C → M →ₗ[R] M) :
    ∀ (k : ℕ) (f : ℕ → C), derivativeProduct Ψ (fun i : Fin (k + 1) => f i.val) =
      derivativeProduct Ψ (fun i : Fin k => f i.val) ∘ₗ Ψ (f k)
  | 0, f => by
    rw [derivativeProduct_succ, derivativeProduct_zero, derivativeProduct_zero,
      LinearMap.comp_id, LinearMap.id_comp]
    rfl
  | k + 1, f => by
    rw [derivativeProduct_succ, derivativeProduct_succ (c := fun i : Fin (k + 1) => f i.val)]
    have h := derivativeProduct_val_succ Ψ k (fun v => f (v + 1))
    have e1 : Fin.tail (fun i : Fin (k + 1 + 1) => f i.val) =
        fun i : Fin (k + 1) => f (i.val + 1) := rfl
    have e2 : Fin.tail (fun i : Fin (k + 1) => f i.val) = fun i : Fin k => f (i.val + 1) := rfl
    rw [e1, e2, h, LinearMap.comp_assoc]
    rfl

end Products

/-! ### Coordinates of a four-mark insertion -/

section Insertion

variable {n : ℕ} {G : GridDiagram n} {c : Fin n} {K : GridDiagram (n + 2)}

theorem fourMarkEmbedding_val (c j : Fin n) :
    (fourMarkEmbedding c j).val = if j.val < c.val then j.val else j.val + 2 := by
  unfold fourMarkEmbedding
  by_cases hj : j.val < c.val
  · rw [Fin.succAbove_of_castSucc_lt c.castSucc j (by rw [Fin.lt_def]; simpa using hj),
      Fin.succAbove_of_castSucc_lt c.castSucc.succ j.castSucc (by rw [Fin.lt_def]; simp; omega),
      if_pos hj]
    simp
  · rw [Fin.succAbove_of_le_castSucc c.castSucc j (by rw [Fin.le_def]; simp; omega),
      Fin.succAbove_of_le_castSucc c.castSucc.succ j.succ (by rw [Fin.le_def]; simp; omega),
      if_neg hj]
    simp

theorem fourMarkEmbedding_ne_left (c j : Fin n) : fourMarkEmbedding c j ≠ c.castSucc.castSucc := by
  intro h
  have := congrArg Fin.val h
  rw [fourMarkEmbedding_val] at this
  simp only [Fin.val_castSucc] at this
  split_ifs at this <;> omega

theorem fourMarkEmbedding_ne_right (c j : Fin n) : fourMarkEmbedding c j ≠ c.castSucc.succ := by
  intro h
  have := congrArg Fin.val h
  rw [fourMarkEmbedding_val] at this
  simp only [Fin.val_succ, Fin.val_castSucc] at this
  split_ifs at this <;> omega

theorem fourMarkEmbedding_self (c : Fin n) : fourMarkEmbedding c c = c.succ.succ := by
  apply Fin.ext
  rw [fourMarkEmbedding_val, if_neg (lt_irrefl _)]
  simp

/-- Every column of the insertion is a block column or the image of a column of `G`. -/
theorem fourMarkInsertion_cases (c : Fin n) (x : Fin (n + 2)) :
    x = c.castSucc.castSucc ∨ x = c.castSucc.succ ∨ ∃ j, fourMarkEmbedding c j = x := by
  by_cases h0 : x.val = c.val
  · left
    exact Fin.ext (by simpa using h0)
  by_cases h1 : x.val = c.val + 1
  · right; left
    exact Fin.ext (by simpa using h1)
  right; right
  by_cases h2 : x.val < c.val
  · refine ⟨⟨x.val, by omega⟩, Fin.ext ?_⟩
    rw [fourMarkEmbedding_val, if_pos h2]
  · refine ⟨⟨x.val - 2, by omega⟩, Fin.ext ?_⟩
    rw [fourMarkEmbedding_val, if_neg (by simp only; omega)]
    simp only
    omega

theorem fourMarkInsertion_O_embedding (hK : IsFourMarkInsertion G c K) (j : Fin n) :
    K.O (fourMarkEmbedding c j) = fourMarkEmbedding (G.X c) (G.O j) := by
  rw [hK.1]
  unfold fourMarkEmbedding
  rw [GridState.insertPoint_apply_succAbove, GridState.insertPoint_apply_succAbove]

theorem fourMarkInsertion_X_embedding (hK : IsFourMarkInsertion G c K) (j : Fin n) :
    K.X (fourMarkEmbedding c j) = fourMarkEmbedding (G.X c) (G.X j) := by
  rw [hK.2, GridState.swapRows_apply]
  have hne1 := fourMarkEmbedding_ne_left (G.X c) (G.X j)
  have hne2 := fourMarkEmbedding_ne_right (G.X c) (G.X j)
  unfold fourMarkEmbedding at hne1 hne2 ⊢
  rw [GridState.insertPoint_apply_succAbove, GridState.insertPoint_apply_succAbove]
  exact Equiv.swap_apply_of_ne_of_ne hne1 hne2

theorem fourMarkInsertion_O_castSucc_castSucc (hK : IsFourMarkInsertion G c K) :
    K.O c.castSucc.castSucc = (G.X c).castSucc.castSucc := by
  have e1 : c.castSucc.castSucc = c.castSucc.succ.succAbove c.castSucc :=
    (Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp)).symm
  rw [hK.1, e1, GridState.insertPoint_apply_succAbove, GridState.insertPoint_apply_newColumn]
  exact Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp)

theorem fourMarkInsertion_O_castSucc_succ (hK : IsFourMarkInsertion G c K) :
    K.O c.castSucc.succ = (G.X c).castSucc.succ := by
  rw [hK.1, GridState.insertPoint_apply_newColumn]

theorem gridComponentPerm_apply_eq_iff {m : ℕ} (G : GridDiagram m) (x y : Fin m) :
    gridComponentPerm G x = y ↔ G.X y = G.O x := by
  unfold gridComponentPerm
  rw [Equiv.trans_apply, Equiv.symm_apply_eq]
  exact eq_comm

theorem fourMarkInsertion_componentPerm_embedding (hK : IsFourMarkInsertion G c K) (j : Fin n) :
    gridComponentPerm K (fourMarkEmbedding c j) = fourMarkEmbedding c (gridComponentPerm G j) := by
  rw [gridComponentPerm_apply_eq_iff, fourMarkInsertion_X_embedding hK,
    fourMarkInsertion_O_embedding hK, (gridComponentPerm_apply_eq_iff G j _).mp rfl]

theorem fourMarkInsertion_componentPerm_left (hK : IsFourMarkInsertion G c K) :
    gridComponentPerm K c.castSucc.castSucc = c.castSucc.succ := by
  rw [gridComponentPerm_apply_eq_iff, fourMarkInsertion_X_castSucc_succ hK,
    fourMarkInsertion_O_castSucc_castSucc hK]

theorem fourMarkInsertion_componentPerm_right (hK : IsFourMarkInsertion G c K) :
    gridComponentPerm K c.castSucc.succ = c.castSucc.castSucc := by
  rw [gridComponentPerm_apply_eq_iff, fourMarkInsertion_X_castSucc_castSucc hK,
    fourMarkInsertion_O_castSucc_succ hK, Fin.succ_castSucc]

/-! ### The colouring of an insertion -/

/-- The colouring of the insertion that extends `χ` and gives both block columns the colour
`v`. -/
def fourMarkColouring (c : Fin n) (χ : Fin n → ℕ) (v : ℕ) (x : Fin (n + 2)) : ℕ :=
  open Classical in
  if h : ∃ j, fourMarkEmbedding c j = x then χ h.choose else v

theorem fourMarkColouring_embedding (c : Fin n) (χ : Fin n → ℕ) (v : ℕ) (j : Fin n) :
    fourMarkColouring c χ v (fourMarkEmbedding c j) = χ j := by
  have h : ∃ j', fourMarkEmbedding c j' = fourMarkEmbedding c j := ⟨j, rfl⟩
  rw [fourMarkColouring, dif_pos h]
  exact congrArg χ (fourMarkEmbedding_injective c h.choose_spec)

theorem fourMarkColouring_left (c : Fin n) (χ : Fin n → ℕ) (v : ℕ) :
    fourMarkColouring c χ v c.castSucc.castSucc = v := by
  rw [fourMarkColouring, dif_neg]
  rintro ⟨j, hj⟩
  exact fourMarkEmbedding_ne_left c j hj

theorem fourMarkColouring_right (c : Fin n) (χ : Fin n → ℕ) (v : ℕ) :
    fourMarkColouring c χ v c.castSucc.succ = v := by
  rw [fourMarkColouring, dif_neg]
  rintro ⟨j, hj⟩
  exact fourMarkEmbedding_ne_right c j hj

theorem fourMarkColouring_comp_embedding (c : Fin n) (χ : Fin n → ℕ) (v : ℕ) :
    fourMarkColouring c χ v ∘ fourMarkEmbedding c = χ :=
  funext fun j => fourMarkColouring_embedding c χ v j

theorem componentColouring_fourMarkColouring (hK : IsFourMarkInsertion G c K) {χ : Fin n → ℕ}
    (hχ : ComponentColouring G χ) (v : ℕ) : ComponentColouring K (fourMarkColouring c χ v) := by
  intro x
  rcases fourMarkInsertion_cases c x with rfl | rfl | ⟨j, rfl⟩
  · rw [fourMarkInsertion_componentPerm_left hK, fourMarkColouring_right,
      fourMarkColouring_left]
  · rw [fourMarkInsertion_componentPerm_right hK, fourMarkColouring_right,
      fourMarkColouring_left]
  · rw [fourMarkInsertion_componentPerm_embedding hK, fourMarkColouring_embedding,
      fourMarkColouring_embedding, hχ j]

/-- If `χ` does not take the value `v`, the colour class of `v` is the block. -/
theorem colourClass_fourMarkColouring_self (c : Fin n) {χ : Fin n → ℕ} {v : ℕ}
    (hv : ∀ j, χ j ≠ v) :
    colourClass (fourMarkColouring c χ v) v =
      {c.castSucc.castSucc, finRotate (n + 2) c.castSucc.castSucc} := by
  ext x
  rw [finRotate_castSucc_castSucc]
  simp only [colourClass, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  rcases fourMarkInsertion_cases c x with rfl | rfl | ⟨j, rfl⟩
  · simp [fourMarkColouring_left]
  · simp [fourMarkColouring_right]
  · rw [fourMarkColouring_embedding]
    exact iff_of_false (hv j) (by
      rintro (h | h)
      · exact fourMarkEmbedding_ne_left c j h
      · exact fourMarkEmbedding_ne_right c j h)

end Insertion

/-! ### The tower -/

section Tower

theorem laurentTotalHomologyMapHet_id {n : ℕ} {G H : GridDiagram n}
    (h : laurentDifferential H (ZMod 2) ∘ₗ LinearMap.id =
      LinearMap.id ∘ₗ laurentDifferential G (ZMod 2)) (ξ : laurentTotalHomology G (ZMod 2)) :
    laurentTotalHomologyMapHet (LinearMap.id :
      LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n) h ξ =
      laurentTotalHomologyMap LinearMap.id h ξ := rfl

/-- **Removing a tower of four-mark blocks.** -/
theorem fourMarkTower_removal {n₀ : ℕ} {G₀ : GridDiagram n₀} (hn₀ : 2 ≤ n₀) {k m : ℕ}
    {G : GridDiagram m} {e : Fin n₀ → Fin m} (h : FourMarkTower G₀ k G e) :
    n₀ ≤ m ∧ ∃ (M : LaurentChain (ZMod 2) m →ₗ[LaurentPolynomial (ZMod 2)]
        LaurentChain (ZMod 2) n₀)
      (hM : laurentDifferential G₀ (ZMod 2) ∘ₗ M = M ∘ₗ laurentDifferential G (ZMod 2))
      (χ : Fin m → ℕ)
      (Qt : laurentTotalHomology G (ZMod 2) →ₗ[LaurentPolynomial (ZMod 2)]
        laurentTotalHomology G₀ (ZMod 2)),
      PieceShift G G₀ G.alexander G₀.alexander M k ((k : ℝ) / 2) ∧
      ComponentColouring G χ ∧ (∀ b, χ (e b) = 0) ∧ (∀ x, χ x ≤ k) ∧
      (∀ i : Fin k, ∃ x, χ x = i.val + 1) ∧
      (∀ hm : 2 ≤ m, Qt (totalCanonicalClass G hm) = totalCanonicalClass G₀ hn₀) ∧
      ∀ ξ, laurentTotalHomologyMapHet M hM ξ =
        Qt (derivativeProduct (fun v => totalODerivative G (colourClass χ v))
          (fun i : Fin k => i.val + 1) ξ) := by
  induction h with
  | base =>
    refine ⟨le_rfl, LinearMap.id, by rw [LinearMap.id_comp, LinearMap.comp_id],
      fun _ => 0, LinearMap.id, ?_, fun _ => rfl, fun _ => rfl, fun _ => le_rfl,
      fun i => i.elim0, fun _ => rfl, fun ξ => ?_⟩
    · have h0 : PieceShift G₀ G₀ G₀.alexander G₀.alexander
          (LinearMap.id : LaurentChain (ZMod 2) n₀ →ₗ[LaurentPolynomial (ZMod 2)] _) 0 0 :=
        PieceShift.of_levelShift (fun m x hx => by simpa using hx)
          (levelShift_id fun x => by simp)
      exact h0.congr rfl (by simp) (by simp)
    · rw [laurentTotalHomologyMapHet_id, laurentTotalHomologyMap_id]
      rfl
  | @insert k m' G e h b G' hG' ih =>
    obtain ⟨hle, M, hM, χ, Qt, hshift, hχ, he0, hlek, hex, hcan, hfac⟩ := ih
    have hm' : 2 ≤ m' := le_trans hn₀ hle
    set c := e b with hc
    have hMb := laurentDifferential_comp_fourMarkRemovalMap hG'
    have hQb := laurentDifferential_comp_fourMarkNormalizationMap hG'
    refine ⟨by omega, M ∘ₗ fourMarkRemovalMap G c G', laurentChainHet_comp hMb hM,
      fourMarkColouring c χ (k + 1),
      Qt ∘ₗ laurentTotalHomologyMapHet (fourMarkNormalizationMap G c G') hQb, ?_,
      componentColouring_fourMarkColouring hG' hχ (k + 1), fun b' => ?_, fun x => ?_,
      fun i => ?_, fun hm => ?_, fun ξ => ?_⟩
    · refine ((pieceShift_fourMarkRemovalMap hG' hm').comp hshift).congr rfl (by push_cast; ring)
        (by push_cast; ring)
    · change fourMarkColouring c χ (k + 1) (fourMarkEmbedding c (e b')) = 0
      rw [fourMarkColouring_embedding, he0]
    · rcases fourMarkInsertion_cases c x with rfl | rfl | ⟨j, rfl⟩
      · rw [fourMarkColouring_left]
      · rw [fourMarkColouring_right]
      · rw [fourMarkColouring_embedding]
        exact le_trans (hlek j) (Nat.le_succ k)
    · by_cases hi : i.val < k
      · obtain ⟨x, hx⟩ := hex ⟨i.val, hi⟩
        exact ⟨fourMarkEmbedding c x, by rw [fourMarkColouring_embedding, hx]⟩
      · refine ⟨c.castSucc.castSucc, ?_⟩
        rw [fourMarkColouring_left]
        omega
    · rw [LinearMap.comp_apply, fourMarkNormalizationMap_totalCanonicalClass hG' hm']
      exact hcan hm'
    · rw [laurentTotalHomologyMapHet_comp_apply hMb hM, hfac, fourMarkRemovalMap_total_apply hG',
        LinearMap.comp_apply]
      congr 1
      have hnat : ∀ i : Fin k,
          laurentTotalHomologyMapHet (fourMarkNormalizationMap G c G') hQb ∘ₗ
              totalODerivative G' (colourClass (fourMarkColouring c χ (k + 1)) (i.val + 1)) =
            totalODerivative G (colourClass χ (i.val + 1)) ∘ₗ
              laurentTotalHomologyMapHet (fourMarkNormalizationMap G c G') hQb := by
        intro i
        apply LinearMap.ext
        intro η
        have hik : i.val + 1 ≠ k + 1 := by omega
        have h0 : c.castSucc.castSucc ∉
            colourClass (fourMarkColouring c χ (k + 1)) (i.val + 1) := by
          simp only [colourClass, Finset.mem_filter, Finset.mem_univ, true_and,
            fourMarkColouring_left]
          omega
        have h1 : c.castSucc.succ ∉ colourClass (fourMarkColouring c χ (k + 1)) (i.val + 1) := by
          simp only [colourClass, Finset.mem_filter, Finset.mem_univ, true_and,
            fourMarkColouring_right]
          omega
        have h2 : c.succ.succ ∉ colourClass (fourMarkColouring c χ (k + 1)) (i.val + 1) := by
          rw [← fourMarkEmbedding_self]
          simp only [colourClass, Finset.mem_filter, Finset.mem_univ, true_and,
            fourMarkColouring_embedding, hc, he0]
          omega
        rw [LinearMap.comp_apply, LinearMap.comp_apply,
          fourMarkNormalizationMap_totalODerivative hG' _ h0 h1 h2,
          colourClass_preimage _ _ (fourMarkEmbedding_injective c),
          fourMarkColouring_comp_embedding]
      have hint := derivativeProduct_intertwine
        (laurentTotalHomologyMapHet (fourMarkNormalizationMap G c G') hQb)
        (fun v => totalODerivative G (colourClass χ v))
        (fun v => totalODerivative G' (colourClass (fourMarkColouring c χ (k + 1)) v))
        (fun i : Fin k => i.val + 1) hnat
      have hlast := derivativeProduct_val_succ
        (fun v => totalODerivative G' (colourClass (fourMarkColouring c χ (k + 1)) v)) k
        (fun v => v + 1)
      have hblock := colourClass_fourMarkColouring_self c (χ := χ) (v := k + 1)
        (fun j => by have := hlek j; omega)
      rw [hlast, LinearMap.comp_apply, ← LinearMap.comp_apply (derivativeProduct _ _), ← hint,
        LinearMap.comp_apply]
      rw [hblock]

end Tower

end OnLeConjecture.KnotFloer.GridFull
