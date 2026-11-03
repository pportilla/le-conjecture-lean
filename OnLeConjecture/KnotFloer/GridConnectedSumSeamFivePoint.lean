/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamUnweightedPaths
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFivePointModel

/-!
# No long correction path on the five-point seam grid

For `n = m = 2` the seam grid has size five. A native state is sent to its
column-to-row function, and a native rectangle to its ordered column sides.
Under this map every entry, internal transition, and exit of a correction
path satisfies the corresponding test of
`GridConnectedSumSeamFivePointModel`. The model certificates there then
show that no correction path has three or more internal transitions.
This is Lemma `J05:lem:seam-size-five-truncation`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween

/-- The column-to-row function of a state of the five-point grid. -/
def seamFiveOf (x : GridState 5) : Fin 5 → Fin 5 := fun c => x c

theorem seamFiveOf_injective : Function.Injective seamFiveOf := by
  intro x y h
  exact GridState.ext fun c => congrFun h c

/-- The open cyclic interval agrees with the model test. -/
theorem mem_cIoo_iff_seamFiveIoo (a b c : Fin 5) :
    c ∈ Grid.cIoo a b ↔ seamFiveIoo a b c := by
  rw [Grid.mem_cIoo, seamFiveIoo]
  by_cases h : a.val < b.val
  · simp [h]
  · simp [h]

/-- The target of a rectangle exchanges the rows of its source in the two side columns. -/
theorem seamFiveOf_target {x y : GridState 5} (r : GridRectangleBetween x y) :
    seamFiveOf y = seamFiveSwap (seamFiveOf x) r.left r.right := by
  funext c
  simp only [seamFiveOf, seamFiveSwap]
  split_ifs with h₁ h₂
  · subst h₁
    exact r.map_left
  · subst h₂
    exact r.map_right
  · exact r.map_of_ne c h₁ h₂

/-- An empty native rectangle passes the model emptiness test at its ordered sides. -/
theorem seamFiveEmpty_of_isEmpty {x y : GridState 5} (r : GridRectangleBetween x y)
    (hr : r.IsEmpty) : seamFiveEmpty (seamFiveOf x) r.left r.right := by
  rw [isEmpty_iff_forall_notMem_cIoo] at hr
  intro c hc hc'
  exact hr c ((mem_cIoo_iff_seamFiveIoo _ _ _).mpr hc)
    ((mem_cIoo_iff_seamFiveIoo _ _ _).mpr hc')

/-- The pair sector is the model sector. -/
theorem seamPairSector_iff_seamFiveSector (w : GridState (2 + 2 + 1)) :
    SeamPairSector (n := 2) (m := 2) w ↔ seamFiveSector (seamFiveOf w) := by
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h₀, h₁⟩ c
    fin_cases c
    · exact h₀
    · exact h₁

/-- The model computes the first two columns of a southwest column set. -/
theorem seamFiveFirst_second_of_min (f : Fin 5 → Fin 5) (a b : Fin 5)
    (ha : 2 ≤ a.val) (hfa : (f a).val ≤ 2) (hb : 2 ≤ b.val) (hfb : (f b).val ≤ 2)
    (hab : a < b) (hmin : ∀ d : Fin 5, 2 ≤ d.val → (f d).val ≤ 2 → a ≤ d)
    (hmin₂ : ∀ d : Fin 5, 2 ≤ d.val → (f d).val ≤ 2 → d ≠ a → b ≤ d) :
    seamFiveFirst f = a ∧ seamFiveSecond f = b := by
  fin_cases a <;> fin_cases b <;> simp at ha hb hab <;> simp at hfa hfb
  · simp [seamFiveFirst, seamFiveSecond, hfa, hfb]
  · have h₃ : ¬ (f 3).val ≤ 2 := fun h => absurd (hmin₂ 3 (by decide) h (by decide)) (by decide)
    simp [seamFiveFirst, seamFiveSecond, hfa, h₃]
  · have h₂ : ¬ (f 2).val ≤ 2 := fun h => absurd (hmin 2 (by decide) h) (by decide)
    simp [seamFiveFirst, seamFiveSecond, hfa, h₂]

/-- The model computes the first two southwest columns of a complementary state. -/
theorem seamFiveFirst_second_eq (x : SeamComplement 2 2) :
    seamFiveFirst (seamFiveOf x.val) = seamComplementFirst x ∧
      seamFiveSecond (seamFiveOf x.val) = seamComplementSecond x := by
  have ha := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x)
  have hb := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x)
  refine seamFiveFirst_second_of_min _ _ _ ha.1 ha.2 hb.1 hb.2
    (seamComplementFirst_lt_second x) ?_ ?_
  · intro d hd hfd
    exact Finset.min'_le _ d ((mem_seamSouthwestColumns _ _).mpr ⟨hd, hfd⟩)
  · intro d hd hfd hda
    exact Finset.min'_le _ d
      (Finset.mem_erase.mpr ⟨hda, (mem_seamSouthwestColumns _ _).mpr ⟨hd, hfd⟩⟩)

/-- The model partner is the selected partner. -/
theorem seamFiveOf_partner (x : SeamComplement 2 2) :
    seamFiveOf (seamComplementPartner x).val = seamFivePartner (seamFiveOf x.val) := by
  obtain ⟨h₁, h₂⟩ := seamFiveFirst_second_eq x
  funext c
  simp only [seamFivePartner, seamFiveSwap, h₁, h₂]
  change x.val.swapColumns (seamComplementFirst x) (seamComplementSecond x) c = _
  rw [GridState.swapColumns_apply, Equiv.swap_apply_def]
  split_ifs <;> rfl

/-- Every matching source passes the model source test. -/
theorem seamFiveSource_of_matchingSource (x : SeamMatchingSource 2 2) :
    seamFiveSource (seamFiveOf x.val.val) := by
  obtain ⟨h₁, h₂⟩ := seamFiveFirst_second_eq x.val
  refine ⟨fun h => x.val.property ((seamPairSector_iff_seamFiveSector _).mpr h), ?_⟩
  rw [h₁, h₂]
  exact x.property

/-- An internal transition is a model step with the same ordered sides. -/
theorem seamFiveStepAt_of_internal {x z : SeamMatchingSource 2 2}
    (r : SeamInternalRectangle x z) :
    seamFiveStepAt (seamFiveOf x.val.val) r.val.left r.val.right ∧
      seamFiveOf z.val.val = seamFiveNext (seamFiveOf x.val.val) r.val.left r.val.right := by
  have ht := seamFiveOf_target r.val
  have hz : seamFiveOf z.val.val =
      seamFiveNext (seamFiveOf x.val.val) r.val.left r.val.right := by
    have hp := seamFiveOf_partner (seamComplementPartner z.val)
    rw [seamComplementPartner_involutive] at hp
    rw [hp, ht]
    rfl
  refine ⟨⟨r.val.left_ne_right, seamFiveEmpty_of_isEmpty r.val r.property.2, ?_, ?_, ?_⟩, hz⟩
  · rw [← ht]
    exact fun h => (seamComplementPartner z.val).property
      ((seamPairSector_iff_seamFiveSector _).mpr h)
  · rw [← hz]
    exact seamFiveSource_of_matchingSource z
  · rw [← hz]
    intro h
    apply r.property.1
    have he := congrArg seamFiveOfCode h
    rw [seamFiveOfCode_code, seamFiveOfCode_code] at he
    exact Subtype.ext (Subtype.ext (seamFiveOf_injective he.symm))

/-- An entry rectangle from a pair-sector state passes the model entry test. -/
theorem seamFiveHasEntry_of_entry {w : GridState 5} (hw : seamFiveSector (seamFiveOf w))
    {x : SeamMatchingSource 2 2} (r : GridRectangleBetween w (seamComplementPartner x.val).val)
    (hr : r.IsEmpty) : seamFiveHasEntry (seamFiveOf x.val.val) := by
  have ht := seamFiveOf_target r
  rw [seamFiveOf_partner] at ht
  have hw' : seamFiveSwap (seamFivePartner (seamFiveOf x.val.val)) r.left r.right =
      seamFiveOf w := by
    rw [ht, seamFiveSwap_swap]
  refine ⟨r.left, r.right, r.left_ne_right, ?_, ?_⟩
  · rw [hw']
    exact hw
  · rw [hw']
    exact seamFiveEmpty_of_isEmpty r hr

/-- An exit rectangle to a pair-sector state passes the model exit test. -/
theorem seamFiveHasExit_of_exit {w : GridState 5} (hw : seamFiveSector (seamFiveOf w))
    {y : SeamMatchingSource 2 2} (r : GridRectangleBetween y.val.val w) (hr : r.IsEmpty) :
    seamFiveHasExit (seamFiveOf y.val.val) := by
  refine ⟨r.left, r.right, r.left_ne_right, seamFiveEmpty_of_isEmpty r hr, ?_⟩
  rw [← seamFiveOf_target r]
  exact hw

/-- Every matching source with an entry lies in `E_0`. -/
theorem seamFiveCode_mem_E0 {x : SeamMatchingSource 2 2}
    (hx : seamFiveHasEntry (seamFiveOf x.val.val)) :
    seamFiveCode (seamFiveOf x.val.val) ∈ seamFiveE0 := by
  have hinj (i j : Fin 5) (hij : i ≠ j) : seamFiveOf x.val.val i ≠ seamFiveOf x.val.val j :=
    fun he => hij (x.val.val.toPerm.injective he)
  have hs : seamFiveSource (seamFiveOfCode (seamFiveCode (seamFiveOf x.val.val))) := by
    rw [seamFiveOfCode_code]
    exact seamFiveSource_of_matchingSource x
  have he : seamFiveHasEntry (seamFiveOfCode (seamFiveCode (seamFiveOf x.val.val))) := by
    rw [seamFiveOfCode_code]
    exact hx
  exact seamFive_entry_mem_E0 _ _ (hinj 0 1 (by decide)) _ (hinj 0 2 (by decide))
    (hinj 1 2 (by decide)) _ (hinj 0 3 (by decide)) (hinj 1 3 (by decide))
    (hinj 2 3 (by decide)) _ (hinj 0 4 (by decide)) (hinj 1 4 (by decide))
    (hinj 2 4 (by decide)) (hinj 3 4 (by decide)) hs he

/-- On the five-point seam grid no correction path has three or more internal transitions. -/
theorem seamCorrectionPath_two_two_isEmpty {k : ℕ} (hk : 3 ≤ k) (p q : SeamRetainedIndex 2 2) :
    IsEmpty (SeamCorrectionPath (n := 2) (m := 2) k p q) := by
  refine ⟨fun ⟨x, y, ⟨re, hre⟩, path, ⟨rx, hrx⟩⟩ => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  obtain ⟨x₁, r₁, x₂, r₂, x₃, r₃, path₃⟩ := path
  have hp : seamFiveSector (seamFiveOf (seamState p.1 p.2)) :=
    (seamPairSector_iff_seamFiveSector _).mp (seamState_mem_pairSector p.1 p.2)
  have hq : seamFiveSector (seamFiveOf (seamState q.1 q.2)) :=
    (seamPairSector_iff_seamFiveSector _).mp (seamState_mem_pairSector q.1 q.2)
  have h₀ := seamFiveCode_mem_E0 (seamFiveHasEntry_of_entry hp re hre)
  obtain ⟨hs₁, he₁⟩ := seamFiveStepAt_of_internal r₁
  have h₁ : seamFiveCode (seamFiveOf x₁.val.val) ∈ seamFiveE1 := by
    rw [he₁]
    exact seamFive_next_mem_E1 h₀ hs₁
  obtain ⟨hs₂, he₂⟩ := seamFiveStepAt_of_internal r₂
  have h₂ : seamFiveCode (seamFiveOf x₂.val.val) ∈ seamFiveE2 := by
    rw [he₂]
    exact seamFive_next_mem_E2 h₁ hs₂
  obtain ⟨hs₃, he₃⟩ := seamFiveStepAt_of_internal r₃
  have h₃ : seamFiveCode (seamFiveOf x₃.val.val) ∈ seamFiveE3 := by
    rw [he₃]
    exact seamFive_next_mem_E3 h₂ hs₃
  cases j with
  | zero =>
    have hxy : x₃ = y := path₃.property
    subst hxy
    exact seamFive_not_hasExit_of_mem_E3 h₃ (seamFiveHasExit_of_exit hq rx hrx)
  | succ j =>
    obtain ⟨x₄, r₄, -⟩ := path₃
    exact seamFive_not_stepAt_of_mem_E3 h₃ _ _ (seamFiveStepAt_of_internal r₄).1

end OnLeConjecture.KnotFloer.GridFull
