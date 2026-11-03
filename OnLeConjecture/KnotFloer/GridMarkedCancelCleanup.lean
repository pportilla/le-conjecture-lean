/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridMarkedCancelSimple
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-!
# The marked factor cleanup

This file proves `GridFull.MarkedFactorCleanupStatement` (`markedFactorCleanup`), the marked
inverse cancellation of the written proof of Statement E (`statement_E_complete_proof.tex`,
Section 8, Lemma `markedInverseCancellation`) for one factor of a normalized factorization,
together with the reframing of Section 10.

Let `q = A η A⁻¹` be the padded factor, with `A = p γ` and the core `η` on `a` strands. The seam
`Σ(H, framePrep G)` of a protected grid `H` with the frame preparation of a signed word grid `G`
of `q` is a marked word grid of `q` at its last corner (`seam_movesTo_marked`). The marked arc
slides along the strand `0` into the core (`mrelF_entry`), and the marked conjugate reduces to the
marked core with a frame tower of `S - a` blocks over `H` (`mrel_conj_core`).

* For a singular factor, the comparison word `w = A° η A°⁻¹` with `A° = σ_0 σ_0⁻¹ ρ'`, where the
  ladder `ρ'` sends the strand `0` to the strand where it enters the core, reduces to the same
  marked core without blocks. Its frame preparation `P` is related to the word grid of `β`
  (`wordGrid_movesTo_lift`), and `Σ(H', P)` is compared with `Σ(H, E)` through frame towers
  (`seam_tower_movesTo`).
* For a simple factor, `P` is the simple factor of the scissor endpoint, which is an unknotted
  seam summand (`connectedSumSeamGrid_simpleFactor_movesTo`), and `Σ(H', P)` is the marked core
  `σ_0` (`simple_seam_movesTo_marked`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid OnLeConjecture.KnotFloer.GridFull
  SignedAdjacentWord

/-! ### Frame towers exist -/

theorem exists_frameTower {a : ℕ} (P : GridDiagram (a + 1)) (hP : TriplyPrepared P) :
    ∀ j : ℕ, ∃ (b : ℕ) (E : GridDiagram (b + 1)), FrameTower P j E
  | 0 => ⟨a, P, FrameTower.base⟩
  | j + 1 => by
    obtain ⟨b, E, hE⟩ := exists_frameTower P hP j
    have hb : 1 ≤ b := two_le_of_triplyPrepared (hE.triplyPrepared hP)
    exact ⟨b + 2, _, hE.insert 1 1 le_rfl hb le_rfl hb⟩

/-! ### The two chains -/

section Chains

variable {S : ℕ} (hS : 2 ≤ S)

/-- The generator `σ_0` as a letter index. -/
abbrev zeroIdx : Fin (S - 1) := ⟨0, by omega⟩

/-- **The chain of the padded factor.** -/
theorem core_chain (A' η : SignedAdjacentWord S) {a : ℕ} (ha : 2 ≤ a) (haS : a ≤ S)
    (hA : ∀ x, x ≤ S - 1 → RankIn ((zeroIdx hS, 1) :: A') x) (hη : ∀ b ∈ η, b.1.val + 2 ≤ a)
    (hηr : ∀ x, x < a → RankIn η x) {i : ℕ} (hi : i < η.length)
    (hfirst : Occ η (follow 0 ((zeroIdx hS, 1) :: A')) ⟨i, hi⟩ ∧
      ∀ i' (hi' : i' < i), ¬ Occ η (follow 0 ((zeroIdx hS, 1) :: A')) ⟨i', by omega⟩) :
    ∃ c : Fin 3, η.xHeight2 (⟨i, hi⟩, c) = 2 * follow 0 ((zeroIdx hS, 1) :: A') ∧
      MRel (conjugateWord ((zeroIdx hS, 1) :: A') η)
        ((conjugateWord ((zeroIdx hS, 1) :: A') η).length - 1, 2) η (i, c) (S - a) := by
  obtain ⟨c, hc, h1⟩ := mrelF_entry A' η (inv ((zeroIdx hS, 1) :: A')) (zeroIdx hS) rfl
    (inv A') (inv_cons _ _) hi hfirst
  refine ⟨c, hc, ?_⟩
  have h2 := mrel_conj_core ((zeroIdx hS, 1) :: A') η (by omega) haS hA hη hηr hi c
  exact (h1.toMRel.trans (h2.cast rfl (by simp only [List.length_cons]) rfl rfl
    rfl)).cast rfl rfl rfl rfl (Nat.zero_add _)

/-- **The chain of the comparison word.** -/
theorem core_chainF (A' η : SignedAdjacentWord S)
    (hAη : ∀ b ∈ (zeroIdx hS, 1) :: A', RankIn η b.1.val ∧ RankIn η (b.1.val + 1)) {i : ℕ}
    (hi : i < η.length)
    (hfirst : Occ η (follow 0 ((zeroIdx hS, 1) :: A')) ⟨i, hi⟩ ∧
      ∀ i' (hi' : i' < i), ¬ Occ η (follow 0 ((zeroIdx hS, 1) :: A')) ⟨i', by omega⟩) :
    ∃ c : Fin 3, η.xHeight2 (⟨i, hi⟩, c) = 2 * follow 0 ((zeroIdx hS, 1) :: A') ∧
      MRelF (conjugateWord ((zeroIdx hS, 1) :: A') η)
        ((conjugateWord ((zeroIdx hS, 1) :: A') η).length - 1, 2) η (i, c) := by
  obtain ⟨c, hc, h1⟩ := mrelF_entry A' η (inv ((zeroIdx hS, 1) :: A')) (zeroIdx hS) rfl
    (inv A') (inv_cons _ _) hi hfirst
  refine ⟨c, hc, ?_⟩
  have h2 := mrelF_conj_reduce η hi c ((zeroIdx hS, 1) :: A') hAη
  exact h1.trans (h2.cast rfl (by simp only [List.length_cons]) rfl rfl)

end Chains

/-! ### The padding word and the cores -/

section Factors

variable {S : ℕ} (hS : 2 ≤ S)

theorem coxeter_eq_cons :
    coxeterSignedWord S = (zeroIdx hS, 1) :: (coxeterSignedWord S).tail := by
  have hne : coxeterSignedWord S ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [coxeterSignedWord] at this; omega
  rw [← List.cons_head_tail hne]
  congr 1
  rw [List.head_eq_getElem]
  simp [coxeterSignedWord]

theorem mem_coxeter (i : Fin (S - 1)) : (i, (1 : ℤˣ)) ∈ coxeterSignedWord S := by
  simp [coxeterSignedWord]

/-- The padded conjugator starts with `σ_0`. -/
theorem pad_eq_cons (γ : SignedAdjacentWord S) :
    padWord S ++ γ =
      (zeroIdx hS, 1) :: ((coxeterSignedWord S).tail ++ inv (coxeterSignedWord S) ++ γ) := by
  rw [padWord, List.append_assoc]
  nth_rw 1 [coxeter_eq_cons hS]
  simp

include hS in
/-- The padded conjugator uses every strand. -/
theorem pad_rankIn (γ : SignedAdjacentWord S) (x : ℕ) (hx : x ≤ S - 1) :
    RankIn (padWord S ++ γ) x := by
  have hm : ∀ i : Fin (S - 1), (i, (1 : ℤˣ)) ∈ padWord S ++ γ := fun i =>
    List.mem_append_left _ (List.mem_append_left _ (mem_coxeter i))
  by_cases h : x < S - 1
  · exact ⟨(⟨x, h⟩, 1), hm _, Or.inl rfl⟩
  · refine ⟨(⟨S - 2, by omega⟩, 1), hm _, Or.inr ?_⟩
    change x = S - 2 + 1
    omega

theorem lift_letters {a : ℕ} (haS : a ≤ S) (β : PositiveAdjacentWord a) :
    ∀ b ∈ liftPositiveWord haS β, b.1.val + 2 ≤ a := by
  intro b hb
  simp only [liftPositiveWord, List.mem_map] at hb
  obtain ⟨i, -, rfl⟩ := hb
  have := i.isLt
  simp only [Fin.val_castLE]
  omega

theorem lift_rankIn {a : ℕ} (haS : a ≤ S) (ha : 2 ≤ a) (β : PositiveAdjacentWord a)
    (hβ : β.toSigned.generatorIndices = Finset.univ) :
    ∀ x, x < a → RankIn (liftPositiveWord haS β) x := by
  intro x hx
  set r : Fin (a - 1) := ⟨min x (a - 2), by omega⟩ with hr
  have hmem : r ∈ β := by
    have h : r ∈ β.toSigned.generatorIndices := by rw [hβ]; exact Finset.mem_univ r
    simp only [generatorIndices, List.mem_toFinset, List.mem_map,
      PositiveAdjacentWord.toSigned] at h
    obtain ⟨b, hb, e⟩ := h
    obtain ⟨i, hi, rfl⟩ := hb
    simp only at e
    rw [← e]; exact hi
  refine ⟨(Fin.castLE (by omega) r, 1), List.mem_map.mpr ⟨r, hmem, rfl⟩, ?_⟩
  simp only [Fin.val_castLE, hr]
  omega

theorem sigma0_letters : ∀ b ∈ sigma0Word hS, b.1.val + 2 ≤ 2 := by
  intro b hb
  simp only [sigma0Word, List.mem_singleton] at hb
  subst hb; simp

theorem sigma0_rankIn : ∀ x, x < 2 → RankIn (sigma0Word hS) x := by
  intro x hx
  refine ⟨(⟨0, by omega⟩, 1), List.mem_singleton_self _, ?_⟩
  simp only
  omega

end Factors

/-! ### The marked factor cleanup -/

/-- The comparison word of a singular factor on `a` strands. -/
def cmpWord {a : ℕ} (ha : 2 ≤ a) (k : ℕ) (hk : 0 + k ≤ a - 1) : SignedAdjacentWord a :=
  (⟨0, by omega⟩, 1) :: (⟨0, by omega⟩, -1) :: ladder 0 k hk

theorem liftWord_cmpWord {a S : ℕ} (haS : a ≤ S) (ha : 2 ≤ a) (k : ℕ) (hk : 0 + k ≤ a - 1)
    (hk' : 0 + k ≤ S - 1) :
    liftWord haS (cmpWord ha k hk) =
      (⟨0, by omega⟩, 1) :: (⟨0, by omega⟩, -1) :: ladder 0 k hk' := by
  rw [cmpWord, show ((⟨0, by omega⟩, 1) :: (⟨0, by omega⟩, -1) :: ladder 0 k hk :
      SignedAdjacentWord a) = [(⟨0, by omega⟩, 1), (⟨0, by omega⟩, -1)] ++ ladder 0 k hk from rfl,
    liftWord_append, liftWord_ladder haS 0 k hk hk']
  rfl

/-- **The marked factor cleanup** (`GridFull.MarkedFactorCleanupStatement`). -/
theorem markedFactorCleanup : MarkedFactorCleanupStatement := by
  intro S N B hS F hzero l
  set γ := F.conjugator l with hγ
  set A' : SignedAdjacentWord S :=
    (coxeterSignedWord S).tail ++ inv (coxeterSignedWord S) ++ γ with hA'
  have hAeq : padWord S ++ γ = (zeroIdx hS, 1) :: A' := pad_eq_cons hS γ
  have hA_all : ∀ x, x ≤ S - 1 → RankIn ((zeroIdx hS, 1) :: A') x := fun x hx => by
    rw [← hAeq]; exact pad_rankIn hS γ x hx
  have hfac : F.factor l = conjugateWord ((zeroIdx hS, 1) :: A') (F.core l) := by
    rw [NormalizedFactorization.factor, hAeq]
  have hz : (conjugateWord ((zeroIdx hS, 1) :: A') (F.core l)).permutation ⟨0, by omega⟩ ≠
      ⟨0, by omega⟩ := by
    rw [← hfac]; exact hzero l
  by_cases hl : l.val < N
  · -- a singular factor
    set j : Fin N := ⟨l.val, hl⟩ with hj
    have haS := F.strands_le j
    have ha2 := F.two_le_strands j
    set a := F.strands j with ha
    set β := F.word j with hβ
    have hcore : F.core l = liftPositiveWord haS β := by
      simp only [NormalizedFactorization.core, dif_pos hl]; rfl
    have hcyc : F.cycleLength l = a := by
      simp only [NormalizedFactorization.cycleLength, dif_pos hl]; rfl
    set η := liftPositiveWord haS β with hηdef
    have hη := lift_letters haS β
    have hηr := lift_rankIn haS ha2 β (F.word_generators j)
    rw [hcore] at hfac hz
    have hk' := follow_lt_of_perm_ne ((zeroIdx hS, 1) :: A') η hη (by omega) hz
    set k' := follow 0 ((zeroIdx hS, 1) :: A') with hk'def
    obtain ⟨i₁, hi₁, hfirst⟩ := exists_first_occ η (hηr k' hk')
    obtain ⟨c₁, hc₁, hchain⟩ := core_chain hS A' η ha2 haS hA_all hη hηr hi₁ hfirst
    -- the comparison word
    have hkS : 0 + k' ≤ S - 1 := by omega
    have hka : 0 + k' ≤ a - 1 := by omega
    set L : SignedAdjacentWord S := ladder 0 k' hkS with hL
    set B' : SignedAdjacentWord S := (zeroIdx hS, -1) :: L with hB'
    have hfollow : follow 0 ((zeroIdx hS, 1) :: B') = k' := by
      change follow (swapAt (zeroIdx hS, -1) (swapAt (zeroIdx hS, 1) 0)) L = k'
      simp only [swapAt]
      exact follow_ladder_zero k' hkS
    have hAη : ∀ b ∈ (zeroIdx hS, 1) :: B', RankIn η b.1.val ∧ RankIn η (b.1.val + 1) := by
      intro b hb
      simp only [hB', List.mem_cons] at hb
      rcases hb with rfl | rfl | hb
      · exact ⟨hηr _ (by simp; omega), hηr _ (by simp; omega)⟩
      · exact ⟨hηr _ (by simp; omega), hηr _ (by simp; omega)⟩
      · have := ladder_rank 0 k' hkS b hb
        exact ⟨hηr _ (by omega), hηr _ (by omega)⟩
    obtain ⟨c₂, hc₂, hchainF⟩ := core_chainF hS B' η hAη hi₁ (by rw [hfollow]; exact hfirst)
    have hc12 : c₂ = c₁ := by
      apply corner_eq_of_xHeight2 (η[i₁]'hi₁)
      have e1 : η.xHeight2 (⟨i₁, hi₁⟩, c₂) = η.xHeight2 (⟨i₁, hi₁⟩, c₁) := by
        rw [hc₂, hc₁, hfollow]
      exact e1
    rw [hc12] at hchainF
    set w := conjugateWord ((zeroIdx hS, 1) :: B') η with hw
    have hw0 : 0 < w.length := by simp [hw, conjugateWord]
    have hwfst : w[0]'hw0 = (zeroIdx hS, 1) := by simp [hw, conjugateWord]
    have hwlst : w[w.length - 1]'(by omega) = (zeroIdx hS, -1) := by
      rw [← List.getLast_eq_getElem] <;> simp [hw, conjugateWord, inv_cons]
    obtain ⟨G₀, hG₀, hC₀⟩ := exists_closingRowBottom w hw0 (zeroIdx hS) rfl hwfst hwlst
    have hP := framePrep_triplyPrepared G₀ hC₀
    obtain ⟨b, E, hPE⟩ := exists_frameTower (framePrep G₀ hC₀) hP (S - a)
    refine ⟨w.length * 3, framePrep G₀ hC₀, b, E, hP, by rw [hcyc]; exact hPE, ?_, ?_, ?_⟩
    · -- the word grid of `β`
      intro h
      have hlift : liftWord haS (conjugateWord (cmpWord ha2 k' hka) β.toSigned) = w := by
        rw [hw, conjugateWord, conjugateWord, liftWord_append, liftWord_append, liftWord_inv,
          liftWord_cmpWord haS ha2 k' hka hkS, liftWord_toSigned]
      have hm : (wordGrid β).MovesTo G₀ := by
        revert G₀
        rw [← hlift]
        intro G₀ hG₀ _ _ _
        exact wordGrid_movesTo_lift haS ha2 β (F.word_generators j) _ hG₀
      exact hm.trans (movesTo_framePrep G₀ hC₀)
    · intro hN; exact absurd hl (by omega)
    · intro G hGs hC m H hH
      have hL0 : 0 < (F.factor l).length := by rw [hfac]; simp [conjugateWord]
      obtain ⟨M₀, hM₀, hm₀⟩ := seam_movesTo_marked (F.factor l) hL0 G hGs hC H hH
      rw [← hfac] at hchain
      obtain ⟨hp, hp', hrel⟩ := hchain
      obtain ⟨k₁, H₁, hH₁, M₁, ht₁, hM₁, hm₁⟩ := hrel H hH M₀ hM₀
      obtain ⟨M₂, hM₂, hm₂⟩ := seam_movesTo_marked w hw0 G₀ hG₀ hC₀ H₁ hH₁
      obtain ⟨hq, hq', hrelF⟩ := hchainF
      obtain ⟨M₃, hM₃, hm₃⟩ := hrelF H₁ hH₁.1 hH₁.2.1 M₂ hM₂
      have hm13 := IsMarkedGrid.movesTo hM₁ hM₃
      have htower := seam_tower_movesTo hH ht₁ hP hPE
      exact hm₀.trans (hm₁.trans (hm13.trans (hm₃.symm.trans (hm₂.symm.trans htower))))
  · -- a simple factor
    have hcore : F.core l = sigma0Word hS := by
      simp only [NormalizedFactorization.core, dif_neg hl, NormalizedFactorization.firstLetter,
        dif_pos hS]
      rfl
    have hcyc : F.cycleLength l = 2 := by
      simp only [NormalizedFactorization.cycleLength, dif_neg hl]
    set η := sigma0Word hS with hηdef
    have hη := sigma0_letters hS
    have hηr := sigma0_rankIn hS
    rw [hcore] at hfac hz
    have hk' := follow_lt_of_perm_ne ((zeroIdx hS, 1) :: A') η hη (by omega) hz
    obtain ⟨i₁, hi₁, hfirst⟩ := exists_first_occ η (hηr _ hk')
    obtain ⟨c₁, -, hchain⟩ := core_chain hS A' η (le_refl 2) hS hA_all hη hηr hi₁ hfirst
    have hi0 : i₁ = 0 := by have : η.length = 1 := rfl; omega
    subst hi0
    -- the slide to the corner of height `0`
    have hslide : MRelF η (0, c₁) η (0, 1) := by
      have key : ∃ n, (((sM η) ^ n) (s0c hS c₁)) = s0c hS 1 := by
        fin_cases c₁
        · refine ⟨2, ?_⟩
          rw [pow_two, Equiv.Perm.mul_apply]
          simp only [Fin.zero_eta]
          rw [sigma0_sM0, sigma0_sM2]
        · exact ⟨0, rfl⟩
        · refine ⟨1, ?_⟩
          rw [pow_one]
          exact sigma0_sM2 hS
      obtain ⟨n, hn⟩ := key
      have := mrelF_slide_pow η (s0c hS c₁) n
      rw [hn] at this
      exact this
    have hP := simpleFactorGrid_triplyPrepared
    obtain ⟨b, E, hPE⟩ := exists_frameTower simpleFactorGrid hP (S - 2)
    refine ⟨3, simpleFactorGrid, b, E, hP, by rw [hcyc]; exact hPE, ?_, ?_, ?_⟩
    · intro h; exact absurd h hl
    · intro _ m G hG
      exact connectedSumSeamGrid_simpleFactor_movesTo G hG
    · intro G hGs hC m H hH
      have hL0 : 0 < (F.factor l).length := by rw [hfac]; simp [conjugateWord]
      obtain ⟨M₀, hM₀, hm₀⟩ := seam_movesTo_marked (F.factor l) hL0 G hGs hC H hH
      rw [← hfac] at hchain
      obtain ⟨hp, hp', hrel⟩ := hchain
      obtain ⟨k₁, H₁, hH₁, M₁, ht₁, hM₁, hm₁⟩ := hrel H hH M₀ hM₀
      obtain ⟨hs, hs', hrelS⟩ := hslide
      obtain ⟨M₁', hM₁', hm₁'⟩ := hrelS H₁ hH₁.1 hH₁.2.1 M₁ hM₁
      obtain ⟨M₂, hM₂, hm₂⟩ := simple_seam_movesTo_marked hS H₁ hH₁
      have hm12 := IsMarkedGrid.movesTo hM₁' hM₂
      have htower := seam_tower_movesTo hH ht₁ hP hPE
      exact hm₀.trans (hm₁.trans (hm₁'.trans (hm12.trans (hm₂.symm.trans htower))))

end OnLeConjecture.KnotTheory.MarkedCancel
