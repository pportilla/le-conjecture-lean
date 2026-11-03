/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.ScissorSequenceComponents

/-!
# Corners of a factor inside a product of padded factors

For a family `q` of padded signed words and a factor `l`, the corner `p = (h, c)` of the word
`q l` is the corner `globC q l p = (o_l + h, c)` of the product `factorProduct q`, where `o_l` is
the offset of the factor (`factorOffset`). Heights and occurrences of ranks agree
(`oHeight2_globC`, `xHeight2_globC`). The first and the last occurrence of a rank in `q l` give the
local corners `lfC` and `llC`, which are the corners `firstCorner` and `lastCorner` of the product.

The matching `sM` of the product and the matching of the factor agree on every corner except the
last corners (`sM_globC_of_ne`), and in the factor the arc of the last corner of a rank ends at
its first corner (`sM_llC`). These facts compare the scissor endpoint of Section 9 of the written
proof of Statement E (`statement_E_complete_proof.tex`) with the signed word grids of the separate
factors (Section 10, "The raw scissor endpoint is already this cyclic grid"). All results are
unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti SignedAdjacentWord

variable {S r : ℕ} (q : Fin r → SignedAdjacentWord S)

/-- The corner of the product corresponding to a corner of the factor `l`. -/
def globC (l : Fin r) (p : Fin (q l).length × Fin 3) : Fin (factorProduct q).length × Fin 3 :=
  (⟨factorOffset q l.val + p.1.val, by have := factorOffset_succ_le q l; have := p.1.isLt; omega⟩,
    p.2)

theorem globC_fst_val (l : Fin r) (p : Fin (q l).length × Fin 3) :
    (globC q l p).1.val = factorOffset q l.val + p.1.val := rfl

theorem globC_snd (l : Fin r) (p : Fin (q l).length × Fin 3) : (globC q l p).2 = p.2 := rfl

theorem globC_injective (l : Fin r) : Function.Injective (globC q l) := by
  intro p p' h
  have h1 := congrArg (fun x => x.1.val) h
  have h2 := congrArg Prod.snd h
  simp only [globC_fst_val] at h1
  exact Prod.ext (Fin.ext (by omega)) h2

theorem getElem_globC (l : Fin r) (p : Fin (q l).length × Fin 3) :
    (factorProduct q)[(globC q l p).1.val] = (q l)[p.1.val] :=
  getElem_factorProduct q l p.1.val p.1.isLt

theorem oHeight2_globC (l : Fin r) (p : Fin (q l).length × Fin 3) :
    (factorProduct q).oHeight2 (globC q l p) = (q l).oHeight2 p := by
  simp only [SignedAdjacentWord.oHeight2, globC_snd]
  rw [getElem_globC]

theorem xHeight2_globC (l : Fin r) (p : Fin (q l).length × Fin 3) :
    (factorProduct q).xHeight2 (globC q l p) = (q l).xHeight2 p := by
  simp only [SignedAdjacentWord.xHeight2, globC_snd]
  rw [getElem_globC]

theorem segOf_globC (l : Fin r) (p : Fin (q l).length × Fin 3) :
    segOf q (globC q l p).1 = l := by
  apply segOf_eq
  · simp [globC_fst_val]
  · rw [globC_fst_val, factorOffset_succ]; have := p.1.isLt; omega

/-- Every corner of the product is the corner of a factor. -/
theorem exists_globC (p : Fin (factorProduct q).length × Fin 3) :
    ∃ (l : Fin r) (p' : Fin (q l).length × Fin 3), globC q l p' = p := by
  refine ⟨segOf q p.1, (⟨p.1.val - factorOffset q (segOf q p.1).val, ?_⟩, p.2), ?_⟩
  · have h1 := factorOffset_segOf_le q p.1
    have h2 := lt_factorOffset_segOf q p.1
    rw [factorOffset_succ] at h2
    omega
  · have h1 := factorOffset_segOf_le q p.1
    apply Prod.ext
    · apply Fin.ext; simp only [globC_fst_val]; omega
    · rfl

variable (hq : ∀ l, IsPadded (q l)) (hS : 2 ≤ S)

/-- The incoming corner of the first occurrence of a rank in a factor, as a corner of the
factor. -/
def lfC (l : Fin r) (x : Fin S) : Fin (q l).length × Fin 3 :=
  (⟨x.val - 1, by have := (hq l).length_ge; have := x.isLt; omega⟩, if x.val = 0 then 0 else 1)

/-- The outgoing corner of the last occurrence of a rank in a factor, as a corner of the factor. -/
def llC (l : Fin r) (x : Fin S) : Fin (q l).length × Fin 3 :=
  (⟨(q l).length - max x.val 1, by have := (hq l).length_ge; have := x.isLt; omega⟩,
    if x.val = 0 then 2 else 1)

theorem globC_lfC (l : Fin r) (x : Fin S) : globC q l (lfC q hq hS l x) = firstCorner q hq hS l x :=
  rfl

theorem globC_llC (l : Fin r) (x : Fin S) :
    globC q l (llC q hq hS l x) = lastCorner q hq hS l x := by
  apply Prod.ext
  · apply Fin.ext
    simp only [globC_fst_val, lastCorner, llC]
    have := (hq l).length_ge; have := x.isLt
    omega
  · rfl

theorem llC_snd_ne (l : Fin r) (x : Fin S) : (llC q hq hS l x).2 ≠ 0 := by
  simp only [llC]; split_ifs <;> decide

/-- **The arc of a last corner inside its factor** ends at the first corner of the same rank. -/
theorem sM_llC (l : Fin r) (x : Fin S) : sM (q l) (llC q hq hS l x) = lfC q hq hS l x := by
  have hh : (q l).xHeight2 (lfC q hq hS l x) = (q l).oHeight2 (llC q hq hS l x) := by
    rw [← xHeight2_globC, ← oHeight2_globC, globC_lfC q hq hS, globC_llC q hq hS,
      xHeight2_firstCorner, oHeight2_lastCorner]
  apply sM_eq_of_spec _ _ _ (llC_snd_ne q hq hS l x) hh
  right
  have hx2 : (q l).oHeight2 (llC q hq hS l x) / 2 = x.val := by
    rw [← oHeight2_globC, globC_llC q hq hS, oHeight2_lastCorner]; omega
  have hlen := (hq l).length_ge
  have hxS := x.isLt
  refine ⟨by rw [Fin.le_def]; simp only [lfC, llC]; omega, fun k hk => ?_⟩
  rw [hx2] at hk
  have hocc : ¬ (((factorProduct q)[factorOffset q l.val + k.val]'(by
      have := factorOffset_succ_le q l; have := k.isLt; omega)).1.val = x.val ∨
      ((factorProduct q)[factorOffset q l.val + k.val]'(by
      have := factorOffset_succ_le q l; have := k.isLt; omega)).1.val + 1 = x.val) → False := by
    intro h
    apply h
    rw [getElem_factorProduct q l k.val k.isLt]
    exact hk
  constructor
  · rw [Fin.le_def]
    by_contra hcon
    push Not at hcon
    exact hocc (not_occ_before_first q hq hS l x _ _ (by omega)
      (by simp only [firstCorner, lfC] at hcon ⊢; omega))
  · rw [Fin.le_def]
    by_contra hcon
    push Not at hcon
    exact hocc (not_occ_after_last q hq hS l x _ _
      (by simp only [lastCorner, llC] at hcon ⊢; omega)
      (by rw [factorOffset_succ]; have := k.isLt; omega))

/-- **The matching of a factor.** On every corner of a factor other than its last corners, the
matching of the product is the matching of the factor. -/
theorem sM_globC_of_ne (l : Fin r) (p : Fin (q l).length × Fin 3)
    (hp : ∀ x, p ≠ llC q hq hS l x) :
    sM (factorProduct q) (globC q l p) = globC q l (sM (q l) p) := by
  by_cases h0 : p.2 = 0
  · obtain ⟨h, c⟩ := p
    simp only at h0
    subst h0
    rw [sM_middle (q l) h]
    exact sM_middle (factorProduct q) (globC q l (h, 0)).1
  · set gp := globC q l p with hgp
    have hseg : segOf q gp.1 = l := segOf_globC q l p
    have hne : gp ≠ lastCorner q hq hS (segOf q gp.1) (exitStrand q gp) := by
      rw [hseg, ← globC_llC q hq hS]
      exact fun h => hp _ (globC_injective q l h)
    obtain ⟨hlt, hseg', hnone⟩ := sM_of_ne_lastCorner q hq hS (p := gp) h0 hne
    set t := sM (factorProduct q) gp with ht
    have ht1 := factorOffset_segOf_le q t.1
    have ht2 := lt_factorOffset_segOf q t.1
    rw [hseg', hseg] at ht1 ht2
    rw [factorOffset_succ] at ht2
    have hlocal : t.1.val - factorOffset q l.val < (q l).length := by omega
    set tl : Fin (q l).length × Fin 3 := (⟨t.1.val - factorOffset q l.val, hlocal⟩, t.2)
    have htl : globC q l tl = t := by
      apply Prod.ext
      · apply Fin.ext; simp only [globC_fst_val, tl]; omega
      · rfl
    rw [← htl]
    congr 1
    symm
    have hheight : (q l).xHeight2 tl = (q l).oHeight2 p := by
      rw [← xHeight2_globC, ← oHeight2_globC, htl, ht]
      exact sM_height _ _
    apply sM_eq_of_spec _ _ _ h0 hheight
    left
    have hlt' : p.1.val < tl.1.val := by
      have : gp.1.val < t.1.val := hlt
      simp only [hgp, globC_fst_val, tl] at this ⊢
      omega
    refine ⟨hlt', fun k hk hpk => ?_⟩
    rw [Fin.le_def]
    by_contra hcon
    push Not at hcon
    have hk2 : ((q l).oHeight2 p) / 2 = exitRank (factorProduct q) gp := by
      have e1 : (factorProduct q).oHeight2 gp = (q l).oHeight2 p := oHeight2_globC q l p
      have e2 := oHeight2_eq_exitRank (factorProduct q) (p := gp) h0
      omega
    rw [hk2] at hk
    apply hnone (factorOffset q l.val + k.val) (by have := factorOffset_succ_le q l
                                                   have := k.isLt; omega)
    · simp only [hgp, globC_fst_val]
      have : p.1.val < k.val := hpk
      omega
    · simp only [tl] at hcon
      omega
    · rw [getElem_factorProduct q l k.val k.isLt]
      exact hk

end OnLeConjecture.KnotTheory.SignedGrid
