/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.ScissorSequenceProduct
public import OnLeConjecture.KnotTheory.ScissorSequenceOrbits

/-!
# Components of the scissor endpoint

This file identifies the components of the endpoint of the star scissors of Section 9 of the
written proof of Statement E (`statement_E_complete_proof.tex`, subsection "The explicit forest for
O-switch selection").

Let `q_0, …, q_{r-1}` be padded factors with permutations `π_l`. At the scissor endpoint the arc
of the last outgoing corner of every rank `x ≥ 1` of a factor returns to the first incoming corner
of that rank in the same factor, and all other arcs are those of the signed word grid of the
product. Every corner carries a *strand label* (`strandLabel`): the index of its factor and the
initial position, in that factor, of the strand through its column. Following an arc keeps the
label, except at the last corners, where the label changes by the merged permutation
`segPerm q` (`mergePerm` of the `π_l` at the strand `0`). Hence two corners lie in one orbit of
the endpoint matching exactly when their labels lie in one orbit of `segPerm q`
(`sameCycle_iff_strandLabel`). All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti SignedAdjacentWord Equiv

variable {S r : ℕ} (q : Fin r → SignedAdjacentWord S) (hq : ∀ l, IsPadded (q l)) (hS : 2 ≤ S)

/-! ### Arcs inside a factor -/

/-- The exit rank of a corner as a strand. -/
def exitStrand (p : Fin (factorProduct q).length × Fin 3) : Fin S :=
  ⟨exitRank (factorProduct q) p, exitRank_lt _ p⟩

/-- **Arcs inside a factor.** An integer arc that does not start at a last corner of its factor
ends in the same factor, at a later letter, and no letter in between involves its rank. -/
theorem sM_of_ne_lastCorner {p : Fin (factorProduct q).length × Fin 3} (hp : p.2 ≠ 0)
    (hne : p ≠ lastCorner q hq hS (segOf q p.1) (exitStrand q p)) :
    p.1 < (sM (factorProduct q) p).1 ∧ segOf q (sM (factorProduct q) p).1 = segOf q p.1 ∧
      ∀ k (hk : k < (factorProduct q).length), p.1.val < k →
        k < (sM (factorProduct q) p).1.val →
        ¬ (((factorProduct q)[k].1).val = exitRank (factorProduct q) p ∨
          ((factorProduct q)[k].1).val + 1 = exitRank (factorProduct q) p) := by
  set l := segOf q p.1
  set x := exitStrand q p
  set Z := lastCorner q hq hS l x
  have hev : (factorProduct q).oHeight2 p = 2 * x.val := oHeight2_eq_exitRank (factorProduct q) hp
  have hx2 : (factorProduct q).oHeight2 p / 2 = x.val := by rw [hev]; omega
  have hoccp : Occ (factorProduct q) x.val p.1 := by
    have := occ_of_oHeight2 (factorProduct q) hp; rwa [hx2] at this
  have h1 : factorOffset q l.val ≤ p.1.val := factorOffset_segOf_le q p.1
  have h2 : p.1.val < factorOffset q (l.val + 1) := lt_factorOffset_segOf q p.1
  have hZ2 : Z.1.val < factorOffset q (l.val + 1) := by
    have := (hq l).length_ge; have := x.isLt
    simp only [Z, lastCorner]; rw [factorOffset_succ]; omega
  have hpZ : p.1.val < Z.1.val := by
    rcases Nat.lt_trichotomy p.1.val Z.1.val with h | h | h
    · exact h
    · exfalso
      apply hne
      exact eq_of_oHeight2_eq (factorProduct q) (Fin.ext h) (by rw [hev, oHeight2_lastCorner])
    · exact absurd hoccp (not_occ_after_last q hq hS l x p.1.val p.1.isLt h h2)
  have hoccZ : Occ (factorProduct q) x.val Z.1 := occ_lastCorner q hq hS l x
  rcases sM_spec (factorProduct q) p hp with ⟨hlt, hmin⟩ | ⟨_, hall⟩
  · rw [hx2] at hmin
    have htZ : (sM (factorProduct q) p).1.val ≤ Z.1.val := hmin Z.1 hoccZ (by rw [Fin.lt_def]; exact hpZ)
    refine ⟨hlt, ?_, fun k hk hk1 hk2 hocc => ?_⟩
    · exact segOf_eq q (by have : p.1.val < (sM (factorProduct q) p).1.val := hlt; omega) (by omega)
    · have := hmin ⟨k, hk⟩ hocc (by rw [Fin.lt_def]; exact hk1)
      rw [Fin.le_def] at this
      exact absurd this (not_le.mpr hk2)
  · rw [hx2] at hall
    have := (hall Z.1 hoccZ).2
    rw [Fin.le_def] at this
    omega

/-! ### Strand labels -/

/-- The strand label of a corner: its factor and the initial position, in that factor, of the
strand through its column. -/
def strandLabel (p : Fin (factorProduct q).length × Fin 3) : Fin r × Fin S :=
  (segOf q p.1, (prefixPerm q (segOf q p.1).val)⁻¹ (glabel (factorProduct q) p))

theorem strandLabel_two (h : Fin (factorProduct q).length) :
    strandLabel q (h, 2) = strandLabel q (h, 0) := by
  simp only [strandLabel, glabel_two]

include hq in
theorem strandLabel_lastCorner (l : Fin r) (x : Fin S) :
    strandLabel q (lastCorner q hq hS l x) = (l, permutation (q l) x) := by
  have hlen := (hq l).length_ge
  have hx := x.isLt
  simp only [strandLabel, segOf_lastCorner]
  congr 1
  rw [glabel_eq_exit]
  have he : (⟨exitRank (factorProduct q) (lastCorner q hq hS l x), exitRank_lt _ _⟩ : Fin S) = x :=
    Fin.ext (exitRank_lastCorner q hq hS l x)
  rw [he]
  have hZ : (lastCorner q hq hS l x).1.val + 1 ≤ factorOffset q (l.val + 1) := by
    simp only [lastCorner]; rw [factorOffset_succ]; omega
  rw [← permutation_take_eq_of_not_occ (factorProduct q) hZ (factorOffset_le q _) x
    (fun k hk h1 h2 => not_occ_after_last q hq hS l x k hk (by omega) h2)]
  change (prefixPerm q l.val)⁻¹ (prefixPerm q (l.val + 1) x) = _
  rw [prefixPerm_succ, Perm.mul_apply]
  simp

include hq in
theorem strandLabel_firstCorner (l : Fin r) (x : Fin S) :
    strandLabel q (firstCorner q hq hS l x) = (l, x) := by
  simp only [strandLabel, segOf_firstCorner]
  congr 1
  unfold glabel
  have he : (⟨enterRank (factorProduct q) (firstCorner q hq hS l x), enterRank_lt _ _⟩ : Fin S) =
      x := Fin.ext (enterRank_firstCorner q hq hS l x)
  rw [he]
  have hF : factorOffset q l.val ≤ (firstCorner q hq hS l x).1.val := by simp [firstCorner]
  rw [permutation_take_eq_of_not_occ (factorProduct q) hF (by
      have := (firstCorner q hq hS l x).1.isLt; omega) x
    (fun k hk h1 h2 => not_occ_before_first q hq hS l x k hk h1 h2)]
  change (prefixPerm q l.val)⁻¹ (prefixPerm q l.val x) = x
  simp

/-- An arc inside a factor keeps the strand label. -/
theorem strandLabel_sM_of_ne {p : Fin (factorProduct q).length × Fin 3} (hp : p.2 ≠ 0)
    (hne : p ≠ lastCorner q hq hS (segOf q p.1) (exitStrand q p)) :
    strandLabel q (sM (factorProduct q) p) = strandLabel q p := by
  obtain ⟨hlt, hseg, hnone⟩ := sM_of_ne_lastCorner q hq hS hp hne
  simp only [strandLabel, hseg]
  congr 1
  have ht2 : (sM (factorProduct q) p).2 ≠ 2 := fun h => by
    have := (xHeight2_odd_iff (factorProduct q) (sM (factorProduct q) p)).mpr h
    rw [sM_height, oHeight2_eq_exitRank (factorProduct q) hp] at this; omega
  have he : (⟨enterRank (factorProduct q) (sM (factorProduct q) p), enterRank_lt _ _⟩ : Fin S) =
      exitStrand q p := by
    apply Fin.ext
    have h1 := xHeight2_eq_enterRank (factorProduct q) ht2
    rw [sM_height, oHeight2_eq_exitRank (factorProduct q) hp] at h1
    simp only [exitStrand]; omega
  have e1 : glabel (factorProduct q) (sM (factorProduct q) p) =
      permutation ((factorProduct q).take (sM (factorProduct q) p).1.val) (exitStrand q p) := by
    unfold glabel; rw [he]
  have e2 : glabel (factorProduct q) p =
      permutation ((factorProduct q).take (p.1.val + 1)) (exitStrand q p) :=
    glabel_eq_exit _ p
  rw [e1, e2]
  have hlt' : p.1.val + 1 ≤ (sM (factorProduct q) p).1.val := hlt
  rw [permutation_take_eq_of_not_occ (factorProduct q) hlt' (sM (factorProduct q) p).1.isLt.le
    (exitStrand q p) (fun k hk h1 h2 => hnone k hk (by omega) h2)]

/-! ### The endpoint matching -/

/-- The merged permutation of the factor permutations at the strand `0`. -/
def segPerm : Perm (Fin r × Fin S) :=
  mergePerm (fun l => permutation (q l)) ⟨0, by omega⟩

/-- A corner is a wrap corner when it is the last corner of a rank in its factor. -/
def IsWrapCorner (p : Fin (factorProduct q).length × Fin 3) : Prop :=
  ∃ l x, p = lastCorner q hq hS l x

/-- **Components of the scissor endpoint.** Let `μ` send the last corner of every rank `x ≥ 1` of
every factor to the first corner of that rank in the same factor, and agree with the matching of
the product elsewhere. Then two corners lie in one orbit of `μ` exactly when their strand labels
lie in one orbit of `segPerm q`. -/
theorem sameCycle_iff_strandLabel (μ : Perm (Fin (factorProduct q).length × Fin 3))
    (hμZ : ∀ l x, x.val ≠ 0 → μ (lastCorner q hq hS l x) = firstCorner q hq hS l x)
    (hμ : ∀ p, (∀ l x, x.val ≠ 0 → p ≠ lastCorner q hq hS l x) → μ p = sM (factorProduct q) p)
    (a b : Fin (factorProduct q).length × Fin 3) :
    μ.SameCycle a b ↔ (segPerm q hS).SameCycle (strandLabel q a) (strandLabel q b) := by
  apply sameCycle_iff_of_wrapLabels μ (segPerm q hS) (strandLabel q) (IsWrapCorner q hq hS)
    (fun p => (finProdFinEquiv p).val)
  · intro p hp
    have hnz : ∀ l x, x.val ≠ 0 → p ≠ lastCorner q hq hS l x :=
      fun l x _ he => hp ⟨l, x, he⟩
    rw [hμ p hnz]
    by_cases h0 : p.2 = 0
    · obtain ⟨h, c⟩ := p
      simp only at h0
      subst h0
      rw [sM_middle, strandLabel_two]
      refine ⟨rfl, ?_⟩
      rw [fpe_val, fpe_val]; simp
    · refine ⟨strandLabel_sM_of_ne q hq hS h0 (fun he => hp ⟨_, _, he⟩), ?_⟩
      obtain ⟨hlt, -, -⟩ := sM_of_ne_lastCorner q hq hS h0 (fun he => hp ⟨_, _, he⟩)
      rw [fpe_val, fpe_val]
      have : p.1.val < (sM (factorProduct q) p).1.val := hlt
      have := p.2.isLt
      omega
  · rintro p ⟨l, x, rfl⟩
    rw [strandLabel_lastCorner q hq hS, segPerm, mergePerm_apply_apply]
    by_cases hx : x.val = 0
    · have hx0 : x = ⟨0, by omega⟩ := Fin.ext hx
      rw [if_pos hx0]
      rw [hμ _ (fun l' x' hx' he => hx' (by
        have := (lastCorner_injective q hq hS he).2; rw [← this]; exact hx)),
        sM_lastCorner, strandLabel_firstCorner, hx0]
    · rw [if_neg (fun e => hx (by rw [e])), hμZ l x hx, strandLabel_firstCorner]
  · rintro a b ⟨l, x, rfl⟩ ⟨l', x', rfl⟩ hab
    rw [strandLabel_lastCorner q hq hS, strandLabel_lastCorner q hq hS] at hab
    obtain ⟨rfl, h2⟩ := Prod.mk.inj hab
    rw [(permutation (q l)).injective h2]

include hq hS in
theorem strandLabel_surjective : Function.Surjective (strandLabel q) := by
  rintro ⟨l, x⟩
  exact ⟨firstCorner q hq hS l x, strandLabel_firstCorner q hq hS l x⟩

end OnLeConjecture.KnotTheory.SignedGrid
