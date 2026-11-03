/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWordDeformation

/-! # Embedded tangles throughout word straightening

Unit slabs separate different connector and letter interiors. Boundary equality
forces the source parameter to be their common endpoint. Combining those facts
with the local injection proofs controls the whole finite word.
-/

@[expose] public noncomputable section

open Set
open scoped Topology

namespace OnLeConjecture.KnotTheory

/-- Connectors, including the last one, and letters in their geometric order. -/
abbrev PositiveRectilinearWordPieceIndex {m : ℕ} (w : PositiveAdjacentWord m) :=
  Fin (w.length + 1) ⊕ Fin w.length

/-- The integer starting coordinate of a connector or letter. -/
def positiveRectilinearWordPieceAddress {m : ℕ} (w : PositiveAdjacentWord m) :
    PositiveRectilinearWordPieceIndex w → ℕ
  | Sum.inl j => 2 * j.val
  | Sum.inr j => 2 * j.val + 1

theorem positiveRectilinearWordPieceAddress_injective {m : ℕ} (w : PositiveAdjacentWord m) :
    Function.Injective (positiveRectilinearWordPieceAddress w) := by
  intro p q hpq
  rcases p with p | p <;> rcases q with q | q
  · have he : p.val = q.val := by change 2 * p.val = 2 * q.val at hpq; omega
    exact congrArg Sum.inl (Fin.ext he)
  · change 2 * p.val = 2 * q.val + 1 at hpq
    omega
  · change 2 * p.val + 1 = 2 * q.val at hpq
    omega
  · have he : p.val = q.val := by change 2 * p.val + 1 = 2 * q.val + 1 at hpq; omega
    exact congrArg Sum.inr (Fin.ext he)

/-- Every source parameter lies in at least one of the finitely many unit slabs. -/
theorem exists_positiveRectilinearWordPiece {m : ℕ} (w : PositiveAdjacentWord m)
    {t : ℝ} (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    ∃ e : PositiveRectilinearWordPieceIndex w,
      t ∈ Icc (positiveRectilinearWordPieceAddress w e : ℝ)
        ((positiveRectilinearWordPieceAddress w e : ℝ) + 1) := by
  have hz : ∃ z : ℕ, z ≤ 2 * w.length ∧ t ∈ Icc (z : ℝ) ((z : ℝ) + 1) := by
    by_cases h : t ≤ (2 * w.length : ℕ)
    · exact ⟨⌊t⌋₊, Nat.floor_le_of_le h, Nat.floor_le ht.1, (Nat.lt_floor_add_one t).le⟩
    · refine ⟨2 * w.length, le_rfl, ?_, ?_⟩
      · exact (lt_of_not_ge h).le
      · simpa only [Nat.cast_mul, Nat.cast_ofNat] using ht.2
  obtain ⟨z, hz, ht⟩ := hz
  rcases Nat.mod_two_eq_zero_or_one z with he | he
  · have he' : z = 2 * (z / 2) := by omega
    let j : Fin (w.length + 1) := ⟨z / 2, by omega⟩
    refine ⟨Sum.inl j, ?_⟩
    change t ∈ Icc ((2 * (z / 2) : ℕ) : ℝ) (((2 * (z / 2) : ℕ) : ℝ) + 1)
    rw [← he']
    exact ht
  · have he' : z = 2 * (z / 2) + 1 := by omega
    let j : Fin w.length := ⟨z / 2, by omega⟩
    refine ⟨Sum.inr j, ?_⟩
    change t ∈ Icc ((2 * (z / 2) + 1 : ℕ) : ℝ)
      (((2 * (z / 2) + 1 : ℕ) : ℝ) + 1)
    rw [← he']
    exact ht

/-- Local piece evaluation in the literal translated coordinates. -/
def positiveRectilinearWordPiece {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (e : PositiveRectilinearWordPieceIndex w) (k : Fin m) (u : ℝ) : ℝ × ℂ :=
  match e with
  | Sum.inl j => positiveRectilinearWordGapDepth w j k d u
  | Sum.inr j => L j k u

/-- Every slab uses precisely its specified local piece, including the last connector. -/
theorem positiveRectilinearWordJoined_piece {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (hL₀ : ∀ j k, L j k 0 = positiveRectilinearWordGapDepth w j.castSucc k d 1)
    (hL₁ : ∀ j k, L j k 1 = positiveRectilinearWordGapDepth w j.succ k d 0)
    (e : PositiveRectilinearWordPieceIndex w) (k : Fin m) {t : ℝ}
    (ht : t ∈ Icc (positiveRectilinearWordPieceAddress w e : ℝ)
      ((positiveRectilinearWordPieceAddress w e : ℝ) + 1)) :
    positiveRectilinearWordJoined w L d k t =
      positiveRectilinearWordPiece w L d e k (t - positiveRectilinearWordPieceAddress w e) := by
  rcases e with j | j
  · induction j using Fin.lastCases with
    | last =>
      have ht' : t ∈ Icc (2 * (w.length : ℝ)) (2 * (w.length : ℝ) + 1) := by
        simpa only [positiveRectilinearWordPieceAddress, Fin.val_last, Nat.cast_mul,
          Nat.cast_ofNat] using ht
      rw [positiveRectilinearWordJoined_last_gap w L d hL₁ k ht'.1,
        positiveWordClip_of_mem ⟨by linarith [ht'.1], by linarith [ht'.2]⟩]
      simp only [positiveRectilinearWordPiece, positiveRectilinearWordPieceAddress,
        Fin.val_last, Nat.cast_mul, Nat.cast_ofNat]
    | cast j =>
      have ht' : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1) := by
        simpa only [positiveRectilinearWordPieceAddress, Fin.val_castSucc,
          Nat.cast_mul, Nat.cast_ofNat] using ht
      simpa only [positiveRectilinearWordPiece, positiveRectilinearWordPieceAddress,
        Fin.val_castSucc, Nat.cast_mul, Nat.cast_ofNat] using
        positiveRectilinearWordJoined_gap w L d hL₀ hL₁ j k ht'
  · have ht' : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) := by
      simpa only [positiveRectilinearWordPieceAddress, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one, add_assoc, one_add_one_eq_two] using ht
    simpa only [positiveRectilinearWordPiece, positiveRectilinearWordPieceAddress,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      positiveRectilinearWordJoined_letter w L d hL₀ hL₁ j k ht'

private theorem convex_unit_slab {s t x : ℝ} (hs : s ∈ Icc 0 1)
    (ht : t ∈ Icc 0 1) (hx : x ∈ Icc 0 1) (hx₀ : x = 0 ↔ t = 0)
    (hx₁ : x = 1 ↔ t = 1) :
    (1 - s) * t + s * x ∈ Icc 0 1 ∧
      ((1 - s) * t + s * x = 0 ↔ t = 0) ∧
      ((1 - s) * t + s * x = 1 ↔ t = 1) := by
  have hst : 0 ≤ (1 - s) * t := mul_nonneg (by linarith [hs.2]) ht.1
  have hsx : 0 ≤ s * x := mul_nonneg hs.1 hx.1
  have hsT : 0 ≤ (1 - s) * (1 - t) := mul_nonneg (by linarith [hs.2]) (by linarith [ht.2])
  have hsX : 0 ≤ s * (1 - x) := mul_nonneg hs.1 (by linarith [hx.2])
  refine ⟨⟨by linarith, by nlinarith⟩, ?_, ?_⟩
  · constructor
    · intro h
      by_cases he : s = 1
      · simp only [he, sub_self, zero_mul, one_mul, zero_add] at h
        exact hx₀.mp h
      · have hp : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 he)
        have hz : (1 - s) * t = 0 := by linarith
        exact (mul_eq_zero.mp hz).resolve_left hp.ne'
    · intro h
      rw [h, hx₀.mpr h]
      ring
  · constructor
    · intro h
      by_cases he : s = 1
      · simp only [he, sub_self, zero_mul, one_mul, zero_add] at h
        exact hx₁.mp h
      · have hp : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 he)
        have hz : (1 - s) * (1 - t) = 0 := by nlinarith
        have ht' := (mul_eq_zero.mp hz).resolve_left hp.ne'
        linarith
    · intro h
      rw [h, hx₁.mpr h]
      ring

/-- The straightening piece stays in its closed unit slab and touches its boundary planes
only at the corresponding parameter endpoints. -/
theorem positiveRectilinearWordStraightenLetter_slab {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) (k : Fin m)
    {s u : ℝ} (hs : s ∈ Icc 0 1) (hu : u ∈ Icc 0 1) :
    (positiveRectilinearWordStraightenLetter w j k s u).1 ∈
        Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) ∧
      ((positiveRectilinearWordStraightenLetter w j k s u).1 = 2 * (j.val : ℝ) + 1 ↔ u = 0) ∧
      ((positiveRectilinearWordStraightenLetter w j k s u).1 = 2 * (j.val : ℝ) + 2 ↔ u = 1) := by
  have hb := positiveRectilinearWord_local_slab w[j.val]
    ((positiveWordPrefix w j.val).symm k) hu
  have hc := convex_unit_slab hs hu hb.1 hb.2.1 hb.2.2
  dsimp only [positiveGridRectilinear] at hc
  dsimp only [positiveRectilinearWordStraightenLetter, positiveGridRectilinearDeformation]
  constructor
  · constructor <;> linarith [hc.1.1, hc.1.2]
  · constructor
    · convert hc.2.1 using 1
      constructor <;> intro h <;> linarith
    · convert hc.2.2 using 1
      constructor <;> intro h <;> linarith

private theorem joined_injective_of_piece_slabs {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (hL₀ : ∀ j k, L j k 0 = positiveRectilinearWordGapDepth w j.castSucc k d 1)
    (hL₁ : ∀ j k, L j k 1 = positiveRectilinearWordGapDepth w j.succ k d 0)
    (hI : ∀ e, Function.Injective (fun p : Fin m × ℝ =>
      positiveRectilinearWordPiece w L d e p.1 p.2))
    (hB : ∀ e k u, u ∈ Icc 0 1 →
      (positiveRectilinearWordPiece w L d e k u).1 ∈
          Icc (positiveRectilinearWordPieceAddress w e : ℝ)
            ((positiveRectilinearWordPieceAddress w e : ℝ) + 1) ∧
        ((positiveRectilinearWordPiece w L d e k u).1 =
          (positiveRectilinearWordPieceAddress w e : ℝ) ↔ u = 0) ∧
        ((positiveRectilinearWordPiece w L d e k u).1 =
          (positiveRectilinearWordPieceAddress w e : ℝ) + 1 ↔ u = 1)) :
    Function.Injective (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRectilinearWordJoined w L d p.1 p.2.val) := by
  rintro ⟨k, ⟨t, ht⟩⟩ ⟨l, ⟨u, hu⟩⟩ he
  change positiveRectilinearWordJoined w L d k t = positiveRectilinearWordJoined w L d l u at he
  have hglobal := he
  obtain ⟨e, het⟩ := exists_positiveRectilinearWordPiece w ht
  obtain ⟨f, hfu⟩ := exists_positiveRectilinearWordPiece w hu
  have htu : t - (positiveRectilinearWordPieceAddress w e : ℝ) ∈ Icc 0 1 :=
    ⟨by linarith [het.1], by linarith [het.2]⟩
  have huu : u - (positiveRectilinearWordPieceAddress w f : ℝ) ∈ Icc 0 1 :=
    ⟨by linarith [hfu.1], by linarith [hfu.2]⟩
  rw [positiveRectilinearWordJoined_piece w L d hL₀ hL₁ e k het,
    positiveRectilinearWordJoined_piece w L d hL₀ hL₁ f l hfu] at he
  have hbe := hB e k _ htu
  have hbf := hB f l _ huu
  have hx := congrArg Prod.fst he
  have htime : t = u := by
    rcases lt_trichotomy (positiveRectilinearWordPieceAddress w e)
        (positiveRectilinearWordPieceAddress w f) with h | h | h
    · have hgap : (positiveRectilinearWordPieceAddress w e : ℝ) + 1 ≤
          (positiveRectilinearWordPieceAddress w f : ℝ) := by exact_mod_cast h
      have htend := hbe.2.2.mp (by linarith [hbe.1.2, hbf.1.1])
      have hustart := hbf.2.1.mp (by linarith [hbe.1.2, hbf.1.1])
      linarith [hbe.1.2, hbf.1.1]
    · have hef := positiveRectilinearWordPieceAddress_injective w h
      subst f
      have hp := hI e
        (a₁ := (k, t - (positiveRectilinearWordPieceAddress w e : ℝ)))
        (a₂ := (l, u - (positiveRectilinearWordPieceAddress w e : ℝ))) he
      have hp' := congrArg Prod.snd hp
      dsimp only at hp'
      linarith
    · have hgap : (positiveRectilinearWordPieceAddress w f : ℝ) + 1 ≤
          (positiveRectilinearWordPieceAddress w e : ℝ) := by exact_mod_cast h
      have hustart := hbe.2.1.mp (by linarith [hbf.1.2, hbe.1.1])
      have htend := hbf.2.2.mp (by linarith [hbf.1.2, hbe.1.1])
      linarith [hbf.1.2, hbe.1.1]
  subst u
  rw [positiveRectilinearWordJoined_piece w L d hL₀ hL₁ e k het,
    positiveRectilinearWordJoined_piece w L d hL₀ hL₁ e l het] at hglobal
  have hk : k = l := congrArg Prod.fst (hI e
    (a₁ := (k, t - (positiveRectilinearWordPieceAddress w e : ℝ)))
    (a₂ := (l, t - (positiveRectilinearWordPieceAddress w e : ℝ))) hglobal)
  subst l
  rfl

private theorem gapDepth_injective {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin (w.length + 1)) (d : ℝ) :
    Function.Injective (fun p : Fin m × ℝ => positiveRectilinearWordGapDepth w j p.1 d p.2) := by
  rintro ⟨k, t⟩ ⟨l, u⟩ he
  have hx := congrArg Prod.fst he
  have hr := congrArg (fun p : ℝ × ℂ => p.2.re) he
  simp only [positiveRectilinearWordGapDepth, Complex.add_re, Complex.natCast_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero] at hx hr
  have ht : t = u := by linarith
  have hk : k = l := (positiveWordPrefix w j.val).symm.injective
    (Fin.ext (Nat.cast_injective hr))
  simp [hk, ht]

private theorem translated_relabel_injective {m : ℕ}
    (P : Fin m → ℝ → ℝ × ℂ)
    (hP : Function.Injective (fun p : Fin m × ℝ => P p.1 p.2))
    (e : Equiv.Perm (Fin m)) (c : ℝ) :
    Function.Injective (fun p : Fin m × ℝ => (c + (P (e.symm p.1) p.2).1,
      (P (e.symm p.1) p.2).2)) := by
  rintro ⟨k, t⟩ ⟨l, u⟩ he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  have hpp : P (e.symm k) t = P (e.symm l) u := Prod.ext (add_left_cancel hx) hy
  have hp := hP (a₁ := (e.symm k, t)) (a₂ := (e.symm l, u)) hpp
  have hk := e.symm.injective (congrArg Prod.fst hp)
  have ht := congrArg Prod.snd hp
  exact Prod.ext hk ht

/-- The first-stage local pieces are injective in label and local parameter. -/
theorem positiveRectilinearWordLift_piece_injective {m : ℕ}
    (w : PositiveAdjacentWord m) {s : ℝ} (hs : s ∈ Icc 0 1)
    (e : PositiveRectilinearWordPieceIndex w) :
    Function.Injective (fun p : Fin m × ℝ => positiveRectilinearWordPiece w
      (fun j k u => positiveRectilinearWordLiftLetter w j k s u) s e p.1 p.2) := by
  rcases e with j | j
  · exact gapDepth_injective w j s
  · exact translated_relabel_injective (fun k u => positiveGridDepthLift w[j.val] k s u)
      (positiveGridDepthLift_injective w[j.val] hs)
      (positiveWordPrefix w j.val) _

/-- The straightening-stage local pieces are injective in label and local parameter. -/
theorem positiveRectilinearWordStraighten_piece_injective {m : ℕ}
    (w : PositiveAdjacentWord m) {s : ℝ} (hs : s ∈ Icc 0 1)
    (e : PositiveRectilinearWordPieceIndex w) :
    Function.Injective (fun p : Fin m × ℝ => positiveRectilinearWordPiece w
      (fun j k u => positiveRectilinearWordStraightenLetter w j k s u) 1 e p.1 p.2) := by
  rcases e with j | j
  · exact gapDepth_injective w j 1
  · exact translated_relabel_injective
      (fun k u => positiveGridRectilinearDeformation w[j.val] k s u)
      (positiveGridRectilinearDeformation_injective w[j.val] hs)
      (positiveWordPrefix w j.val) _

private theorem liftPiece_fst {m : ℕ} (w : PositiveAdjacentWord m)
    (e : PositiveRectilinearWordPieceIndex w) (k : Fin m) (s u : ℝ) :
    (positiveRectilinearWordPiece w
      (fun j k u => positiveRectilinearWordLiftLetter w j k s u) s e k u).1 =
        (positiveRectilinearWordPieceAddress w e : ℝ) + u := by
  rcases e with j | j <;>
    simp [positiveRectilinearWordPiece, positiveRectilinearWordPieceAddress,
      positiveRectilinearWordGapDepth, positiveRectilinearWordLiftLetter, positiveGridDepthLift]

/-- The first stage is an embedding of the entire finite tangle, not only of each letter. -/
theorem positiveRectilinearWordLift_injective {m : ℕ}
    (w : PositiveAdjacentWord m) {s : ℝ} (hs : s ∈ Icc 0 1) :
    Function.Injective (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRectilinearWordLift w p.1 s p.2.val) := by
  apply joined_injective_of_piece_slabs w _ s
    (fun j k => (positiveRectilinearWordLiftLetter_endpoints w s j k).1)
    (fun j k => (positiveRectilinearWordLiftLetter_endpoints w s j k).2)
    (positiveRectilinearWordLift_piece_injective w hs)
  intro e k u hu
  rw [liftPiece_fst]
  constructor
  · constructor <;> linarith [hu.1, hu.2]
  · constructor <;> constructor <;> intro h <;> linarith

/-- The second stage remains an embedding through the literal polygonal endpoint. -/
theorem positiveRectilinearWordStraighten_injective {m : ℕ}
    (w : PositiveAdjacentWord m) {s : ℝ} (hs : s ∈ Icc 0 1) :
    Function.Injective (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRectilinearWordStraighten w p.1 s p.2.val) := by
  apply joined_injective_of_piece_slabs w _ 1
    (fun j k => (positiveRectilinearWordStraightenLetter_endpoints w s j k).1)
    (fun j k => (positiveRectilinearWordStraightenLetter_endpoints w s j k).2)
    (positiveRectilinearWordStraighten_piece_injective w hs)
  intro e k u hu
  rcases e with j | j
  · simp only [positiveRectilinearWordPiece, positiveRectilinearWordGapDepth,
      positiveRectilinearWordPieceAddress, Nat.cast_mul, Nat.cast_ofNat]
    constructor
    · constructor <;> linarith [hu.1, hu.2]
    · constructor <;> constructor <;> intro h <;> linarith
  · simpa only [positiveRectilinearWordPiece, positiveRectilinearWordPieceAddress,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      positiveRectilinearWordStraightenLetter_slab w j k hs hu

/-- The first stage is a native topological closed embedding of the compact finite tangle. -/
theorem positiveRectilinearWordLift_isClosedEmbedding {m : ℕ}
    (w : PositiveAdjacentWord m) {s : ℝ} (hs : s ∈ Icc 0 1) :
    Topology.IsClosedEmbedding (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRectilinearWordLift w p.1 s p.2.val) := by
  have hc : Continuous (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRectilinearWordLift w p.1 s p.2.val) := by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    have hcomp := (positiveRectilinearWordLift_continuous w k).comp
      ((continuous_const (y := s)).prodMk (continuous_id : Continuous (fun u : ℝ => u)))
    change Continuous (fun u : ℝ => positiveRectilinearWordLift w k s u) at hcomp
    exact hcomp.comp continuous_subtype_val
  exact hc.isClosedEmbedding (positiveRectilinearWordLift_injective w hs)

/-- The second stage is a closed embedding of that same compact finite tangle at every time. -/
theorem positiveRectilinearWordStraighten_isClosedEmbedding {m : ℕ}
    (w : PositiveAdjacentWord m) {s : ℝ} (hs : s ∈ Icc 0 1) :
    Topology.IsClosedEmbedding (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRectilinearWordStraighten w p.1 s p.2.val) := by
  have hc : Continuous (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRectilinearWordStraighten w p.1 s p.2.val) := by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    have hcomp := (positiveRectilinearWordStraighten_continuous w k).comp
      ((continuous_const (y := s)).prodMk (continuous_id : Continuous (fun u : ℝ => u)))
    change Continuous (fun u : ℝ => positiveRectilinearWordStraighten w k s u) at hcomp
    exact hcomp.comp continuous_subtype_val
  exact hc.isClosedEmbedding (positiveRectilinearWordStraighten_injective w hs)

/-- The marked literal polygonal carrier is the embedded terminal finite tangle. -/
theorem positiveRectilinearWordCarrier_isClosedEmbedding {m : ℕ}
    (w : PositiveAdjacentWord m) :
    Topology.IsClosedEmbedding (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRectilinearWordCarrier w p.1 p.2.val) := by
  simpa only [positiveRectilinearWordStraighten_one] using
    positiveRectilinearWordStraighten_isClosedEmbedding w (s := 1) ⟨zero_le_one, le_rfl⟩

/-- All piece addresses lie before the last source endpoint. -/
theorem positiveRectilinearWordPieceAddress_le {m : ℕ} (w : PositiveAdjacentWord m)
    (e : PositiveRectilinearWordPieceIndex w) :
    positiveRectilinearWordPieceAddress w e ≤ 2 * w.length := by
  rcases e with j | j <;> dsimp only [positiveRectilinearWordPieceAddress]
  all_goals have hj := j.isLt; omega

/-- The first stage leaves the global horizontal coordinate equal to the source parameter. -/
theorem positiveRectilinearWordLift_fst {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    (positiveRectilinearWordLift w k s t).1 = t := by
  obtain ⟨e, he⟩ := exists_positiveRectilinearWordPiece w ht
  have hp := positiveRectilinearWordJoined_piece w _ s
    (fun j k => (positiveRectilinearWordLiftLetter_endpoints w s j k).1)
    (fun j k => (positiveRectilinearWordLiftLetter_endpoints w s j k).2) e k he
  change positiveRectilinearWordLift w k s t = _ at hp
  rw [hp, liftPiece_fst]
  ring

/-- Uniform closed-slab and boundary properties for every straightening piece. -/
theorem positiveRectilinearWordStraighten_piece_slab {m : ℕ} (w : PositiveAdjacentWord m)
    {s : ℝ} (hs : s ∈ Icc 0 1) (e : PositiveRectilinearWordPieceIndex w)
    (k : Fin m) {u : ℝ} (hu : u ∈ Icc 0 1) :
    (positiveRectilinearWordPiece w
      (fun j k u => positiveRectilinearWordStraightenLetter w j k s u) 1 e k u).1 ∈
        Icc (positiveRectilinearWordPieceAddress w e : ℝ)
          ((positiveRectilinearWordPieceAddress w e : ℝ) + 1) ∧
      ((positiveRectilinearWordPiece w
        (fun j k u => positiveRectilinearWordStraightenLetter w j k s u) 1 e k u).1 =
          (positiveRectilinearWordPieceAddress w e : ℝ) ↔ u = 0) ∧
      ((positiveRectilinearWordPiece w
        (fun j k u => positiveRectilinearWordStraightenLetter w j k s u) 1 e k u).1 =
          (positiveRectilinearWordPieceAddress w e : ℝ) + 1 ↔ u = 1) := by
  rcases e with j | j
  · simp only [positiveRectilinearWordPiece, positiveRectilinearWordGapDepth,
      positiveRectilinearWordPieceAddress, Nat.cast_mul, Nat.cast_ofNat]
    constructor
    · constructor <;> linarith [hu.1, hu.2]
    · constructor <;> constructor <;> intro h <;> linarith
  · simpa only [positiveRectilinearWordPiece, positiveRectilinearWordPieceAddress,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      positiveRectilinearWordStraightenLetter_slab w j k hs hu

/-- Straightening stays in the full word slab and reaches its boundary planes only at the
corresponding source endpoints. This excludes additional collisions after cylinder closure. -/
theorem positiveRectilinearWordStraighten_fst_slab {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) {s t : ℝ} (hs : s ∈ Icc 0 1)
    (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    (positiveRectilinearWordStraighten w k s t).1 ∈ Icc 0 (2 * (w.length : ℝ) + 1) ∧
      ((positiveRectilinearWordStraighten w k s t).1 = 0 ↔ t = 0) ∧
      ((positiveRectilinearWordStraighten w k s t).1 = 2 * (w.length : ℝ) + 1 ↔
        t = 2 * (w.length : ℝ) + 1) := by
  obtain ⟨e, he⟩ := exists_positiveRectilinearWordPiece w ht
  have hp := positiveRectilinearWordJoined_piece w _ 1
    (fun j k => (positiveRectilinearWordStraightenLetter_endpoints w s j k).1)
    (fun j k => (positiveRectilinearWordStraightenLetter_endpoints w s j k).2) e k he
  change positiveRectilinearWordStraighten w k s t = _ at hp
  rw [hp]
  have hu : t - (positiveRectilinearWordPieceAddress w e : ℝ) ∈ Icc 0 1 :=
    ⟨by linarith [he.1], by linarith [he.2]⟩
  have hb := positiveRectilinearWordStraighten_piece_slab w hs e k hu
  have hlo := Nat.cast_nonneg (α := ℝ) (positiveRectilinearWordPieceAddress w e)
  have hhi : (positiveRectilinearWordPieceAddress w e : ℝ) ≤ 2 * (w.length : ℝ) := by
    exact_mod_cast positiveRectilinearWordPieceAddress_le w e
  constructor
  · constructor <;> linarith [hb.1.1, hb.1.2]
  · constructor
    · constructor
      · intro h
        have hu0 := hb.2.1.mp (by linarith [hb.1.1])
        linarith [hb.1.1]
      · intro h
        have hx0 := hb.2.1.mpr (by linarith [he.1])
        linarith [he.1]
    · constructor
      · intro h
        have hu1 := hb.2.2.mp (by linarith [hb.1.2])
        linarith [hb.1.2]
      · intro h
        have hx1 := hb.2.2.mpr (by linarith [he.2])
        linarith [he.2]

end OnLeConjecture.KnotTheory
