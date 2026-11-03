/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionNativeAssembly
public import OnLeConjecture.Analytic.ExteriorEventFactorization
public import OnLeConjecture.KnotTheory.ExteriorHurwitzWords
public import OnLeConjecture.KnotFloer.GridExteriorReduction
public import OnLeConjecture.KnotFloer.GridMovesToCanonicalMap
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-!
# Statement E from its three remaining inputs

This file proves the reduction of Statement E (`ExteriorNativeMapStatement`) to three statements:

* `EventFactorizationStatement`, the analytic event factorization of Section 3 of the written
  proof (`statement_E_complete_proof.tex`);
* `SignedWordGridRelationsStatement`, the grid realization of signed braid-word relations
  (Section 7);
* `GridFull.ScissorCleanupStatement`, the scissors, cleanup and contractions (Sections 4 to 6 and
  8 to 11).

The proof (`exteriorNativeMapStatement_of_reductions`) is the outline of Section 12. The event
factorization is normalized by Hurwitz moves (`exists_hurwitz_normalized`): strand `0` lies in the
nontrivial cycle of every factor, the singular factors come first, and every factor is padded by
`ρ ρ⁻¹`. The conjugacy derivation from `d_S w` to the padded product is realized by grid moves, and
the scissor statement gives the map to the iterated seam. The second shift `(s - U)/2` equals
`μ(V)/2` (`scissorShiftCount_eq_sourceMilnorNumber`): the exponent sums of the two sides of the
derivation agree, and the lengths of the image word and the local words are fixed by the delta
invariants, the genus balance and the source genus.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open TauCeti CategoryTheory HomologicalComplex
open OnLeConjecture.KnotFloer OnLeConjecture.KnotFloer.GridFull OnLeConjecture.KnotTheory
open OnLeConjecture.PlaneCurve

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-! ### Words -/

theorem letterSum_fullTwist_append (S : ℕ) (w : PositiveAdjacentWord S) :
    SignedAdjacentWord.letterSum (fullTwistWord S ++ w).toSigned =
      ((S * (S - 1) : ℕ) : ℤ) + w.length := by
  rw [letterSum_toSigned, List.length_append, fullTwistWord, torusWord_length, Nat.cast_add,
    mul_comm S]

theorem mem_fullTwistWord {S : ℕ} (hS : 0 < S) (i : Fin (S - 1)) : i ∈ fullTwistWord S := by
  rw [fullTwistWord, torusWord, List.mem_flatten]
  exact ⟨coxeterWord S, List.mem_replicate.mpr ⟨by omega, rfl⟩, List.mem_finRange i⟩

theorem generatorIndices_fullTwist_append {S : ℕ} (hS : 0 < S) (w : PositiveAdjacentWord S) :
    (fullTwistWord S ++ w).toSigned.generatorIndices = Finset.univ := by
  ext i
  simp only [SignedAdjacentWord.generatorIndices, PositiveAdjacentWord.toSigned, List.map_map,
    Function.comp_def, List.map_id', List.mem_toFinset, Finset.mem_univ, iff_true]
  exact List.mem_append_left _ (mem_fullTwistWord hS i)

theorem mem_padWord {S : ℕ} (i : Fin (S - 1)) : (i, (1 : ℤˣ)) ∈ padWord S := by
  rw [padWord]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

theorem generatorIndices_product {S N B : ℕ} (hN : 0 < N) (F : NormalizedFactorization S N B) :
    F.product.generatorIndices = Finset.univ := by
  ext i
  simp only [SignedAdjacentWord.generatorIndices, List.mem_toFinset, Finset.mem_univ, iff_true,
    List.mem_map]
  refine ⟨(i, 1), ?_, rfl⟩
  rw [NormalizedFactorization.product, List.mem_flatten]
  refine ⟨F.factor ⟨0, by omega⟩, List.mem_ofFn.mpr ⟨_, rfl⟩, ?_⟩
  rw [NormalizedFactorization.factor, conjugateWord]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_padWord i)))

theorem two_le_product_length {S N B : ℕ} (hS : 2 ≤ S) (hN : 0 < N)
    (F : NormalizedFactorization S N B) : 2 ≤ F.product.length * 3 := by
  have h := generatorIndices_product hN F
  have hmem : (⟨0, by omega⟩ : Fin (S - 1)) ∈ F.product.generatorIndices := by
    rw [h]
    exact Finset.mem_univ _
  have hpos : 0 < F.product.length := by
    rcases hp : F.product with _ | ⟨a, l⟩
    · rw [hp] at hmem
      simp [SignedAdjacentWord.generatorIndices] at hmem
    · simp
  omega

theorem letterSum_product {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S) :
    SignedAdjacentWord.letterSum F.product = (∑ j, ((F.word j).length : ℤ)) + B := by
  rw [NormalizedFactorization.product, letterSum_flatten, List.map_ofFn, List.sum_ofFn,
    Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, NormalizedFactorization.factor, letterSum_conjugateWord,
      NormalizedFactorization.core, Fin.val_castAdd, j.isLt, dif_pos, letterSum_liftPositiveWord]
  · have : ∀ k : Fin B, SignedAdjacentWord.letterSum
        (F.factor (Fin.natAdd N k)) = 1 := by
      intro k
      rw [NormalizedFactorization.factor, letterSum_conjugateWord, NormalizedFactorization.core,
        dif_neg (by simp), NormalizedFactorization.firstLetter, dif_pos hS]
      simp
    simp only [Function.comp_apply, this, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]

/-! ### The count `s - U = μ(V)` -/

theorem sum_deltaInvariant_point (L : ResolutionSectionLevel A) :
    ∑ j, (deltaInvariant (localSectionEquation A.H (L.point j)) : ℤ) = A.singularDelta := by
  have h := L.delta_sum
  have h2 : ∑ j, deltaInvariant (localSectionEquation A.H (L.point j)) =
      ∑ x ∈ L.points, deltaInvariant (localSectionEquation A.H x) := by
    rw [← Finset.sum_coe_sort L.points]
    exact Equiv.sum_comp L.points.equivFin.symm
      (fun x : L.points => deltaInvariant (localSectionEquation A.H x))
  exact_mod_cast h2.trans h

/-- The second shift of the scissor construction is the Milnor number of the source equation,
given the equality of exponent sums of the two sides of the derivation. -/
theorem scissorShiftCount_eq_sourceMilnorNumber {A : ResolutionSectionAssembly g hd hi}
    {L : ResolutionSectionLevel A} (C : NativeRouteChoice A L) {B : ℕ}
    (F : NormalizedFactorization A.squareSum L.points.card B)
    (hstrands : F.strands = C.strands) (hword : ∀ j, (F.word j).length = (C.factorWord j).length)
    (hsum : ((A.squareSum * (A.squareSum - 1) : ℕ) : ℤ) + C.imageWord.length =
      (∑ j, ((F.word j).length : ℤ)) + B) :
    F.scissorShiftCount = A.sourceMilnorNumber := by
  obtain ⟨γ, hγ₁, hγ₂⟩ := A.exists_sourceGenus
  have hb := A.irreducibleBranchCount_imageEquation
  have himg := C.imageWord_length
  have himage := A.image_delta
  have hδ := sum_deltaInvariant_point L
  set t := A.squareSum * (A.squareSum - 1) with ht
  have hloc : ∀ j, ((F.word j).length : ℤ) + 1 =
      2 * deltaInvariant (localSectionEquation A.H (L.point j)) + C.strands j := by
    intro j
    rw [hword]
    exact_mod_cast C.factorWord_length j
  have hsumloc : (∑ j, ((F.word j).length : ℤ)) + L.points.card =
      2 * A.singularDelta + ∑ j, (C.strands j : ℤ) := by
    have := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hloc j
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hδ] at this
    simpa using this
  simp only [NormalizedFactorization.scissorShiftCount, hstrands]
  have himgZ : (C.imageWord.length : ℤ) + t + irreducibleBranchCount A.imageEquation =
      2 * deltaInvariant A.imageEquation + A.squareSum := by exact_mod_cast himg
  have hγZ₁ : (2 * γ + irreducibleBranchCount A.sourceEquation : ℤ) =
      A.sourceMilnorNumber + 1 := by exact_mod_cast hγ₁
  have hγZ₂ : (γ + irreducibleBranchCount A.sourceEquation : ℤ) =
      deltaInvariant A.sourceEquation + 1 := by exact_mod_cast hγ₂
  have himageZ : (deltaInvariant A.imageEquation : ℤ) =
      deltaInvariant A.sourceEquation + A.singularDelta := by exact_mod_cast himage
  have hbZ : (irreducibleBranchCount A.imageEquation : ℤ) =
      irreducibleBranchCount A.sourceEquation := by exact_mod_cast hb
  linarith

/-! ### The reduction -/

/-- **Statement E from its three remaining inputs.** The analytic event factorization, the grid
realization of signed word relations, and the scissor and cleanup statement imply the exterior
native map statement. -/
theorem exteriorNativeMapStatement_of_reductions (h3 : EventFactorizationStatement)
    (h7 : SignedWordGridRelationsStatement) (h9 : ScissorCleanupStatement) :
    ExteriorNativeMapStatement := by
  classical
  intro g hd hi
  obtain ⟨A, L, C, ⟨E⟩⟩ := h3 g hd hi
  have hS : 2 ≤ A.squareSum := A.two_le_squareSum
  have hN : 0 < L.points.card := L.card_points_pos
  -- the cores by label
  let η : Option (Fin L.points.card) → SignedAdjacentWord A.squareSum := fun o =>
    match o with
    | some j => liftPositiveWord (E.strands_le j) (C.factorWord j)
    | none => NormalizedFactorization.firstLetter A.squareSum
  have hη : ∀ o, (η o).permutation.IsCycle := by
    intro o
    rcases o with _ | j
    · exact isCycle_permutation_firstLetter hS
    · exact isCycle_permutation_liftPositiveWord _ (C.two_le_strands j) _
        (C.factorWord_cycleCount j)
  have hcoreWord : ∀ l, E.coreWord l = η (E.core l) := by
    intro l
    simp only [EventFactorization.coreWord, η]
    rcases E.core l with _ | j
    · simp [firstGeneratorWord, NormalizedFactorization.firstLetter, dif_pos hS]
    · rfl
  have hEfactor : ∀ l, E.factor l = conjugateWord (E.conjugator l) (η (E.core l)) := by
    intro l
    rw [EventFactorization.factor, hcoreWord]
  have htrans := E.transitive
  simp only [hEfactor] at htrans
  obtain ⟨γ', hequiv, hzero, htrans'⟩ :=
    exists_hurwitz_normalized hS E.core E.core_unique η hη E.conjugator htrans
  -- the normalized factorization
  let F : NormalizedFactorization A.squareSum L.points.card E.simpleCount :=
    { strands := C.strands
      word := C.factorWord
      two_le_strands := C.two_le_strands
      strands_le := E.strands_le
      word_cycleCount := C.factorWord_cycleCount
      word_generators := C.factorWord_generators
      conjugator := γ' }
  have hFfactor : ∀ l, F.factor l =
      conjugateWord (padWord A.squareSum ++ γ' l) (η (standardLabel _ _ l)) := by
    intro l
    simp only [NormalizedFactorization.factor, NormalizedFactorization.core, standardLabel, η, F]
    split_ifs <;> rfl
  have hFprod : F.product = (List.ofFn fun l =>
      conjugateWord (padWord A.squareSum ++ γ' l) (η (standardLabel _ _ l))).flatten := by
    rw [NormalizedFactorization.product]
    congr 1
    exact List.ofFn_inj.mpr (funext hFfactor)
  have hEprod : E.product = (List.ofFn fun l =>
      conjugateWord (E.conjugator l) (η (E.core l))).flatten := by
    rw [EventFactorization.product]
    congr 1
    exact List.ofFn_inj.mpr (funext hEfactor)
  have hconj : SignedBraidConj (fullTwistWord A.squareSum ++ C.imageWord).toSigned F.product := by
    have h1 := E.derivation
    rw [hEprod] at h1
    rw [hFprod]
    exact Relation.EqvGen.trans _ _ _ h1 hequiv.toConj
  have hzeroF : F.StrandZeroInEveryFactor (by omega) := by
    intro l
    rw [hFfactor]
    exact hzero l
  have htransF : F.Transitive := by
    intro x y
    simp only [hFfactor]
    exact htrans' x y
  -- the grid moves and the scissor map
  obtain ⟨H, hH, hmoves⟩ := h7 hS _ _ (generatorIndices_fullTwist_append (by omega) _)
    (generatorIndices_product hN F) hconj
  obtain ⟨sizes, D, hprep, hD, hDmoves, hmap⟩ := h9 _ _ _ hS hN F hzeroF htransF
  obtain ⟨ψ, hψs, hψc⟩ := hmap H (two_le_product_length hS hN F) hH
  have hsrc : 2 ≤ (fullTwistWord A.squareSum ++ C.imageWord).length * 3 :=
    two_le_wordGrid_size_fullTwist (by have := A.four_le_squareSum; omega) C.imageWord
  obtain ⟨_, φ, hφs, hφc⟩ := exists_movesTo_canonical_map_of_two_le _ H hsrc hmoves
  -- the shift count
  have hsum : ((A.squareSum * (A.squareSum - 1) : ℕ) : ℤ) + C.imageWord.length =
      (∑ j, ((F.word j).length : ℤ)) + E.simpleCount := by
    have h := hconj.letterSum_eq
    rw [letterSum_fullTwist_append, letterSum_product F hS] at h
    exact h
  have hcount := scissorShiftCount_eq_sourceMilnorNumber C F rfl (fun _ => rfl) hsum
  refine ⟨A, L, C, sizes, D, hprep, hD, hDmoves, φ ≫ ψ, ?_, ?_⟩
  · have h := hφs.comp hψs
    have hreal : ((F.scissorShiftCount : ℤ) : ℝ) / 2 = (A.sourceMilnorNumber : ℝ) / 2 := by
      rw [hcount]
      push_cast
      ring
    rw [add_zero, zero_add, hreal] at h
    exact h
  · rw [homologyMap_comp, CategoryTheory.comp_apply, hφc, hψc]

end OnLeConjecture.Analytic
