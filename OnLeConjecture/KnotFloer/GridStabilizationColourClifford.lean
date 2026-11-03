/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationColourAlgebra
public import OnLeConjecture.KnotFloer.GridStabilizationOCenter
public import OnLeConjecture.KnotFloer.GridStabilizationXPartner
public import OnLeConjecture.KnotFloer.GridExteriorCommutationColour

/-!
# Three blocks of the transferred colour derivative of a stabilization

Let `A = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization of `G` splitting the `X`
marking of column `s`, with the special contraction `fullStabilizationTransferredRetraction` of
`C(A)` onto `C(G) × C(G)`. For a set `P` of columns of `A`, the colour derivative
`Ψ = oDerivative R A P` is a chain map, and its transfer `T = proj Ψ incl`
(`stabilizationColourTransfer`) is an endomorphism of `C(G) × C(G)` commuting with the diagonal
old differential. This file determines three of the four blocks of `T` up to homotopy:

* `isNullHomotopic_stabilizationColourTransfer_snd_inl`: the block from the first copy to the
  second copy is null-homotopic;
* `isNullHomotopic_stabilizationColourTransfer_diagonal`: the two diagonal blocks agree up to
  homotopy;
* `isNullHomotopic_stabilizationColourTransfer_fst_inr`: if the new `O` column `s.castSucc` and the
  column `s.succ`, which carries the old `O` marking of the split column, both lie in `P` or both
  lie outside `P`, then the block from the second copy to the first copy is null-homotopic.

The proofs use two Clifford relations in `C(A)`. The new-O derivative `L`
(`stabilizationODerivative`) anticommutes with `Ψ` up to homotopy, and so does the derivative `Ξ`
at the new `X` marking in column `s.succ` (`stabilizationXDerivative`) under the stated condition on
`P`, because the curvature of `Ξ Ψ + Ψ Ξ` counts the colour-`P` `O` markings in the column and
row of that `X`. The transfers of `L` and `Ξ` are computed in `GridStabilizationOCenter` and
`GridStabilizationXPartner`, and the block identities of `GridStabilizationColourAlgebra` read off
the three blocks.

This is the stabilization case of Lemma `movesToNativeMap` of the written proof of Statement E
(`statement_E_complete_proof.tex`). There it follows from the multivariable chain equations of
Section 6. Here the contraction of the project is used instead.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The colour derivative of the column set `P` of the stabilized grid, transferred to the two
copies of the old complex. -/
def stabilizationColourTransfer (P : Finset (Fin (n + 1))) :
    Module.End (LaurentPolynomial R) (LaurentChain R n × LaurentChain R n) :=
  contractionTransfer (fullStabilizationTransferredRetraction G s R)
    (oDerivative R (G.stabilizeX s.castSucc (G.X s).castSucc s) P)

omit [CharP R 2] in
/-- The new-O derivative is the single-column derivative at the new column. -/
theorem stabilizationODerivative_eq_oDerivative :
    stabilizationODerivative G s R =
      oDerivative R (G.stabilizeX s.castSucc (G.X s).castSucc s) {s.castSucc} := by
  have h := smul_oDerivative_singleton (R := R) (G.stabilizeX s.castSucc (G.X s).castSucc s)
    s.castSucc
  have hO : (G.stabilizeX s.castSucc (G.X s).castSucc s).O s.castSucc = (G.X s).castSucc := by
    simp only [GridDiagram.stabilizeX_O, GridState.insertPoint_apply_newColumn]
  rw [hO] at h
  unfold stabilizationODerivative
  change (LaurentPolynomial.T (-1) : LaurentPolynomial R) •
    squareCount R (G.stabilizeX s.castSucc (G.X s).castSucc s) (s.castSucc, (G.X s).castSucc) = _
  rw [← h, smul_smul, ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero,
    one_smul]

/-- The column of an `O` marking of the stabilized grid lies in the new row exactly at the new
column. -/
theorem stabilizeX_O_eq_newRow_iff (h : Fin (n + 1)) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).O h = (G.X s).castSucc ↔ h = s.castSucc := by
  rw [GridDiagram.stabilizeX_O]
  exact GridState.insertPoint_apply_eq_iff _ _ _ _

variable (P : Finset (Fin (n + 1)))

set_option quotPrecheck false in
local notation "𝔸" => G.stabilizeX s.castSucc (G.X s).castSucc s

omit [CharP R 2] in
theorem comp_finsetSum_add_finsetSum_comp {M : Type*} [AddCommGroup M]
    [Module (LaurentPolynomial R) M] (f : Module.End (LaurentPolynomial R) M)
    {ι : Type*} (t : Finset ι) (g : ι → Module.End (LaurentPolynomial R) M) :
    f ∘ₗ (∑ i ∈ t, g i) + (∑ i ∈ t, g i) ∘ₗ f = ∑ i ∈ t, (f ∘ₗ g i + g i ∘ₗ f) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    Finset.sum_add_distrib]

/-- The new-O derivative anticommutes with every colour derivative up to homotopy. -/
theorem isNullHomotopic_stabilizationODerivative_anticomm :
    IsNullHomotopic (laurentDifferential 𝔸 R) (laurentDifferential 𝔸 R)
      (stabilizationODerivative G s R ∘ₗ oDerivative R 𝔸 P +
        oDerivative R 𝔸 P ∘ₗ stabilizationODerivative G s R) := by
  rw [stabilizationODerivative_eq_oDerivative, oDerivative_eq_sum (R := R) 𝔸 P,
    comp_finsetSum_add_finsetSum_comp]
  refine IsNullHomotopic.finsetSum P fun h _ => ?_
  by_cases hk : s.castSucc = h
  · subst hk
    apply IsNullHomotopic.of_eq_zero
    rw [oDerivative_singleton_comp_self, add_zero]
  · have hh := oDerivative_anticommutator_homotopy (R := R) 𝔸 hk
    refine ⟨-oSecondDerivative R 𝔸 {s.castSucc, h}, ?_⟩
    rw [LinearMap.comp_neg, LinearMap.neg_comp, ← neg_add]
    exact eq_neg_of_add_eq_zero_left hh

/-- The new-X derivative anticommutes with a colour derivative up to homotopy when the new `O`
column and the column of the split old `O` marking have the same membership in `P`. -/
theorem isNullHomotopic_stabilizationXDerivative_anticomm
    (hP : s.castSucc ∈ P ↔ s.succ ∈ P) :
    IsNullHomotopic (laurentDifferential 𝔸 R) (laurentDifferential 𝔸 R)
      (stabilizationXDerivative G s R ∘ₗ oDerivative R 𝔸 P +
        oDerivative R 𝔸 P ∘ₗ stabilizationXDerivative G s R) := by
  classical
  set Ξ := stabilizationXDerivative G s R with hΞ
  set d := laurentDifferential 𝔸 R with hd
  have hcount (h : Fin (n + 1)) :
      Ξ ∘ₗ squareCount R 𝔸 (h, (𝔸).O h) + squareCount R 𝔸 (h, (𝔸).O h) ∘ₗ Ξ +
        (d ∘ₗ squarePairCount R 𝔸 (s.succ, (G.X s).castSucc) (h, (𝔸).O h) +
          squarePairCount R 𝔸 (s.succ, (G.X s).castSucc) (h, (𝔸).O h) ∘ₗ d) =
        ((if s.succ = h then LaurentPolynomial.T 1 else 0) +
          (if (G.X s).castSucc = (𝔸).O h then LaurentPolynomial.T 1 else 0) :
            LaurentPolynomial R) • LinearMap.id :=
    squareCount_anticomm 𝔸 (s.succ, (G.X s).castSucc) (h, (𝔸).O h)
  set W := ∑ h ∈ P, squarePairCount R 𝔸 (s.succ, (G.X s).castSucc) (h, (𝔸).O h) with hW
  have hsum : (LaurentPolynomial.T 1 : LaurentPolynomial R) •
      (Ξ ∘ₗ oDerivative R 𝔸 P + oDerivative R 𝔸 P ∘ₗ Ξ) + (d ∘ₗ W + W ∘ₗ d) = 0 := by
    have hT (h : Fin (n + 1)) :=
      smul_oDerivative_singleton (R := R) 𝔸 h
    have hexp : (LaurentPolynomial.T 1 : LaurentPolynomial R) •
        (Ξ ∘ₗ oDerivative R 𝔸 P + oDerivative R 𝔸 P ∘ₗ Ξ) =
        ∑ h ∈ P, (Ξ ∘ₗ squareCount R 𝔸 (h, (𝔸).O h) + squareCount R 𝔸 (h, (𝔸).O h) ∘ₗ Ξ) := by
      rw [oDerivative_eq_sum (R := R) 𝔸 P, comp_finsetSum_add_finsetSum_comp, Finset.smul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← hT, smul_add, LinearMap.comp_smul, LinearMap.smul_comp]
    have hWexp : d ∘ₗ W + W ∘ₗ d = ∑ h ∈ P,
        (d ∘ₗ squarePairCount R 𝔸 (s.succ, (G.X s).castSucc) (h, (𝔸).O h) +
          squarePairCount R 𝔸 (s.succ, (G.X s).castSucc) (h, (𝔸).O h) ∘ₗ d) := by
      rw [hW]
      apply LinearMap.ext
      intro x
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
        Finset.sum_add_distrib]
    rw [hexp, hWexp, ← Finset.sum_add_distrib]
    simp_rw [hcount]
    rw [← Finset.sum_smul, Finset.sum_add_distrib, Finset.sum_ite_eq]
    have hrow : (∑ h ∈ P, if (G.X s).castSucc = (𝔸).O h then
        (LaurentPolynomial.T 1 : LaurentPolynomial R) else 0) =
        if s.castSucc ∈ P then LaurentPolynomial.T 1 else 0 := by
      simp_rw [eq_comm (a := (G.X s).castSucc), stabilizeX_O_eq_newRow_iff]
      exact Finset.sum_ite_eq' P s.castSucc _
    rw [hrow]
    by_cases hs : s.succ ∈ P
    · rw [if_pos hs, if_pos (hP.mpr hs), CharTwo.add_self_eq_zero, zero_smul]
    · rw [if_neg hs, if_neg (fun h => hs (hP.mp h)), add_zero, zero_smul]
  have hTunit : IsUnit (LaurentPolynomial.T 1 : LaurentPolynomial R) := LaurentPolynomial.isUnit_T 1
  refine ⟨-((LaurentPolynomial.T (-1) : LaurentPolynomial R) • W), ?_⟩
  have h2 := congrArg (fun f => (LaurentPolynomial.T (-1) : LaurentPolynomial R) • f)
    (eq_neg_of_add_eq_zero_left hsum)
  simp only [smul_smul, ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero,
    one_smul, smul_neg, smul_add] at h2
  rw [h2, LinearMap.comp_neg, LinearMap.neg_comp, LinearMap.comp_smul, LinearMap.smul_comp,
    neg_add]

/-! ### The transferred derivatives -/

/-- The transfer of the new-X derivative kills the first component of its output. -/
theorem fst_comp_contractionTransfer_stabilizationXDerivative :
    LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
      contractionTransfer (fullStabilizationTransferredRetraction G s R)
        (stabilizationXDerivative G s R) = 0 := by
  apply LinearMap.ext
  intro z
  exact fullStabilizationTransferredRetraction_proj_XDerivative_fst G s R _

/-- The transfer of the new-X derivative sends the first copy to the second copy. -/
theorem contractionTransfer_stabilizationXDerivative_comp_inl :
    contractionTransfer (fullStabilizationTransferredRetraction G s R)
        (stabilizationXDerivative G s R) ∘ₗ
      LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) =
    LinearMap.inr (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  change (fullStabilizationTransferredRetraction G s R).proj
      (stabilizationXDerivative G s R
        ((fullStabilizationTransferredRetraction G s R).incl (single x 1, 0))) = (0, single x 1)
  rw [fullStabilizationTransferredRetraction_incl_first_single, map_sub, map_sub,
    fullStabilizationTransferredRetraction_proj_XDerivative_homotopy, sub_zero,
    fullStabilizationTransferredRetraction_proj_XDerivative_partner]

theorem stabilizationColourTransfer_chain :
    laurentDifferential 𝔸 R ∘ₗ oDerivative R 𝔸 P =
      oDerivative R 𝔸 P ∘ₗ laurentDifferential 𝔸 R :=
  laurentDifferential_comp_oDerivative_eq 𝔸 P

/-- The anticommutator of the transferred new-O derivative with `T` is null-homotopic. -/
theorem isNullHomotopic_inl_snd_anticomm_stabilizationColourTransfer :
    IsNullHomotopic ((laurentDifferential G R).prodMap (laurentDifferential G R))
      ((laurentDifferential G R).prodMap (laurentDifferential G R))
      ((LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
          LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n)) ∘ₗ
          stabilizationColourTransfer G s R P +
        stabilizationColourTransfer G s R P ∘ₗ
          (LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
            LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n))) := by
  set c := fullStabilizationTransferredRetraction G s R
  have h1 := isNullHomotopic_contractionTransfer c
    (isNullHomotopic_stabilizationODerivative_anticomm G s R P)
  have h2 := isNullHomotopic_contractionTransfer_anticomm_sub c
    (stabilizationODerivative_chain G s R) (stabilizationColourTransfer_chain G s R P)
  have h := h1.sub h2
  rw [sub_sub_cancel] at h
  have hL : contractionTransfer c (stabilizationODerivative G s R) =
      LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
        LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) :=
    fullStabilizationTransferredRetraction_proj_ODerivative_incl G s R
  rw [hL] at h
  obtain ⟨K, hK⟩ := h
  exact ⟨K, by rw [← stabilizationTransferredDifferential_eq_old_double]; exact hK⟩

/-- Under the colour condition, the anticommutator of the transferred new-X derivative with `T`
is null-homotopic. -/
theorem isNullHomotopic_X_anticomm_stabilizationColourTransfer
    (hP : s.castSucc ∈ P ↔ s.succ ∈ P) :
    IsNullHomotopic ((laurentDifferential G R).prodMap (laurentDifferential G R))
      ((laurentDifferential G R).prodMap (laurentDifferential G R))
      (contractionTransfer (fullStabilizationTransferredRetraction G s R)
          (stabilizationXDerivative G s R) ∘ₗ stabilizationColourTransfer G s R P +
        stabilizationColourTransfer G s R P ∘ₗ
          contractionTransfer (fullStabilizationTransferredRetraction G s R)
            (stabilizationXDerivative G s R)) := by
  set c := fullStabilizationTransferredRetraction G s R
  have h1 := isNullHomotopic_contractionTransfer c
    (isNullHomotopic_stabilizationXDerivative_anticomm G s R P hP)
  have h2 := isNullHomotopic_contractionTransfer_anticomm_sub c
    (stabilizationXDerivative_chain G s R) (stabilizationColourTransfer_chain G s R P)
  have h := h1.sub h2
  rw [sub_sub_cancel] at h
  obtain ⟨K, hK⟩ := h
  exact ⟨K, by rw [← stabilizationTransferredDifferential_eq_old_double]; exact hK⟩

/-! ### The three blocks -/

/-- The block of the transferred colour derivative from the first copy to the second copy is
null-homotopic. -/
theorem isNullHomotopic_stabilizationColourTransfer_snd_inl :
    IsNullHomotopic (laurentDifferential G R) (laurentDifferential G R)
      (LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
        stabilizationColourTransfer G s R P ∘ₗ
          LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n)) :=
  isNullHomotopic_snd_comp_inl_of_anticomm
    (isNullHomotopic_inl_snd_anticomm_stabilizationColourTransfer G s R P)

/-- The two diagonal blocks of the transferred colour derivative agree up to homotopy. -/
theorem isNullHomotopic_stabilizationColourTransfer_diagonal :
    IsNullHomotopic (laurentDifferential G R) (laurentDifferential G R)
      (LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
          stabilizationColourTransfer G s R P ∘ₗ
            LinearMap.inr (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) +
        LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
          stabilizationColourTransfer G s R P ∘ₗ
            LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n)) :=
  isNullHomotopic_diagonal_of_anticomm
    (isNullHomotopic_inl_snd_anticomm_stabilizationColourTransfer G s R P)

/-- Under the colour condition, the block of the transferred colour derivative from the second
copy to the first copy is null-homotopic. -/
theorem isNullHomotopic_stabilizationColourTransfer_fst_inr
    (hP : s.castSucc ∈ P ↔ s.succ ∈ P) :
    IsNullHomotopic (laurentDifferential G R) (laurentDifferential G R)
      (LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
        stabilizationColourTransfer G s R P ∘ₗ
          LinearMap.inr (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n)) :=
  isNullHomotopic_fst_comp_inr_of_anticomm
    (fst_comp_contractionTransfer_stabilizationXDerivative G s R)
    (contractionTransfer_stabilizationXDerivative_comp_inl G s R)
    (isNullHomotopic_X_anticomm_stabilizationColourTransfer G s R P hP)

end OnLeConjecture.KnotFloer.GridFull
