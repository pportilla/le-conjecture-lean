/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationColourCenter

/-!
# Colour naturality of the canonical stabilization maps

Let `A = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization of `G` splitting the `X`
marking of column `s`. Its new `O` marking lies in column `s.castSucc`, and the old `O` marking of
the split column lies in column `s.succ`. Let `c = fullStabilizationTransferredRetraction G s R` be
the special contraction of `C(A)` onto `C(G) × C(G)`. The canonical stabilization maps are the
first component of the projection, `fst ∘ c.proj : C(A) → C(G)`, and the inclusion of the first
copy, `c.incl ∘ inl : C(G) → C(A)` (compare `stabilizationCanonicalProjection` and
`stabilizationCanonicalInclusion`).

For a set `P` of columns of `A`, put `P_G = {c | s.castSucc.succAbove c ∈ P}`. This file proves:

* `isNullHomotopic_stabilization_projection_colour`: if `s.castSucc ∈ P ↔ s.succ ∈ P`, then
  `fst ∘ c.proj` intertwines the colour derivatives `Φ_P` of `A` and `Φ_{P_G}` of `G` up to an
  explicit chain homotopy;
* `isNullHomotopic_stabilization_inclusion_colour`: `c.incl ∘ inl` intertwines them up to homotopy,
  for every `P`.

The condition on `P` says that the new `O` marking carries the colour of the old `O` marking of
the split column, which lies on the same component. This is the stabilization case of Lemma
`movesToNativeMap` of the written proof of Statement E (`statement_E_complete_proof.tex`): "A
stabilization gives its new O the colour of its component."

The proof combines the four blocks of the transferred colour derivative `T = c.proj Φ_P c.incl`:
the center block is `Φ_{P_G}` (`stabilizationColourTransfer_center`), the first-to-second block is
null-homotopic, the diagonal blocks agree up to homotopy, and under the condition on `P` the
second-to-first block is null-homotopic (`GridStabilizationColourClifford`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]
  (P : Finset (Fin (n + 1)))

theorem fst_comp_stabilizationTransferredDifferential :
    LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
        stabilizationTransferredDifferential G s R =
      laurentDifferential G R ∘ₗ
        LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) := by
  rw [stabilizationTransferredDifferential_eq_old_double]
  exact fst_comp_prodMap _

theorem snd_comp_stabilizationTransferredDifferential :
    LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
        stabilizationTransferredDifferential G s R =
      laurentDifferential G R ∘ₗ
        LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) := by
  rw [stabilizationTransferredDifferential_eq_old_double]
  exact snd_comp_prodMap _

theorem stabilizationTransferredDifferential_comp_inl :
    stabilizationTransferredDifferential G s R ∘ₗ
        LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) =
      LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
        laurentDifferential G R := by
  rw [stabilizationTransferredDifferential_eq_old_double]
  exact prodMap_comp_inl _

theorem stabilizationTransferredDifferential_comp_inr :
    stabilizationTransferredDifferential G s R ∘ₗ
        LinearMap.inr (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) =
      LinearMap.inr (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
        laurentDifferential G R := by
  rw [stabilizationTransferredDifferential_eq_old_double]
  exact prodMap_comp_inr _

/-- The first diagonal block of the transferred colour derivative is the old colour derivative
up to homotopy. -/
theorem isNullHomotopic_stabilizationColourTransfer_fst_inl_sub :
    IsNullHomotopic (laurentDifferential G R) (laurentDifferential G R)
      (LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
          stabilizationColourTransfer G s R P ∘ₗ
            LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) -
        oDerivative R G (P.preimage s.castSucc.succAbove
          s.castSucc.succAbove_right_injective.injOn)) := by
  have h := isNullHomotopic_stabilizationColourTransfer_diagonal G s R P
  rw [stabilizationColourTransfer_center] at h
  rw [laurentModule_sub_eq_add (R := R), add_comm]
  exact h

/-- **Colour naturality of the canonical stabilization projection.** -/
theorem isNullHomotopic_stabilization_projection_colour (hP : s.castSucc ∈ P ↔ s.succ ∈ P) :
    IsNullHomotopic (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R)
      (laurentDifferential G R)
      ((LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
            (fullStabilizationTransferredRetraction G s R).proj) ∘ₗ
          oDerivative R (G.stabilizeX s.castSucc (G.X s).castSucc s) P -
        oDerivative R G (P.preimage s.castSucc.succAbove
            s.castSucc.succAbove_right_injective.injOn) ∘ₗ
          (LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
            (fullStabilizationTransferredRetraction G s R).proj)) := by
  have hfst := fst_comp_stabilizationTransferredDifferential G s R
  have hsnd := snd_comp_stabilizationTransferredDifferential G s R
  have hπ1 : laurentDifferential G R ∘ₗ
        (LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
          (fullStabilizationTransferredRetraction G s R).proj) =
      (LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
          (fullStabilizationTransferredRetraction G s R).proj) ∘ₗ
        laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R := by
    apply LinearMap.ext
    intro z
    have h1 := LinearMap.congr_fun (fullStabilizationTransferredRetraction G s R).proj_comp_dM z
    have h2 := LinearMap.congr_fun hfst ((fullStabilizationTransferredRetraction G s R).proj z)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hπ2 : laurentDifferential G R ∘ₗ
        (LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
          (fullStabilizationTransferredRetraction G s R).proj) =
      (LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
          (fullStabilizationTransferredRetraction G s R).proj) ∘ₗ
        laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R := by
    apply LinearMap.ext
    intro z
    have h1 := LinearMap.congr_fun (fullStabilizationTransferredRetraction G s R).proj_comp_dM z
    have h2 := LinearMap.congr_fun hsnd ((fullStabilizationTransferredRetraction G s R).proj z)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  have h1 := (isNullHomotopic_proj_comp_sub (fullStabilizationTransferredRetraction G s R)
    (stabilizationColourTransfer_chain G s R P)).comp_left hfst
  have h2 := (isNullHomotopic_stabilizationColourTransfer_fst_inl_sub G s R P).comp_right hπ1
  have h3 := (isNullHomotopic_stabilizationColourTransfer_fst_inr G s R P hP).comp_right hπ2
  convert h1.add (h2.add h3) using 1
  apply LinearMap.ext
  intro z
  have hT : stabilizationColourTransfer G s R P
        ((fullStabilizationTransferredRetraction G s R).proj z) =
      stabilizationColourTransfer G s R P
          (((fullStabilizationTransferredRetraction G s R).proj z).1, 0) +
        stabilizationColourTransfer G s R P
          (0, ((fullStabilizationTransferredRetraction G s R).proj z).2) := by
    rw [← map_add]
    congr 1
    ext <;> simp
  change ((fullStabilizationTransferredRetraction G s R).proj
        (oDerivative R (G.stabilizeX s.castSucc (G.X s).castSucc s) P z)).1 -
      oDerivative R G (P.preimage s.castSucc.succAbove
        s.castSucc.succAbove_right_injective.injOn)
        ((fullStabilizationTransferredRetraction G s R).proj z).1 =
    (((fullStabilizationTransferredRetraction G s R).proj
          (oDerivative R (G.stabilizeX s.castSucc (G.X s).castSucc s) P z)).1 -
        (stabilizationColourTransfer G s R P
          ((fullStabilizationTransferredRetraction G s R).proj z)).1) +
      (((stabilizationColourTransfer G s R P
            (((fullStabilizationTransferredRetraction G s R).proj z).1, 0)).1 -
          oDerivative R G (P.preimage s.castSucc.succAbove
            s.castSucc.succAbove_right_injective.injOn)
            ((fullStabilizationTransferredRetraction G s R).proj z).1) +
        (stabilizationColourTransfer G s R P
          (0, ((fullStabilizationTransferredRetraction G s R).proj z).2)).1)
  rw [hT, Prod.fst_add]
  abel

/-- **Colour naturality of the canonical stabilization inclusion.** -/
theorem isNullHomotopic_stabilization_inclusion_colour :
    IsNullHomotopic (laurentDifferential G R)
      (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R)
      (oDerivative R (G.stabilizeX s.castSucc (G.X s).castSucc s) P ∘ₗ
          ((fullStabilizationTransferredRetraction G s R).incl ∘ₗ
            LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n)) -
        ((fullStabilizationTransferredRetraction G s R).incl ∘ₗ
            LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n)) ∘ₗ
          oDerivative R G (P.preimage s.castSucc.succAbove
            s.castSucc.succAbove_right_injective.injOn)) := by
  have hinl := stabilizationTransferredDifferential_comp_inl G s R
  have hinr := stabilizationTransferredDifferential_comp_inr G s R
  set c := fullStabilizationTransferredRetraction G s R
  have hι1 : (c.incl ∘ₗ LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n))
        ∘ₗ laurentDifferential G R =
      laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
        (c.incl ∘ₗ LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n)) := by
    rw [LinearMap.comp_assoc, ← hinl, ← LinearMap.comp_assoc, ← c.dM_comp_incl,
      LinearMap.comp_assoc]
  have hι2 : (c.incl ∘ₗ LinearMap.inr (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n))
        ∘ₗ laurentDifferential G R =
      laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
        (c.incl ∘ₗ LinearMap.inr (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n)) := by
    rw [LinearMap.comp_assoc, ← hinr, ← LinearMap.comp_assoc, ← c.dM_comp_incl,
      LinearMap.comp_assoc]
  have h1 := (isNullHomotopic_comp_incl_sub c
    (stabilizationColourTransfer_chain G s R P)).comp_right hinl
  have h2 := (isNullHomotopic_stabilizationColourTransfer_fst_inl_sub G s R P).comp_left hι1
  have h3 := (isNullHomotopic_stabilizationColourTransfer_snd_inl G s R P).comp_left hι2
  convert h1.add (h2.add h3) using 1
  apply LinearMap.ext
  intro z
  have hT : c.incl (stabilizationColourTransfer G s R P (z, 0)) =
      c.incl ((stabilizationColourTransfer G s R P (z, 0)).1, 0) +
        c.incl (0, (stabilizationColourTransfer G s R P (z, 0)).2) := by
    rw [← map_add]
    congr 1
    ext <;> simp
  change oDerivative R (G.stabilizeX s.castSucc (G.X s).castSucc s) P (c.incl (z, 0)) -
      c.incl (oDerivative R G (P.preimage s.castSucc.succAbove
        s.castSucc.succAbove_right_injective.injOn) z, 0) =
    (oDerivative R (G.stabilizeX s.castSucc (G.X s).castSucc s) P (c.incl (z, 0)) -
        c.incl (stabilizationColourTransfer G s R P (z, 0))) +
      (c.incl ((stabilizationColourTransfer G s R P (z, 0)).1 -
          oDerivative R G (P.preimage s.castSucc.succAbove
            s.castSucc.succAbove_right_injective.injOn) z, 0) +
        c.incl (0, (stabilizationColourTransfer G s R P (z, 0)).2))
  have hsub : c.incl ((stabilizationColourTransfer G s R P (z, 0)).1 -
        oDerivative R G (P.preimage s.castSucc.succAbove
          s.castSucc.succAbove_right_injective.injOn) z, 0) =
      c.incl ((stabilizationColourTransfer G s R P (z, 0)).1, 0) -
        c.incl (oDerivative R G (P.preimage s.castSucc.succAbove
          s.castSucc.succAbove_right_injective.injOn) z, 0) := by
    rw [← map_sub]
    congr 1
    ext <;> simp
  rw [hT, hsub]
  abel

end OnLeConjecture.KnotFloer.GridFull
