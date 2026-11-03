/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridScissorSequencePhase

/-!
# The scissor phase and its spanning tree

This file completes the combinatorics of the star scissors of Section 9 of the written proof of
Statement E (`statement_E_complete_proof.tex`, subsections "Signed word grids and the scissor
switches" and "The explicit forest for O-switch selection").

For a normalized factorization `F` with strand `0` in every factor cycle and transitive factor
permutations, every signed word grid `H` of the product reaches, by a scissor phase, a grid `K`
such that (`exists_scissorPhase`)

* the number of `X` switches is `F.scissorShiftCount`;
* the `O` switches record the edges `(Z l x, Z 0 x)` of the selected leaves, and these edges form
  a spanning tree of the components of `K` (`SpanningTreeEdges`);
* the rows of `K` are ordered by height, and its component permutation sends the last column of
  every rank `x ≥ 1` of a factor to the first column of that rank in the same factor and agrees
  with the matching of the product elsewhere (`IsScissorEndpoint`).

The components of `K` are counted through the strand labels of `ScissorSequenceComponents`: they
are the orbits of the merged permutation of the factor permutations, so there is one main
component and one component for every pair `(l, y)` of a factor and a strand fixed by it. Each
selected edge joins the component of a fixed strand to a component nearer the main one. All
results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory OnLeConjecture.KnotTheory.SignedGrid
  OnLeConjecture.KnotTheory.NormalizedFactorization Equiv

/-- Orbits are transported by `Equiv.permCongr`. -/
theorem sameCycle_permCongr {α β : Type*} (e : α ≃ β) (σ : Perm α) (x y : α) :
    (e.permCongr σ).SameCycle (e x) (e y) ↔ σ.SameCycle x y := by
  have hz : ∀ i : ℤ, e.permCongr (σ ^ i) = (e.permCongr σ) ^ i := fun i => by
    simpa only [Equiv.permCongrHom_coe] using map_zpow e.permCongrHom σ i
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, e.injective ?_⟩
    rw [← hz, Equiv.permCongr_apply, Equiv.symm_apply_apply] at hi
    exact hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← hz, Equiv.permCongr_apply, Equiv.symm_apply_apply, hi]

section Endpoint

variable {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S) (hN : 0 < N)

/-- The component permutation of the scissor endpoint: the last column of every rank `x ≥ 1` of a
factor goes to the first column of that rank in the same factor, and every other column follows
the matching of the product. -/
def IsScissorEndpointPerm (μ : Perm (Fin (prodSize F))) : Prop :=
  (∀ l (x : Fin S), 1 ≤ x.val → μ (colZ F hS l x) = colF F hS l x) ∧
    ∀ d, (∀ l (x : Fin S), 1 ≤ x.val → d ≠ colZ F hS l x) → μ d = prodPerm F d

/-- The corner form of a permutation of the columns. -/
def cornerPerm (μ : Perm (Fin (prodSize F))) : Perm (Fin (factorProduct F.factor).length × Fin 3) :=
  finProdFinEquiv.symm.permCongr μ

theorem permCongr_cornerPerm (μ : Perm (Fin (prodSize F))) :
    finProdFinEquiv.permCongr (cornerPerm F μ) = μ := by
  refine Equiv.ext fun c => ?_
  simp only [cornerPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

theorem cornerPerm_apply (μ : Perm (Fin (prodSize F))) (p : Fin (factorProduct F.factor).length × Fin 3) :
    cornerPerm F μ p = finProdFinEquiv.symm (μ (col F p)) := by
  simp [cornerPerm, Equiv.permCongr_apply]

variable {F hS}

/-- **Components of the scissor endpoint**, in terms of strand labels. -/
theorem sameCycle_endpoint_iff {μ : Perm (Fin (prodSize F))} (hμ : IsScissorEndpointPerm F hS μ)
    (p p' : Fin (factorProduct F.factor).length × Fin 3) :
    μ.SameCycle (col F p) (col F p') ↔
      (segPerm F.factor hS).SameCycle (strandLabel F.factor p) (strandLabel F.factor p') := by
  rw [← permCongr_cornerPerm F μ, sameCycle_permCongr]
  apply sameCycle_iff_strandLabel F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F)
    hS (cornerPerm F μ)
  · intro l x hx
    rw [cornerPerm_apply]
    have := hμ.1 l x (by omega)
    simp only [colZ] at this
    rw [this, colF, col, Equiv.symm_apply_apply]
  · intro q hq
    rw [cornerPerm_apply, hμ.2 _ (fun l x hx he => hq l x (by omega)
      (finProdFinEquiv.injective he)), prodPerm_apply, col, Equiv.symm_apply_apply]

include hN in
/-- **The number of components of the scissor endpoint.** -/
theorem orbitCount_endpoint (hzero : F.StrandZeroInEveryFactor (by omega))
    {μ : Perm (Fin (prodSize F))} (hμ : IsScissorEndpointPerm F hS μ) :
    orbitCount μ = F.auxCount + 1 := by
  rw [← permCongr_cornerPerm F μ, Equiv.orbitCount_permCongr]
  have h1 := orbitCount_eq_of_sameCycle_iff (strandLabel F.factor)
    (strandLabel_surjective F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F) hS)
    (fun p p' => by
      rw [← sameCycle_endpoint_iff hμ, ← sameCycle_permCongr finProdFinEquiv, permCongr_cornerPerm])
  rw [h1, segPerm, orbitCount_mergePerm (by omega) (fun l => hzero l)
    (fun l y hy => F.sameCycle_factor_zero hS hzero l y hy)]
  rfl

omit hN in
theorem strandLabel_colZ (l : Fin (N + B)) (x : Fin S) :
    strandLabel F.factor (lastCorner F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F)
      hS l x) = (l, F.factorPerm l x) :=
  strandLabel_lastCorner F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F) hS l x

include hN in
/-- **Connectivity.** The components of the scissor endpoint and the selected edges connect all
columns. -/
theorem eqvGen_endpoint (htrans : F.Transitive) (hzero : F.StrandZeroInEveryFactor (by omega))
    {μ : Perm (Fin (prodSize F))} (hμ : IsScissorEndpointPerm F hS μ)
    {E : List (Fin (prodSize F) × Fin (prodSize F))}
    (hE : ∀ e, e ∈ E ↔ ∃ (x : Fin S) (l : Fin (N + B)), 1 ≤ x.val ∧ x.val ≤ S - 1 ∧
      l.val ≠ 0 ∧ Selected F hN x l ∧ e = (colZ F hS l x, center F hS hN x))
    (a b : Fin (prodSize F)) :
    Relation.EqvGen (fun a b => μ.SameCycle a b ∨ (a, b) ∈ E) a b := by
  set R : Fin (prodSize F) → Fin (prodSize F) → Prop := fun a b => μ.SameCycle a b ∨ (a, b) ∈ E
  have hpad := SignedGrid.NormalizedFactorization.factor_isPadded F
  set o : Fin S := ⟨0, by omega⟩ with ho
  set root := col F (firstCorner F.factor hpad hS (fac0 hN) o) with hroot
  have hmerge := sameCycle_mergePerm_iff (π := fun l => (F.factor l).permutation) (o := o)
    (fun l => hzero l) (fun l y hy => F.sameCycle_factor_zero hS hzero l y hy)
  -- a column of a moved label lies in the orbit of the root
  have hmain : ∀ p, MergeMoved (fun l => (F.factor l).permutation) (strandLabel F.factor p) →
      Relation.EqvGen R (col F p) root := by
    intro p hp
    apply Relation.EqvGen.rel
    left
    rw [hroot, sameCycle_endpoint_iff hμ, strandLabel_firstCorner, segPerm]
    exact (hmerge _ _).mpr (Or.inr ⟨hp, hzero (fac0 hN)⟩)
  have hZmain : ∀ l (x : Fin S), F.factorPerm l x ≠ x → Relation.EqvGen R (colZ F hS l x) root := by
    intro l x hx
    apply hmain
    rw [strandLabel_colZ]
    simp only [MergeMoved]
    exact fun h => hx ((F.factor l).permutation.injective h)
  have hedge : ∀ l (x : Fin S), 1 ≤ x.val → l.val ≠ 0 → Selected F hN x l →
      Relation.EqvGen R (colZ F hS l x) (center F hS hN x) := by
    intro l x h1 hl hs
    exact Relation.EqvGen.rel _ _ (Or.inr ((hE _).mpr ⟨x, l, h1, by omega, hl, hs, rfl⟩))
  have hcenter : ∀ x : Fin S, 1 ≤ x.val → Relation.EqvGen R (center F hS hN x) root := by
    intro x h1
    by_cases h0 : F.factorPerm (fac0 hN) x = x
    · have hmove := F.exists_factor_moves hS htrans x
      have hst := lstar_spec F hN hmove
      have hst0 : (lstar F hN x).val ≠ 0 := fun e => hst (by
        rw [show lstar F hN x = fac0 hN from Fin.ext e]; exact h0)
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (hedge _ x h1 hst0 (Or.inr ⟨h0, rfl⟩))) (hZmain _ x hst)
    · exact hZmain (fac0 hN) x h0
  have hZ : ∀ l (x : Fin S), 1 ≤ x.val → Relation.EqvGen R (colZ F hS l x) root := by
    intro l x h1
    by_cases hx : F.factorPerm l x = x
    · by_cases hl : l.val = 0
      · have : l = fac0 hN := Fin.ext hl
        subst this
        exact hcenter x h1
      · exact Relation.EqvGen.trans _ _ _ (hedge l x h1 hl (Or.inl hx)) (hcenter x h1)
    · exact hZmain l x hx
  have hall : ∀ a, Relation.EqvGen R a root := by
    intro a
    obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective a
    by_cases hm : MergeMoved (fun l => (F.factor l).permutation) (strandLabel F.factor p)
    · exact hmain p hm
    · rcases hlab : strandLabel F.factor p with ⟨l, y⟩
      rw [hlab] at hm
      simp only [MergeMoved, ne_eq, not_not] at hm
      have hy : 1 ≤ y.val := by
        by_contra h
        have hyo : y = o := Fin.ext (by simp [ho]; omega)
        rw [hyo] at hm
        exact hzero l hm
      have hsame : Relation.EqvGen R (col F p) (colZ F hS l y) := by
        apply Relation.EqvGen.rel
        left
        rw [colZ, sameCycle_endpoint_iff hμ, strandLabel_colZ, hlab]
        change (segPerm F.factor hS).SameCycle (l, y) (l, (F.factor l).permutation y)
        rw [hm]
      exact Relation.EqvGen.trans _ _ _ hsame (hZ l y hy)
  exact Relation.EqvGen.trans _ _ _ (hall a) (Relation.EqvGen.symm _ _ (hall b))

omit hN in
theorem auxCount_eq_sum :
    F.auxCount = ∑ x : Fin S,
      (Finset.univ.filter fun l : Fin (N + B) => F.factorPerm l x = x).card := by
  classical
  rw [auxCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact if_congr (by simp [MergeMoved, factorPerm]) rfl rfl

omit hN in
include hS in
theorem auxCount_eq_sum_filter (hzero : F.StrandZeroInEveryFactor (by omega)) :
    F.auxCount = ∑ x ∈ Finset.univ.filter (fun x : Fin S => 1 ≤ x.val ∧ x.val ≤ S - 1),
      (Finset.univ.filter fun l : Fin (N + B) => F.factorPerm l x = x).card := by
  rw [auxCount_eq_sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hx
  have hx0 : x.val = 0 := by have := x.isLt; by_contra h; exact absurd (hx (by omega)) (by omega)
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l _
  have := hzero l
  rwa [show x = ⟨0, by omega⟩ from Fin.ext hx0]

include hN in
/-- **The scissor phase.** Every signed word grid of the product reaches, by a scissor phase with
`F.scissorShiftCount` adjacent `X` switches, a grid whose recorded `O`-switch edges form a
spanning tree of its components; its rows are ordered by height and its component permutation
is that of the scissor endpoint. -/
theorem exists_scissorPhase (hzero : F.StrandZeroInEveryFactor (by omega)) (htrans : F.Transitive)
    {H : GridDiagram (prodSize F)} (hH : IsSignedWordGrid (factorProduct F.factor) H) :
    ∃ (K : GridDiagram (prodSize F)) (E : List (Fin (prodSize F) × Fin (prodSize F))) (k : ℕ),
      (k : ℤ) = F.scissorShiftCount ∧ ScissorPhase H K k E ∧ SpanningTreeEdges K E ∧
      ∃ (ℓ : List (Fin (prodSize F))) (hnd : ℓ.Nodup) (hl : ℓ.length = prodSize F)
        (μ : Perm (Fin (prodSize F))) (hμ : ∀ d, μ d ≠ d),
        K = phaseGrid (listPerm ℓ hnd hl) μ hμ ∧
        ℓ.Pairwise (fun a b => colHeight F a ≤ colHeight F b) ∧ IsScissorEndpointPerm F hS μ := by
  obtain ⟨ℓ, hnd, hl, μ, hμ, k, E, hsort, hZ, hrest, hph, hk, hmem, hlen⟩ :=
    exists_phase_upto F hS hN htrans hH (S - 1) le_rfl
  have hend : IsScissorEndpointPerm F hS μ :=
    ⟨fun l x h1 => hZ l x h1 (by have := x.isLt; omega),
      fun d hd => hrest d (fun l x h1 _ => hd l x h1)⟩
  have hU : E.length = F.auxCount := by rw [hlen, auxCount_eq_sum_filter (hS := hS) hzero]
  refine ⟨_, E, k, ?_, hph, ⟨?_, ?_⟩, ℓ, hnd, hl, μ, hμ, rfl, hsort, hend⟩
  · rw [← scissorShiftCount_eq F hS, ← hU]
    have hk' : (k : ℤ) + E.length = ((S - 1 : ℕ) : ℤ) * ((N + B - 1 : ℕ) : ℤ) := by
      rw [← Nat.cast_add, hk, Nat.cast_mul]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at hk'
    push_cast at hk' ⊢
    linarith
  · intro a b
    rw [gridComponentPerm_phaseGrid]
    exact eqvGen_endpoint hN htrans hzero hend hmem a b
  · rw [gridComponentPerm_phaseGrid, hU, ← orbitCount_endpoint hN hzero hend, orbitCount_def]

end Endpoint

end OnLeConjecture.KnotFloer.GridFull
