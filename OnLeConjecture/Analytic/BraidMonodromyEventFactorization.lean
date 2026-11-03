/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyFactorization

/-!
# The event factorization from the closed-braid output of the finite projection

This module proves `LevelBraidFactorization.exists_eventFactorizationData`: the closed-braid
output `LevelBraidFactorization A L` of the finite projection of a level gives native route
choices `C` and `EventFactorizationData A L C`. Consequently
`eventFactorizationStatement_of_levelBraidFactorization` proves `EventFactorizationStatement`
from `LevelBraidFactorizationStatement`.

The factors are listed loop by loop. A singular loop of `Q_j` contributes the single factor
`x β_j x⁻¹`, where `x` conjugates the path word of the loop to its core
(`SignedBraidConj.exists_conjugator`). A ramification loop of order `d` contributes `d - 1`
conjugates of `σ_0` (`exists_conjugate_positive_equiv_flatten`). The derivation
`d_S w ∼ q_1 ⋯ q_{N+B}` combines the representation of the outer braid, the homotopy with fixed
endpoints, the concatenation of the loop path words, and the conjugations. The permutations of
the path words of the loops are conjugates of the monodromies of the loops, and the lexicographic
orders at the integer times differ by these permutations; this transfers the transitivity.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory PlaneCurve SignedAdjacentWord

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}
  {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}

namespace LevelBraidFactorization

variable (F : LevelBraidFactorization A L)

/-- The core of a factor: `β_j` on the first `a_j` strands, or `σ_0`. -/
def coreOf : Option (Fin L.points.card) → SignedAdjacentWord A.squareSum
  | some j => liftPositiveWord (F.strands_le_squareSum j) (F.factorWord j)
  | none => firstGeneratorWord A.two_le_squareSum

/-- The factor `γ η γ⁻¹` of a pair formed by a core label and a conjugator. -/
def toFactor (p : Option (Fin L.points.card) × SignedAdjacentWord A.squareSum) :
    SignedAdjacentWord A.squareSum :=
  conjugateWord p.2 (F.coreOf p.1)

/-- The number of factors of a loop. -/
def kindSize : Fin L.points.card ⊕ Fin F.ramCount → ℕ :=
  Sum.elim (fun _ => 1) fun i => F.ramOrder i - 1

/-- The native route choices of the data. -/
def nativeRouteChoice : NativeRouteChoice A L where
  imageWord := F.imageWord
  imageWord_cycleCount := F.imageWord_cycleCount
  imageWord_length := F.imageWord_length
  strands := F.strands
  factorWord := F.factorWord
  two_le_strands := F.two_le_strands
  strands_le := F.strands_le
  factorWord_cycleCount := F.factorWord_cycleCount
  factorWord_generators := F.factorWord_generators
  factorWord_length := F.factorWord_length

/-- The factors of one loop. -/
theorem exists_block (l : Fin (L.points.card + F.ramCount)) :
    ∃ (W : SignedAdjacentWord A.squareSum)
      (blk : List (Option (Fin L.points.card) × SignedAdjacentWord A.squareSum)),
      IsPathWord F.loops (l : ℝ) ((l : ℝ) + 1) W ∧
      SignedBraidEquiv W (blk.map F.toFactor).flatten ∧
      blk.length = F.kindSize (F.loopKind l) ∧
      ∀ j, (blk.map Prod.fst).count (some j) = if F.loopKind l = Sum.inl j then 1 else 0 := by
  obtain ⟨W, hW, hconj⟩ := (F.loop_represented l).exists_isPathWord_signedBraidConj
  obtain ⟨x, hx⟩ := hconj.exists_conjugator
  rcases hk : F.loopKind l with j | i
  · rw [F.loopCore_singular l j hk, toSigned_liftPositive] at hx
    refine ⟨W, [(some j, x)], hW, ?_, by simp [kindSize], fun j' => ?_⟩
    · simpa [toFactor, coreOf, conjugateWord] using hx
    · by_cases hj : j = j'
      · subst hj; simp
      · simp [hj]
  · rw [F.loopCore_ram l i hk] at hx
    obtain ⟨cs, hlen, hcs⟩ := exists_conjugate_positive_equiv_flatten A.two_le_squareSum x
      (liftPositive (F.ramOrder_le i) (coxeterWord (F.ramOrder i)))
    refine ⟨W, cs.map fun c => (none, c), hW, ?_, ?_, fun j => ?_⟩
    · refine hx.trans (hcs.trans (SignedBraidEquiv.of_eq ?_))
      simp only [List.map_map]
      rfl
    · simp [hlen, length_liftPositive, coxeterWord, kindSize]
    · simp [List.count_eq_zero]

theorem sum_kind_eq (j : Fin L.points.card) :
    ∑ l : Fin (L.points.card + F.ramCount),
      (if F.loopKind l = Sum.inl j then 1 else 0) = 1 := by
  rw [Equiv.sum_comp F.loopKind (fun x => if x = Sum.inl j then 1 else 0)]
  simp

theorem sum_kindSize :
    ∑ l : Fin (L.points.card + F.ramCount), F.kindSize (F.loopKind l) =
      L.points.card + ∑ i : Fin F.ramCount, (F.ramOrder i - 1) := by
  rw [Equiv.sum_comp F.loopKind F.kindSize, Fintype.sum_sum_type]
  simp [kindSize]

/-- **The event factorization from the closed-braid output of the finite projection.** -/
theorem exists_eventFactorizationData (F : LevelBraidFactorization A L) :
    ∃ C : NativeRouteChoice A L, Nonempty (EventFactorizationData A L C) := by
  classical
  set N := L.points.card
  set R := F.ramCount
  set r := N + R with hrdef
  set S := A.squareSum
  have hN : 0 < N := by
    change 0 < L.points.card
    rw [L.card_eq]; exact A.count_pos
  have hr : 0 < r := by omega
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  -- The outer path word.
  obtain ⟨Wout, hWout, hconj⟩ := F.outer_represented.exists_isPathWord_signedBraidConj
  have hWout' : IsPathWord (fun k t => F.outer k (t / (r : ℝ))) 0 r Wout := by
    refine IsPathWord.comp_affine (K := F.outer) (φ := fun t => t / (r : ℝ)) (α := 1 / r)
      (β := 0) (by positivity) (fun t => by ring) ?_
    simpa [div_self hrR.ne'] using hWout
  -- The blocks of factors of the loops.
  choose W blk hWp hWeq hlen hcount using F.exists_block
  -- The homotopy with fixed endpoints.
  obtain ⟨H, hHc, hHi, hH0, hH1, hHs0, hHsr⟩ := F.homotopy
  have hloops : IsPathWord F.loops 0 r (List.ofFn W).flatten :=
    isPathWord_ofFn_flatten F.loops_continuousOn F.loops_injective r hr le_rfl W hWp
  have hhom : SignedBraidEquiv Wout (List.ofFn W).flatten := by
    refine isPathWord_homotopy_rel_endpoints (u := 0) (v := (r : ℝ)) hrR hHc hHi
      (fun s hs k => by rw [hHs0 s hs, hHs0 0 ⟨le_rfl, zero_le_one⟩])
      (fun s hs k => by rw [hHsr s hs, hHsr 0 ⟨le_rfl, zero_le_one⟩]) ?_ ?_
    · exact hWout'.of_eqOn fun k t ht => (hH0 k t ht).symm
    · exact hloops.of_eqOn fun k t ht => (hH1 k t ht).symm
  -- The list of all factors.
  set facs := (List.ofFn blk).flatten with hfacs
  set B := ∑ i : Fin R, (F.ramOrder i - 1)
  have hlenfacs : facs.length = N + B := by
    rw [hfacs, List.length_flatten, List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply, hlen]
    exact F.sum_kindSize
  have hprod : SignedBraidEquiv (List.ofFn W).flatten (facs.map F.toFactor).flatten := by
    refine (signedBraidEquiv_ofFn_flatten hWeq).trans (SignedBraidEquiv.of_eq ?_)
    rw [hfacs, List.map_flatten, List.flatten_flatten, List.map_ofFn, List.map_ofFn]
    rfl
  set C := F.nativeRouteChoice
  let E : EventFactorization A L C :=
    { simpleCount := B
      core := fun l' => (facs.get (Fin.cast hlenfacs.symm l')).1
      core_unique := by
        intro j
        have hc : (facs.map Prod.fst).count (some j) = 1 := by
          rw [hfacs, List.map_flatten, List.count_flatten, List.map_ofFn, List.map_ofFn,
            List.sum_ofFn]
          simp only [Function.comp_apply, hcount]
          exact F.sum_kind_eq j
        obtain ⟨i, hi, huniq⟩ := exists_unique_get_of_count_eq_one hc
        have hlm : (facs.map Prod.fst).length = N + B := by rw [List.length_map, hlenfacs]
        refine ⟨Fin.cast hlm i, ?_, fun l' hl' => ?_⟩
        · simpa using hi
        · have := huniq (Fin.cast hlm.symm l') (by simpa using hl')
          rw [← this]
          rfl
      strands_le := F.strands_le_squareSum
      conjugator := fun l' => (facs.get (Fin.cast hlenfacs.symm l')).2 }
  have hfactor : ∀ l', E.factor l' = F.toFactor (facs.get (Fin.cast hlenfacs.symm l')) := by
    intro l'
    have hcore : E.core l' = (facs.get (Fin.cast hlenfacs.symm l')).1 := rfl
    unfold EventFactorization.factor EventFactorization.coreWord
    rw [hcore]
    unfold toFactor coreOf
    rcases (facs.get (Fin.cast hlenfacs.symm l')).1 with _ | j <;> rfl
  have hproduct : E.product = (facs.map F.toFactor).flatten := by
    unfold EventFactorization.product
    rw [show E.factor = fun l' => F.toFactor (facs.get (Fin.cast hlenfacs.symm l')) from
      funext hfactor, ofFn_get_cast]
  refine ⟨C, ⟨{ toEventFactorization := E, derivation := ?_, transitive := ?_ }⟩⟩
  · -- The derivation.
    rw [hproduct]
    exact hconj.symm.trans (hhom.trans hprod).toConj
  · -- Transitivity.
    intro x y
    have hloopI : ∀ l : Fin r, ∀ t ∈ Icc (l : ℝ) ((l : ℝ) + 1), t ∈ Icc (0 : ℝ) (r : ℝ) := by
      intro l t ht
      have hl1 : (l : ℝ) + 1 ≤ r := by exact_mod_cast l.isLt
      exact ⟨(Nat.cast_nonneg _).trans ht.1, ht.2.trans hl1⟩
    have hclose : ∀ l : Fin r, ∃ τ : Equiv.Perm (Fin S),
        ∀ k, F.loops k ((l : ℝ) + 1) = F.loops (τ k) (l : ℝ) := by
      intro l
      obtain ⟨π, hiso⟩ := F.loop_represented l
      refine ⟨π * (PositiveAdjacentWord.permutation (F.loopCore l))⁻¹ * π⁻¹, fun k => ?_⟩
      have := hiso.left.closing (π⁻¹ k)
      simpa [Equiv.Perm.mul_apply] using this
    choose τ hτ using hclose
    set σ : ℕ → Equiv.Perm (Fin S) := fun l => configSort fun k => F.loops k (l : ℝ)
    set G := Subgroup.closure (Set.range fun l' => (E.factor l').permutation)
    have hWG : ∀ l, (W l).permutation ∈ G := by
      intro l
      rw [SignedBraidEquiv.permutation_eq (hWeq l), permutation_flatten]
      apply Subgroup.list_prod_mem
      intro q hq
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw'
      have hpf : p ∈ facs := List.mem_flatten.mpr ⟨blk l, List.mem_ofFn.mpr ⟨l, rfl⟩, hp⟩
      obtain ⟨i, hi⟩ := List.get_of_mem hpf
      apply Subgroup.subset_closure
      refine ⟨Fin.cast hlenfacs i, ?_⟩
      simp only
      rw [hfactor, ← hi]
      rfl
    have hinjl : ∀ l : Fin r, ∀ t ∈ Icc (l : ℝ) ((l : ℝ) + 1), Injective fun k => F.loops k t :=
      fun l t ht => F.loops_injective t (hloopI l t ht)
    have hpermW : ∀ l : Fin r,
        (W l).permutation = (σ l)⁻¹ * (τ l)⁻¹ * σ l := fun l =>
      (hWp l).permutation_of_closing (by linarith) (hinjl l) (hτ l)
    have hσsucc : ∀ l : Fin r, σ (l + 1) = (τ l)⁻¹ * σ l := by
      intro l
      have hv : (fun k => F.loops k (((l : ℕ) + 1 : ℕ) : ℝ)) =
          (fun k => F.loops k (l : ℝ)) ∘ ⇑(τ l) := by
        funext k
        push_cast
        exact hτ l k
      change configSort _ = _
      rw [hv, configSort_comp (hinjl l _ ⟨le_rfl, by linarith⟩)]
    have hσG : ∀ l ≤ r, ∃ h ∈ G, σ l = σ 0 * h := by
      intro l
      induction l with
      | zero => intro _; exact ⟨1, G.one_mem, by simp⟩
      | succ l ih =>
        intro hl
        obtain ⟨h, hh, hσ⟩ := ih (by omega)
        set lf : Fin r := ⟨l, by omega⟩
        refine ⟨h * (W lf).permutation, G.mul_mem hh (hWG lf), ?_⟩
        have e1 := hσsucc lf
        have e2 := hpermW lf
        simp only [lf] at e1 e2
        rw [e1, ← mul_assoc, ← hσ, e2]
        group
    have hτG : ∀ l : Fin r, τ l ∈ G.map (MulAut.conj (σ 0)).toMonoidHom := by
      intro l
      obtain ⟨h, hh, hσ⟩ := hσG l l.isLt.le
      refine Subgroup.mem_map.mpr ⟨(h * (W l).permutation * h⁻¹)⁻¹,
        G.inv_mem (G.mul_mem (G.mul_mem hh (hWG l)) (G.inv_mem hh)), ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hpermW l, hσ]
      group
    have hT : Subgroup.closure {τ' : Equiv.Perm (Fin S) | ∃ l : Fin r,
        ∀ k, F.loops k ((l : ℝ) + 1) = F.loops (τ' k) (l : ℝ)} ≤
        G.map (MulAut.conj (σ 0)).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro τ' ⟨l, hl⟩
      have : τ' = τ l := by
        ext k
        have h1 := (hl k).symm.trans (hτ l k)
        exact congrArg Fin.val (hinjl l _ ⟨le_rfl, by linarith⟩ h1)
      rw [this]
      exact hτG l
    obtain ⟨gg, hgg, hggx⟩ := F.loops_transitive (σ 0 x) (σ 0 y)
    obtain ⟨g₁, hg₁, hg₁eq⟩ := Subgroup.mem_map.mp (hT hgg)
    refine ⟨g₁, hg₁, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hg₁eq
    have : σ 0 (g₁ x) = σ 0 y := by
      rw [← hggx, ← hg₁eq]
      simp [Equiv.Perm.mul_apply]
    exact (σ 0).injective this

end LevelBraidFactorization

/-- **`EventFactorizationStatement` from the closed-braid output of the finite projection.** -/
theorem eventFactorizationStatement_of_levelBraidFactorization
    (h : LevelBraidFactorizationStatement) : EventFactorizationStatement := by
  intro g hd hi
  obtain ⟨A, L, ⟨F⟩⟩ := h g hd hi
  obtain ⟨C, hC⟩ := F.exists_eventFactorizationData
  exact ⟨A, L, C, hC⟩

end OnLeConjecture.Analytic
