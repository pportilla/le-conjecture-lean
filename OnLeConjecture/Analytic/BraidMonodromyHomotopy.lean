/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyPathWord
public import OnLeConjecture.Analytic.MultiSheetBraidClosed

/-!
# Homotopies of configurations give finite word relations

This module proves the word-level content of the subsection "Why the configuration homotopies
give finite word relations" of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`). The argument here is different from the written one: no
piecewise-affine approximation and no genericity of the homotopy is used. The local words of
`BraidMonodromyLocalWord.lean` are attached to the edges of a fine square grid on the parameter
rectangle; every grid square gives a relation by the independence of the center and the
cocycle property, and a discrete Stokes argument assembles these relations.

* `isPathWord_homotopy`: for a family `H s` of strand families on `[u, v]`, `s ∈ [0, 1]`,
  jointly continuous with pairwise distinct points, the path words satisfy
  `W₀ W_v ≡ W_u W₁`, where `W₀`, `W₁` are the path words of `H 0`, `H 1` and `W_u`, `W_v` those of
  the two side paths `s ↦ H s · u` and `s ↦ H s · v`.
* `isPathWord_homotopy_rel_endpoints`: a homotopy with fixed endpoint configurations preserves
  the path word up to `SignedBraidEquiv`.
* `ClosedStrandBraidIsotopic.signedBraidConj`: isotopic closed braids
  (`ClosedStrandBraidIsotopic`, job J14) have conjugate path words. The two side paths of a closed
  braid isotopy differ by the relabelling of the monodromy, so the moving basepoint contributes a
  conjugation.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory

variable {S : ℕ}

/-- **Homotopy relation of path words.** For a family `H s` of strand families on `[u, v]`,
jointly continuous on `[0, 1] × [u, v]` with pairwise distinct points, the path words of
`H 0`, `H 1` and of the side paths at `u` and `v` satisfy `W₀ W_v ≡ W_u W₁`. -/
theorem isPathWord_homotopy {H : ℝ → Fin S → ℝ → ℂ} {u v : ℝ} (huv : u < v)
    (hcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ => H p.1 k p.2) (Icc 0 1 ×ˢ Icc u v))
    (hinj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc u v, Injective fun k => H s k t)
    {W₀ W₁ Wu Wv : SignedAdjacentWord S}
    (h₀ : IsPathWord (H 0) u v W₀) (h₁ : IsPathWord (H 1) u v W₁)
    (hu : IsPathWord (fun k s => H s k u) 0 1 Wu) (hv : IsPathWord (fun k s => H s k v) 0 1 Wv) :
    SignedBraidEquiv (W₀ ++ Wv) (Wu ++ W₁) := by
  obtain ⟨m, hm, δ, hδ, hsep, hnear⟩ := exists_config_modulus
    (F := fun p : ℝ × ℝ => fun k => H p.1 k p.2) (isCompact_Icc.prod isCompact_Icc) hcont
    (fun p hp => hinj p.1 hp.1 p.2 hp.2)
  obtain ⟨δ₀, hδ₀, h₀⟩ := h₀
  obtain ⟨δ₁, hδ₁, h₁⟩ := h₁
  obtain ⟨δu, hδu, hu⟩ := hu
  obtain ⟨δv, hδv, hv⟩ := hv
  set ε := min δ (min (min δ₀ δ₁) (min δu δv)) with hε
  have hεpos : 0 < ε := lt_min hδ (lt_min (lt_min hδ₀ hδ₁) (lt_min hδu hδv))
  -- A grid fine in both directions.
  obtain ⟨N₁, hN₁, hf₁⟩ := exists_uniform_fine huv hεpos
  obtain ⟨N₂, hN₂, hf₂⟩ := exists_uniform_fine (zero_lt_one' ℝ) hεpos
  set N := N₁ * N₂ with hN
  have hNpos : 0 < N := Nat.mul_pos hN₁ hN₂
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hNr₁ : (N₁ : ℝ) ≤ N := by exact_mod_cast Nat.le_mul_of_pos_right N₁ hN₂
  have hNr₂ : (N₂ : ℝ) ≤ N := by exact_mod_cast Nat.le_mul_of_pos_left N₂ hN₁
  have hN₁r : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
  have hN₂r : (0 : ℝ) < N₂ := by exact_mod_cast hN₂
  have hft : (v - u) / N < ε :=
    (div_le_div_of_nonneg_left (by linarith) hN₁r hNr₁).trans_lt hf₁
  have hfs : (1 - 0) / N < ε :=
    (div_le_div_of_nonneg_left (by norm_num) hN₂r hNr₂).trans_lt hf₂
  have Pt := isStrictPartition_uniform huv hNpos hft
  have Ps := isStrictPartition_uniform (zero_lt_one' ℝ) hNpos hfs
  set t := uniformPartition u v N
  set s := uniformPartition 0 1 N
  let X : ℕ → ℕ → Fin S → ℂ := fun a b k => H (s b) k (t a)
  have hXmem : ∀ a ≤ N, ∀ b ≤ N, (s b, t a) ∈ Icc (0 : ℝ) 1 ×ˢ Icc u v :=
    fun a ha b hb => ⟨Ps.mem_Icc hb, Pt.mem_Icc ha⟩
  -- Every grid square is a cell.
  have hcell : ∀ a < N, ∀ b < N, IsConfigCell
      {X a b, X (a + 1) b, X a (b + 1), X (a + 1) (b + 1)} m := by
    intro a ha b hb
    have hmem : ∀ a' ∈ ({a, a + 1} : Set ℕ), ∀ b' ∈ ({b, b + 1} : Set ℕ),
        (s b', t a') ∈ Icc (0 : ℝ) 1 ×ˢ Icc u v := by
      rintro a' ha' b' hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha' hb'
      exact hXmem a' (by omega) b' (by omega)
    have hclose : ∀ a' ∈ ({a, a + 1} : Set ℕ), ∀ b' ∈ ({b, b + 1} : Set ℕ),
        ∀ a'' ∈ ({a, a + 1} : Set ℕ), ∀ b'' ∈ ({b, b + 1} : Set ℕ),
        ConfigNear (X a' b') (X a'' b'') (m / 8) := by
      intro a' ha' b' hb' a'' ha'' b'' hb''
      apply hnear _ (hmem a' ha' b' hb') _ (hmem a'' ha'' b'' hb'')
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      have hgs := Ps.gap b hb
      have hgt := Pt.gap a ha
      have hss := Ps.step b hb
      have hst := Pt.step a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha' hb' ha'' hb''
      constructor
      · rw [abs_lt]
        rcases hb' with rfl | rfl <;> rcases hb'' with rfl | rfl <;> constructor <;>
          linarith [min_le_left δ (min (min δ₀ δ₁) (min δu δv))]
      · rw [abs_lt]
        rcases ha' with rfl | rfl <;> rcases ha'' with rfl | rfl <;> constructor <;>
          linarith [min_le_left δ (min (min δ₀ δ₁) (min δu δv))]
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hsep _ (hmem a (by simp) b (by simp))
      · exact hsep _ (hmem (a + 1) (by simp) b (by simp))
      · exact hsep _ (hmem a (by simp) (b + 1) (by simp))
      · exact hsep _ (hmem (a + 1) (by simp) (b + 1) (by simp))
    · intro x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        exact hclose _ (by simp) _ (by simp) _ (by simp) _ (by simp)
  -- The relation of one grid square.
  have hsquare : ∀ a < N, ∀ b < N, SignedBraidEquiv
      (localWord (X a b) (X a b) (X (a + 1) b) ++
        localWord (X (a + 1) b) (X (a + 1) b) (X (a + 1) (b + 1)))
      (localWord (X a b) (X a b) (X a (b + 1)) ++
        localWord (X a (b + 1)) (X a (b + 1)) (X (a + 1) (b + 1))) := by
    intro a ha b hb
    have hC := hcell a ha b hb
    have m00 : X a b ∈ ({X a b, X (a + 1) b, X a (b + 1), X (a + 1) (b + 1)} :
      Set (Fin S → ℂ)) := by simp
    have m10 : X (a + 1) b ∈ ({X a b, X (a + 1) b, X a (b + 1), X (a + 1) (b + 1)} :
      Set (Fin S → ℂ)) := by simp
    have m01 : X a (b + 1) ∈ ({X a b, X (a + 1) b, X a (b + 1), X (a + 1) (b + 1)} :
      Set (Fin S → ℂ)) := by simp
    have m11 : X (a + 1) (b + 1) ∈ ({X a b, X (a + 1) b, X a (b + 1), X (a + 1) (b + 1)} :
      Set (Fin S → ℂ)) := by simp
    have l1 := (SignedBraidEquiv.refl (localWord (X a b) (X a b) (X (a + 1) b))).append
      (hC.localWord_center hm m10 m00 m10 m11)
    have l2 := (SignedBraidEquiv.refl (localWord (X a b) (X a b) (X a (b + 1)))).append
      (hC.localWord_center hm m01 m00 m01 m11)
    exact (l1.trans (localWord_comp _ _ _ _)).trans (l2.trans (localWord_comp _ _ _ _)).symm
  -- Discrete Stokes, first along a row, then along the columns.
  let V : ℕ → ℕ → SignedAdjacentWord S := fun a b => localWord (X a b) (X a b) (X a (b + 1))
  have hrow : ∀ b < N, ∀ a ≤ N, SignedBraidEquiv
      (chainWord (fun a' => X a' b) a ++ V a b)
      (V 0 b ++ chainWord (fun a' => X a' (b + 1)) a) := by
    intro b hb a
    induction a with
    | zero => intro _; simpa using SignedBraidEquiv.refl (V 0 b)
    | succ a ih =>
      intro ha
      rw [chainWord_succ, chainWord_succ, List.append_assoc]
      have h1 := (SignedBraidEquiv.refl (chainWord (fun a' => X a' b) a)).append
        (hsquare a (by omega) b hb)
      refine h1.trans ?_
      rw [← List.append_assoc]
      have h2 := (ih (by omega)).append (SignedBraidEquiv.refl
        (localWord (X a (b + 1)) (X a (b + 1)) (X (a + 1) (b + 1))))
      simpa [List.append_assoc, V] using h2
  have hcol : ∀ b ≤ N, SignedBraidEquiv
      (chainWord (fun a => X a 0) N ++ chainWord (fun b' => X N b') b)
      (chainWord (fun b' => X 0 b') b ++ chainWord (fun a => X a b) N) := by
    intro b
    induction b with
    | zero => intro _; simpa using SignedBraidEquiv.refl _
    | succ b ih =>
      intro hb
      rw [chainWord_succ, chainWord_succ (fun b' => X 0 b')]
      have h1 := (ih (by omega)).append (SignedBraidEquiv.refl (V N b))
      rw [← List.append_assoc]
      refine h1.trans ?_
      rw [List.append_assoc, List.append_assoc]
      exact (SignedBraidEquiv.refl _).append (hrow b (by omega) N le_rfl)
  have hfinal := hcol N le_rfl
  -- Identify the four boundary chains with the given path words.
  have e0 : SignedBraidEquiv (chainWord (fun a => X a 0) N) W₀ := by
    have := h₀ t N (Pt.mono (min_le_right _ _ |>.trans (min_le_left _ _) |>.trans
      (min_le_left _ _)))
    simpa [X, s, Ps.zero] using this
  have e1 : SignedBraidEquiv (chainWord (fun a => X a N) N) W₁ := by
    have := h₁ t N (Pt.mono (min_le_right _ _ |>.trans (min_le_left _ _) |>.trans
      (min_le_right _ _)))
    simpa [X, s, Ps.last] using this
  have eu : SignedBraidEquiv (chainWord (fun b => X 0 b) N) Wu := by
    have := hu s N (Ps.mono (min_le_right _ _ |>.trans (min_le_right _ _) |>.trans
      (min_le_left _ _)))
    simpa [X, t, Pt.zero] using this
  have ev : SignedBraidEquiv (chainWord (fun b => X N b) N) Wv := by
    have := hv s N (Ps.mono (min_le_right _ _ |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _)))
    simpa [X, t, Pt.last] using this
  exact ((e0.symm.append ev.symm).trans hfinal).trans (eu.append e1)

/-- **Homotopy with fixed endpoints.** If the endpoint configurations of the strand families
`H s` do not depend on `s`, the path words of `H 0` and `H 1` are equivalent. -/
theorem isPathWord_homotopy_rel_endpoints {H : ℝ → Fin S → ℝ → ℂ} {u v : ℝ} (huv : u < v)
    (hcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ => H p.1 k p.2) (Icc 0 1 ×ˢ Icc u v))
    (hinj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc u v, Injective fun k => H s k t)
    (hu : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k, H s k u = H 0 k u)
    (hv : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k, H s k v = H 0 k v)
    {W₀ W₁ : SignedAdjacentWord S} (h₀ : IsPathWord (H 0) u v W₀)
    (h₁ : IsPathWord (H 1) u v W₁) : SignedBraidEquiv W₀ W₁ := by
  have hu' : IsPathWord (fun k s => H s k u) 0 1 [] :=
    IsPathWord.const fun k s hs => by rw [hu s hs k]
  have hv' : IsPathWord (fun k s => H s k v) 0 1 [] :=
    IsPathWord.const fun k s hs => by rw [hv s hs k]
  simpa using isPathWord_homotopy huv hcont hinj h₀ h₁ hu' hv'

/-- The side path `s ↦ H s · t₀` of a jointly continuous family is continuous. -/
theorem continuousOn_side {H : ℝ → Fin S → ℝ → ℂ} {u v t₀ : ℝ}
    (hcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ => H p.1 k p.2) (Icc 0 1 ×ˢ Icc u v))
    (ht₀ : t₀ ∈ Icc u v) (k : Fin S) : ContinuousOn (fun s => H s k t₀) (Icc 0 1) :=
  (hcont k).comp (Continuous.prodMk continuous_id continuous_const).continuousOn
    fun _ hs => ⟨hs, ht₀⟩

/-- **Isotopic closed braids have conjugate path words.** If the closed braids `K₀` and `K₁`
over `[u, v]` are isotopic through closed braids with monodromy `τ`, any path words of `K₀` and
`K₁` on `[u, v]` are conjugate by a finite signed-word derivation. -/
theorem ClosedStrandBraidIsotopic.signedBraidConj {K₀ K₁ : Fin S → ℝ → ℂ} {u v : ℝ}
    {τ : Equiv.Perm (Fin S)} (h : ClosedStrandBraidIsotopic K₀ K₁ u v τ)
    {W₀ W₁ : SignedAdjacentWord S} (h₀ : IsPathWord K₀ u v W₀) (h₁ : IsPathWord K₁ u v W₁) :
    SignedBraidConj W₀ W₁ := by
  obtain ⟨H, hH, hH0, hH1⟩ := h
  have huv := hH.lt
  have huI : u ∈ Icc u v := ⟨le_rfl, huv.le⟩
  have hvI : v ∈ Icc u v := ⟨huv.le, le_rfl⟩
  obtain ⟨Wu, hWu⟩ := exists_isPathWord (K := fun k s => H s k u) (zero_lt_one' ℝ)
    (continuousOn_side hH.continuousOn huI) (fun s hs => hH.injective s hs u huI)
  have hWv : IsPathWord (fun k s => H s k v) 0 1 Wu := by
    have heq : IsPathWord (fun k s => H s (τ k) u) 0 1 Wu :=
      (IsPathWord.relabel (fun s hs => hH.injective s hs u huI) τ).mpr hWu
    exact heq.of_eqOn fun k s hs => (hH.closing s hs k).symm
  have h₀' : IsPathWord (H 0) u v W₀ := h₀.of_eqOn fun k t ht => (hH0 k t ht).symm
  have h₁' : IsPathWord (H 1) u v W₁ := h₁.of_eqOn fun k t ht => (hH1 k t ht).symm
  have hrel := isPathWord_homotopy huv hH.continuousOn hH.injective h₀' h₁' hWu hWv
  exact SignedBraidConj.of_equiv_conjugate hrel

end OnLeConjecture.Analytic
