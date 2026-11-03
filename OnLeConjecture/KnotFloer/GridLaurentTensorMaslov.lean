/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentTensorLowerBound

/-!
# The native Maslov complex of the balanced Laurent tensor product

The degree-r submodule is spanned over the coefficient field by homogeneous
pure tensors whose degrees sum to r. The tensor differential restricts to
these submodules and lowers degree by one. The two filtration coordinates
are convolved before restricting to each degree.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti TensorProduct CategoryTheory

variable {K : Type*} [Field K] {n m : ℕ}
variable (G : GridDiagram n) (H : GridDiagram m)

/-- The homogeneous degree-r submodule of the tensor product over the Laurent ring. -/
def laurentTensorMaslovPiece (r : ℤ) :
    Submodule K (LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) :=
  Submodule.span K {z | ∃ p q : ℤ, ∃ c : LaurentChain K n, ∃ d : LaurentChain K m,
    c ∈ laurentMaslovPiece G K p ∧ d ∈ laurentMaslovPiece H K q ∧
      p + q = r ∧ z = c ⊗ₜ[LaurentPolynomial K] d}

/-- The additive group structure induced by the coefficient field on each degree. -/
instance laurentTensorMaslovPieceAddCommGroup (r : ℤ) :
    AddCommGroup (laurentTensorMaslovPiece (K := K) G H r) :=
  Module.addCommMonoidToAddCommGroup K

/-- Homogeneous pure tensors belong to the sum of their Maslov degrees. -/
theorem tmul_mem_laurentTensorMaslovPiece {p q : ℤ}
    {c : LaurentChain K n} {d : LaurentChain K m}
    (hc : c ∈ laurentMaslovPiece G K p) (hd : d ∈ laurentMaslovPiece H K q) :
    c ⊗ₜ[LaurentPolynomial K] d ∈ laurentTensorMaslovPiece G H (p + q) :=
  Submodule.subset_span ⟨p, q, c, d, hc, hd, rfl, rfl⟩

/-- The balanced tensor differential lowers the sum Maslov degree by one. -/
theorem laurentTensorDifferential_mem_maslovPiece {r : ℤ}
    {z : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m}
    (hz : z ∈ laurentTensorMaslovPiece G H r) :
    laurentTensorDifferential (K := K) G H z ∈ laurentTensorMaslovPiece G H (r - 1) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, c, d, hc, hd, hpq, rfl⟩ := hz
    rw [laurentTensorDifferential_tmul]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨p - 1, q, _, _,
        laurentDifferential_mem_maslovPiece G hc, hd, by omega, rfl⟩
    · exact Submodule.subset_span ⟨p, q - 1, _, _, hc,
        laurentDifferential_mem_maslovPiece H hd, by omega, rfl⟩
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul a z _ hz =>
    change ((laurentTensorDifferential (K := K) G H).restrictScalars K) (a • z) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ a hz

/-- The tensor differential restricted between consecutive Maslov pieces. -/
def laurentTensorGradedDifferential (r : ℤ) :
    laurentTensorMaslovPiece (K := K) G H (r + 1) →ₗ[K]
      laurentTensorMaslovPiece (K := K) G H r :=
  { toFun z := ⟨laurentTensorDifferential (K := K) G H z, by
      simpa only [add_sub_cancel_right] using
        laurentTensorDifferential_mem_maslovPiece G H z.property⟩
    map_add' z w := Subtype.ext (map_add (laurentTensorDifferential (K := K) G H)
      (z : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m)
      (w : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m))
    map_smul' a z := Subtype.ext
      (((laurentTensorDifferential (K := K) G H).restrictScalars K).map_smul a
        (z : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m)) }

@[simp]
theorem coe_laurentTensorGradedDifferential (r : ℤ)
    (z : laurentTensorMaslovPiece (K := K) G H (r + 1)) :
    (laurentTensorGradedDifferential G H r z :
      LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) =
        laurentTensorDifferential (K := K) G H z := rfl

variable [CharP K 2]

/-- The native integer-graded complex of the balanced Laurent tensor product. -/
def laurentTensorMaslovComplex : ChainComplex (ModuleCat K) ℤ :=
  ChainComplex.of (fun r => ModuleCat.of K (laurentTensorMaslovPiece (K := K) G H r))
    (fun r => ModuleCat.ofHom (laurentTensorGradedDifferential G H r)) (fun r => by
      ext z
      exact laurentTensorDifferential_sq_eq_zero G H
        (z : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m))

/-- Identify a native tensor chain group with its homogeneous submodule. -/
def laurentTensorMaslovChainEquiv (r : ℤ) :
    (laurentTensorMaslovComplex (K := K) G H).X r ≃ₗ[K]
      laurentTensorMaslovPiece (K := K) G H r :=
  (eqToIso (show (laurentTensorMaslovComplex (K := K) G H).X r =
    ModuleCat.of K (laurentTensorMaslovPiece (K := K) G H r) from rfl)).toLinearEquiv

/-- Under the homogeneous-submodule identification, the native differential is the
already constructed balanced tensor differential. -/
theorem laurentTensorMaslovChainEquiv_d (r : ℤ)
    (z : (laurentTensorMaslovComplex (K := K) G H).X (r + 1)) :
    (laurentTensorMaslovChainEquiv G H r
      ((laurentTensorMaslovComplex (K := K) G H).d (r + 1) r z) :
        LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) =
      laurentTensorDifferential (K := K) G H (laurentTensorMaslovChainEquiv G H (r + 1) z) := by
  simp only [laurentTensorMaslovComplex, ChainComplex.of_d]
  rfl

/-- The outgoing degree-zero differential on underlying tensor chains. -/
theorem laurentTensorMaslovChainEquiv_d_zero
    (z : (laurentTensorMaslovComplex (K := K) G H).X 0) :
    (laurentTensorMaslovChainEquiv G H (-1)
      ((laurentTensorMaslovComplex (K := K) G H).d 0 (-1) z) :
        LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) =
      laurentTensorDifferential (K := K) G H (laurentTensorMaslovChainEquiv G H 0 z) := by
  have h : (0 : ℤ) = -1 + 1 := by omega
  revert z
  rw [h]
  intro z
  exact laurentTensorMaslovChainEquiv_d (K := K) G H (-1) z

/-- Coordinatewise convolution of the raw grid bifiltrations. -/
def laurentTensorBifiltrationLevel (A B : ℝ) :
    Submodule K (LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) :=
  Submodule.span K {z | ∃ a b c d : ℝ,
    ∃ x : LaurentChain K n, ∃ y : LaurentChain K m,
      x ∈ laurentBifiltrationLevel G K a b ∧ y ∈ laurentBifiltrationLevel H K c d ∧
        a + c ≤ A ∧ b + d ≤ B ∧ z = x ⊗ₜ[LaurentPolynomial K] y}

omit [CharP K 2] in
/-- The tensor differential preserves both convolved coordinates. -/
theorem laurentTensorDifferential_mem_bifiltrationLevel (A B : ℝ)
    {z : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m}
    (hz : z ∈ laurentTensorBifiltrationLevel G H A B) :
    laurentTensorDifferential (K := K) G H z ∈ laurentTensorBifiltrationLevel G H A B := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, c, d, x, y, hx, hy, hA, hB, rfl⟩ := hz
    rw [laurentTensorDifferential_tmul]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨a, b, c, d, _, _,
        laurentDifferential_mem_bifiltrationLevel G K a b x hx, hy, hA, hB, rfl⟩
    · exact Submodule.subset_span ⟨a, b, c, d, _, _, hx,
        laurentDifferential_mem_bifiltrationLevel H K c d y hy, hA, hB, rfl⟩
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul a z _ hz =>
    change ((laurentTensorDifferential (K := K) G H).restrictScalars K) (a • z) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ a hz

/-- The native Maslov complex with the coordinatewise tensor bifiltration. -/
def laurentTensorMaslovBifiltration :
    Bifiltration (laurentTensorMaslovComplex (K := K) G H) where
  level A B r := (laurentTensorBifiltrationLevel G H A B).comap
    ((laurentTensorMaslovPiece (K := K) G H r).subtype.comp
      (laurentTensorMaslovChainEquiv G H r).toLinearMap)
  mono r _ _ _ _ hA hB := Submodule.comap_mono (Submodule.span_mono (by
    rintro z ⟨a, b, c, d, x, y, hx, hy, ha, hb, hz⟩
    exact ⟨a, b, c, d, x, y, hx, hy, ha.trans hA, hb.trans hB, hz⟩))
  differential_mem A B i j z hz := by
    by_cases hij : j + 1 = i
    · subst i
      change (laurentTensorMaslovChainEquiv G H j
        ((laurentTensorMaslovComplex (K := K) G H).d (j + 1) j z) :
          LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) ∈
            laurentTensorBifiltrationLevel G H A B
      rw [laurentTensorMaslovChainEquiv_d]
      exact laurentTensorDifferential_mem_bifiltrationLevel G H A B hz
    · rw [(laurentTensorMaslovComplex (K := K) G H).shape i j
        (by simpa only [ComplexShape.down_Rel] using hij)]
      exact Submodule.zero_mem _

/-- The weighted native tensor filtration is contained in the previously constructed
convolution filtration at the same real level. -/
theorem native_weighted_mem_laurentTensorLevel (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (r : ℤ) {s : ℝ} {z : (laurentTensorMaslovComplex (K := K) G H).X r}
    (hz : z ∈ ((laurentTensorMaslovBifiltration G H).weighted t).level s r) :
    (laurentTensorMaslovChainEquiv G H r z :
      LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) ∈
        laurentTensorLevel G H t s := by
  have hα : 0 ≤ 1 - t / 2 := by linarith
  have hβ : 0 ≤ t / 2 := by linarith
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨A, B, hz, hs⟩ := hz
    change (laurentTensorMaslovChainEquiv G H r z :
      LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) ∈
        laurentTensorBifiltrationLevel G H A B at hz
    generalize heq : (laurentTensorMaslovChainEquiv G H r z :
      LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) = v at hz ⊢
    clear heq
    induction hz using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, b, c, d, x, y, hx, hy, hA, hB, rfl⟩ := hv
      apply Submodule.subset_span
      refine ⟨(1 - t / 2) * a + (t / 2) * b,
        (1 - t / 2) * c + (t / 2) * d, x, y,
        Submodule.subset_span ⟨a, b, hx, le_rfl⟩,
        Submodule.subset_span ⟨c, d, hy, le_rfl⟩, ?_, rfl⟩
      have ha := mul_le_mul_of_nonneg_left hA hα
      have hb := mul_le_mul_of_nonneg_left hB hβ
      nlinarith
    | zero => exact Submodule.zero_mem _
    | add v w _ _ hv hw => exact Submodule.add_mem _ hv hw
    | smul a v _ hv => exact Submodule.smul_mem _ a hv
  | zero => simp only [map_zero, ZeroMemClass.coe_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul a z _ hz => simpa using Submodule.smul_mem _ a hz

end OnLeConjecture.KnotFloer.GridFull
