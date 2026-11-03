/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineUnitChartNorm

/-!
# Degree of the determinant norm on the C9 unit chart

The power basis of the C9 unit chart algebra carries the filtration induced by
total degree in the three affine coordinates. The two cubic relations preserve
this filtration. A homogeneous difference section of degree `N` therefore acts
by a matrix whose weighted entry degrees imply that its determinant has degree
at most `9N`.
-/

public section

noncomputable section

open scoped BigOperators

namespace OnLeConjecture.DThree.ECNineDegree

open _root_.Polynomial

theorem natDegree_sum_le_of_forall
    {R : Type} [Semiring R] {ι : Type}
    (s : Finset ι) (f : ι → R[X]) (D : ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ D) :
    (∑ i ∈ s, f i).natDegree ≤ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (natDegree_add_le _ _).trans
        (max_le (h a (by simp)) (ih (fun i hi => h i (by simp [hi]))))

theorem natDegree_det_le_of_weighted_entries
    {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R[X]) (w : ι → ℕ) (D : ℕ)
    (hentry : ∀ i j,
      M i j = 0 ∨ (M i j).natDegree + w i ≤ D + w j) :
    M.det.natDegree ≤ Fintype.card ι * D := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall Finset.univ _ _
  intro σ _hσ
  by_cases hzero : ∃ i, M (σ i) i = 0
  · obtain ⟨i, hi⟩ := hzero
    have hprod : ∏ i, M (σ i) i = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hi
    rw [hprod, smul_zero]
    simp
  · exact (natDegree_smul_le _ _).trans <|
      (natDegree_prod_le Finset.univ (fun i => M (σ i) i)).trans <| by
        have hnonzero (i : ι) : M (σ i) i ≠ 0 := by
          intro hi
          exact hzero ⟨i, hi⟩
        have hsum := Finset.sum_le_sum
          (fun i (_hi : i ∈ (Finset.univ : Finset ι)) =>
            (hentry (σ i) i).resolve_left (hnonzero i))
        simp only [Finset.sum_add_distrib] at hsum
        rw [Equiv.sum_comp σ w] at hsum
        have hcard : ∑ _i : ι, D = Fintype.card ι * D := by
          simp [Nat.mul_comm]
        rw [hcard] at hsum
        omega

end OnLeConjecture.DThree.ECNineDegree

namespace OnLeConjecture.DThree

open _root_.Polynomial Module

theorem eCNineUnitDegree_first_radicand_natDegree_le :
    eCNineUnitFirstRadicand.natDegree ≤ 3 := by
  rw [eCNineUnitFirstRadicand]
  compute_degree

theorem eCNineUnitDegree_second_radicand_natDegree_le :
    eCNineUnitSecondRadicand.natDegree ≤ 3 := by
  rw [eCNineUnitSecondRadicand]
  compute_degree

theorem eCNineUnitDegree_basis_apply (i j : Fin 3) :
    eCNineUnitBasis (i, j) =
      eCNineUnitT ^ (i : ℕ) * eCNineUnitCapitalT ^ (j : ℕ) := by
  rw [eCNineUnitBasis_apply, Algebra.smul_def]
  simp [eCNineUnitT, eCNineUnitCapitalT, map_pow]

theorem eCNineUnitDegree_t_mul_basis_zero (j : Fin 3) :
    eCNineUnitT * eCNineUnitBasis (0, j) =
      eCNineUnitBasis (1, j) := by
  simp [eCNineUnitDegree_basis_apply]

theorem eCNineUnitDegree_t_mul_basis_one (j : Fin 3) :
    eCNineUnitT * eCNineUnitBasis (1, j) =
      eCNineUnitBasis (2, j) := by
  simp [eCNineUnitDegree_basis_apply, pow_two]
  ring

theorem eCNineUnitDegree_t_mul_basis_two (j : Fin 3) :
    eCNineUnitT * eCNineUnitBasis (2, j) =
      eCNineUnitFirstRadicand • eCNineUnitBasis (0, j) := by
  rw [eCNineUnitDegree_basis_apply, eCNineUnitDegree_basis_apply]
  rw [Algebra.smul_def]
  have htwo : ((2 : Fin 3) : ℕ) = 2 := rfl
  have hzero : ((0 : Fin 3) : ℕ) = 0 := rfl
  rw [htwo, hzero, pow_zero, one_mul]
  calc
    eCNineUnitT * (eCNineUnitT ^ 2 * eCNineUnitCapitalT ^ (j : ℕ)) =
        eCNineUnitT ^ 3 * eCNineUnitCapitalT ^ (j : ℕ) := by ring
    _ = algebraMap ECNineUnitBase ECNineUnitAlgebra
        eCNineUnitFirstRadicand * eCNineUnitCapitalT ^ (j : ℕ) := by
      rw [eCNineUnitT_cube]

theorem eCNineUnitDegree_T_mul_basis_zero (i : Fin 3) :
    eCNineUnitCapitalT * eCNineUnitBasis (i, 0) =
      eCNineUnitBasis (i, 1) := by
  simp [eCNineUnitDegree_basis_apply]
  ring

theorem eCNineUnitDegree_T_mul_basis_one (i : Fin 3) :
    eCNineUnitCapitalT * eCNineUnitBasis (i, 1) =
      eCNineUnitBasis (i, 2) := by
  simp [eCNineUnitDegree_basis_apply, pow_two]
  ring

theorem eCNineUnitDegree_T_mul_basis_two (i : Fin 3) :
    eCNineUnitCapitalT * eCNineUnitBasis (i, 2) =
      eCNineUnitSecondRadicand • eCNineUnitBasis (i, 0) := by
  rw [eCNineUnitDegree_basis_apply, eCNineUnitDegree_basis_apply, Algebra.smul_def]
  have htwo : ((2 : Fin 3) : ℕ) = 2 := rfl
  have hzero : ((0 : Fin 3) : ℕ) = 0 := rfl
  rw [htwo, hzero, pow_zero]
  calc
    eCNineUnitCapitalT *
        (eCNineUnitT ^ (i : ℕ) * eCNineUnitCapitalT ^ 2) =
        eCNineUnitCapitalT ^ 3 * eCNineUnitT ^ (i : ℕ) := by ring
    _ = algebraMap ECNineUnitBase ECNineUnitAlgebra
        eCNineUnitSecondRadicand * eCNineUnitT ^ (i : ℕ) := by
      rw [eCNineUnitCapitalT_cube]
    _ = algebraMap ECNineUnitBase ECNineUnitAlgebra
        eCNineUnitSecondRadicand *
          (eCNineUnitT ^ (i : ℕ) * 1) := by rw [mul_one]

/-- The total degree assigned to a power basis element. -/
def eCNineUnitBasisWeight (ij : Fin 3 × Fin 3) : ℕ := (ij.1 : ℕ) + (ij.2 : ℕ)

/-- A finite filtration on the C9 unit chart algebra. -/
def ECNineUnitFiltered (D : ℕ) (z : ECNineUnitAlgebra) : Prop :=
  ∃ c : Fin 3 × Fin 3 → ECNineUnitBase,
    z = ∑ ij, c ij • eCNineUnitBasis ij ∧
    ∀ ij, c ij = 0 ∨ (c ij).natDegree + eCNineUnitBasisWeight ij ≤ D

theorem eCNineUnitDegree_filtered_zero (D : ℕ) : ECNineUnitFiltered D 0 := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp
  · intro ij
    exact Or.inl rfl

theorem eCNineUnitDegree_filtered_mono {D E : ℕ} {z : ECNineUnitAlgebra}
    (h : ECNineUnitFiltered D z) (hDE : D ≤ E) : ECNineUnitFiltered E z := by
  obtain ⟨c, hc, hdegree⟩ := h
  exact ⟨c, hc, fun ij => (hdegree ij).imp_right (fun h => h.trans hDE)⟩

theorem eCNineUnitDegree_filtered_add {D : ℕ} {z w : ECNineUnitAlgebra}
    (hz : ECNineUnitFiltered D z) (hw : ECNineUnitFiltered D w) :
    ECNineUnitFiltered D (z + w) := by
  obtain ⟨c, hc, hcdegree⟩ := hz
  obtain ⟨d, hd, hddegree⟩ := hw
  refine ⟨fun ij => c ij + d ij, ?_, ?_⟩
  · rw [hc, hd, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ij _hij
    rw [add_smul]
  · intro ij
    by_cases hsum : c ij + d ij = 0
    · exact Or.inl hsum
    · right
      change (c ij + d ij).natDegree + eCNineUnitBasisWeight ij ≤ D
      rcases hcdegree ij with hczero | hcdegree
      · rw [hczero, zero_add]
        exact (hddegree ij).resolve_left (fun hdzero => hsum (by
          simp [hczero, hdzero]))
      · rcases hddegree ij with hdzero | hddegree
        · rw [hdzero, add_zero]
          exact hcdegree
        · calc
            (c ij + d ij).natDegree + eCNineUnitBasisWeight ij ≤
                max (c ij).natDegree (d ij).natDegree + eCNineUnitBasisWeight ij :=
              Nat.add_le_add_right (Polynomial.natDegree_add_le _ _) _
            _ = max ((c ij).natDegree + eCNineUnitBasisWeight ij)
                ((d ij).natDegree + eCNineUnitBasisWeight ij) := by omega
            _ ≤ D := max_le hcdegree hddegree

theorem eCNineUnitDegree_filtered_smul_basis {D : ℕ}
    (q : ECNineUnitBase) (ij : Fin 3 × Fin 3)
    (hq : q = 0 ∨ q.natDegree + eCNineUnitBasisWeight ij ≤ D) :
    ECNineUnitFiltered D (q • eCNineUnitBasis ij) := by
  classical
  refine ⟨fun kl => if kl = ij then q else 0, ?_, ?_⟩
  · rw [Finset.sum_eq_single ij]
    · simp
    · intro kl _hkl hne
      simp [hne]
    · simp
  · intro kl
    by_cases hkl : kl = ij
    · subst kl
      simpa using hq
    · left
      simp [hkl]

theorem eCNineUnitDegree_filtered_sum {D : ℕ}
    {S : Type} [Fintype S] (f : S → ECNineUnitAlgebra)
    (hf : ∀ s, ECNineUnitFiltered D (f s)) :
    ECNineUnitFiltered D (∑ s, f s) := by
  classical
  induction (Finset.univ : Finset S) using Finset.induction_on with
  | empty => simpa using eCNineUnitDegree_filtered_zero D
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact eCNineUnitDegree_filtered_add (hf a) ih

theorem eCNineUnitDegree_filtered_base_smul {D : ℕ} {z : ECNineUnitAlgebra}
    (q : ECNineUnitBase) (hz : ECNineUnitFiltered D z) :
    ECNineUnitFiltered (q.natDegree + D) (q • z) := by
  obtain ⟨c, hc, hcdegree⟩ := hz
  refine ⟨fun ij => q * c ij, ?_, ?_⟩
  · rw [hc, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro ij _hij
    rw [mul_smul]
  · intro ij
    by_cases hzero : q * c ij = 0
    · exact Or.inl hzero
    · right
      have hcne : c ij ≠ 0 := fun hc0 => hzero (by rw [hc0, mul_zero])
      have hcdegree' := (hcdegree ij).resolve_left hcne
      calc
        (q * c ij).natDegree + eCNineUnitBasisWeight ij ≤
            (q.natDegree + (c ij).natDegree) + eCNineUnitBasisWeight ij :=
          Nat.add_le_add_right Polynomial.natDegree_mul_le _
        _ ≤ q.natDegree + D := by omega

theorem eCNineUnitDegree_filtered_t_mul_smul_basis {D : ℕ}
    (q : ECNineUnitBase) (i j : Fin 3)
    (hq : q = 0 ∨ q.natDegree + eCNineUnitBasisWeight (i, j) ≤ D) :
    ECNineUnitFiltered (D + 1)
      (eCNineUnitT * (q • eCNineUnitBasis (i, j))) := by
  rw [Algebra.mul_smul_comm]
  fin_cases i
  · change ECNineUnitFiltered (D + 1)
      (q • (eCNineUnitT * eCNineUnitBasis (0, j)))
    rw [eCNineUnitDegree_t_mul_basis_zero]
    apply eCNineUnitDegree_filtered_smul_basis q (1, j)
    rcases hq with rfl | hq
    · exact Or.inl rfl
    · right
      simp only [eCNineUnitBasisWeight] at hq ⊢
      omega
  · change ECNineUnitFiltered (D + 1)
      (q • (eCNineUnitT * eCNineUnitBasis (1, j)))
    rw [eCNineUnitDegree_t_mul_basis_one]
    apply eCNineUnitDegree_filtered_smul_basis q (2, j)
    rcases hq with rfl | hq
    · exact Or.inl rfl
    · right
      simp only [eCNineUnitBasisWeight] at hq ⊢
      omega
  · change ECNineUnitFiltered (D + 1)
      (q • (eCNineUnitT * eCNineUnitBasis (2, j)))
    rw [eCNineUnitDegree_t_mul_basis_two, smul_smul]
    apply eCNineUnitDegree_filtered_smul_basis
      (q * eCNineUnitFirstRadicand) (0, j)
    by_cases hzero : q * eCNineUnitFirstRadicand = 0
    · exact Or.inl hzero
    · right
      have hqne : q ≠ 0 := fun h => hzero (by rw [h, zero_mul])
      have hqdegree := hq.resolve_left hqne
      calc
        (q * eCNineUnitFirstRadicand).natDegree + eCNineUnitBasisWeight (0, j) ≤
            (q.natDegree + eCNineUnitFirstRadicand.natDegree) +
              eCNineUnitBasisWeight (0, j) :=
          Nat.add_le_add_right Polynomial.natDegree_mul_le _
        _ ≤ D + 1 := by
          have := eCNineUnitDegree_first_radicand_natDegree_le
          simp only [eCNineUnitBasisWeight] at hqdegree ⊢
          omega

theorem eCNineUnitDegree_filtered_T_mul_smul_basis {D : ℕ}
    (q : ECNineUnitBase) (i j : Fin 3)
    (hq : q = 0 ∨ q.natDegree + eCNineUnitBasisWeight (i, j) ≤ D) :
    ECNineUnitFiltered (D + 1)
      (eCNineUnitCapitalT * (q • eCNineUnitBasis (i, j))) := by
  rw [Algebra.mul_smul_comm]
  fin_cases j
  · change ECNineUnitFiltered (D + 1)
      (q • (eCNineUnitCapitalT * eCNineUnitBasis (i, 0)))
    rw [eCNineUnitDegree_T_mul_basis_zero]
    apply eCNineUnitDegree_filtered_smul_basis q (i, 1)
    rcases hq with rfl | hq
    · exact Or.inl rfl
    · right
      simp only [eCNineUnitBasisWeight] at hq ⊢
      omega
  · change ECNineUnitFiltered (D + 1)
      (q • (eCNineUnitCapitalT * eCNineUnitBasis (i, 1)))
    rw [eCNineUnitDegree_T_mul_basis_one]
    apply eCNineUnitDegree_filtered_smul_basis q (i, 2)
    rcases hq with rfl | hq
    · exact Or.inl rfl
    · right
      simp only [eCNineUnitBasisWeight] at hq ⊢
      omega
  · change ECNineUnitFiltered (D + 1)
      (q • (eCNineUnitCapitalT * eCNineUnitBasis (i, 2)))
    rw [eCNineUnitDegree_T_mul_basis_two, smul_smul]
    apply eCNineUnitDegree_filtered_smul_basis
      (q * eCNineUnitSecondRadicand) (i, 0)
    by_cases hzero : q * eCNineUnitSecondRadicand = 0
    · exact Or.inl hzero
    · right
      have hqne : q ≠ 0 := fun h => hzero (by rw [h, zero_mul])
      have hqdegree := hq.resolve_left hqne
      calc
        (q * eCNineUnitSecondRadicand).natDegree + eCNineUnitBasisWeight (i, 0) ≤
            (q.natDegree + eCNineUnitSecondRadicand.natDegree) +
              eCNineUnitBasisWeight (i, 0) :=
          Nat.add_le_add_right Polynomial.natDegree_mul_le _
        _ ≤ D + 1 := by
          have := eCNineUnitDegree_second_radicand_natDegree_le
          simp only [eCNineUnitBasisWeight] at hqdegree ⊢
          omega

theorem eCNineUnitDegree_filtered_t_mul {D : ℕ} {z : ECNineUnitAlgebra}
    (hz : ECNineUnitFiltered D z) :
    ECNineUnitFiltered (D + 1) (eCNineUnitT * z) := by
  obtain ⟨c, hc, hcdegree⟩ := hz
  rw [hc, Finset.mul_sum]
  exact eCNineUnitDegree_filtered_sum _ fun ij =>
    eCNineUnitDegree_filtered_t_mul_smul_basis (c ij) ij.1 ij.2 (hcdegree ij)

theorem eCNineUnitDegree_filtered_T_mul {D : ℕ} {z : ECNineUnitAlgebra}
    (hz : ECNineUnitFiltered D z) :
    ECNineUnitFiltered (D + 1) (eCNineUnitCapitalT * z) := by
  obtain ⟨c, hc, hcdegree⟩ := hz
  rw [hc, Finset.mul_sum]
  exact eCNineUnitDegree_filtered_sum _ fun ij =>
    eCNineUnitDegree_filtered_T_mul_smul_basis (c ij) ij.1 ij.2 (hcdegree ij)

theorem eCNineUnitDegree_filtered_t_pow_mul {D n : ℕ} {z : ECNineUnitAlgebra}
    (hz : ECNineUnitFiltered D z) :
    ECNineUnitFiltered (D + n) (eCNineUnitT ^ n * z) := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
      rw [pow_succ', mul_assoc]
      have h := eCNineUnitDegree_filtered_t_mul ih
      exact eCNineUnitDegree_filtered_mono h (by omega)

theorem eCNineUnitDegree_filtered_T_pow_mul {D n : ℕ} {z : ECNineUnitAlgebra}
    (hz : ECNineUnitFiltered D z) :
    ECNineUnitFiltered (D + n) (eCNineUnitCapitalT ^ n * z) := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
      rw [pow_succ', mul_assoc]
      have h := eCNineUnitDegree_filtered_T_mul ih
      exact eCNineUnitDegree_filtered_mono h (by omega)

theorem eCNineUnitDegree_filtered_mul {D E : ℕ} {z w : ECNineUnitAlgebra}
    (hz : ECNineUnitFiltered D z) (hw : ECNineUnitFiltered E w) :
    ECNineUnitFiltered (D + E) (z * w) := by
  obtain ⟨c, hc, hcdegree⟩ := hz
  rw [hc, Finset.sum_mul]
  apply eCNineUnitDegree_filtered_sum
  intro ij
  rcases hcdegree ij with hcZero | hcdegree
  · rw [hcZero, zero_smul, zero_mul]
    exact eCNineUnitDegree_filtered_zero (D + E)
  · rw [Algebra.smul_mul_assoc, eCNineUnitDegree_basis_apply]
    have hT : ECNineUnitFiltered (E + (ij.2 : ℕ))
        (eCNineUnitCapitalT ^ (ij.2 : ℕ) * w) :=
      eCNineUnitDegree_filtered_T_pow_mul hw
    have ht : ECNineUnitFiltered ((E + (ij.2 : ℕ)) + (ij.1 : ℕ))
        (eCNineUnitT ^ (ij.1 : ℕ) *
          (eCNineUnitCapitalT ^ (ij.2 : ℕ) * w)) :=
      eCNineUnitDegree_filtered_t_pow_mul hT
    have hscalar := eCNineUnitDegree_filtered_base_smul (c ij) ht
    have heq :
        c ij • ((eCNineUnitT ^ (ij.1 : ℕ) *
          eCNineUnitCapitalT ^ (ij.2 : ℕ)) * w) =
        c ij • (eCNineUnitT ^ (ij.1 : ℕ) *
          (eCNineUnitCapitalT ^ (ij.2 : ℕ) * w)) := by
      rw [mul_assoc]
    rw [heq]
    apply eCNineUnitDegree_filtered_mono hscalar
    simp only [eCNineUnitBasisWeight] at hcdegree
    omega

theorem eCNineUnitDegree_filtered_one : ECNineUnitFiltered 0 (1 : ECNineUnitAlgebra) := by
  have h := eCNineUnitDegree_filtered_smul_basis (D := 0)
    (1 : ECNineUnitBase) (0, 0)
    (Or.inr (by simp [eCNineUnitBasisWeight]))
  simpa [eCNineUnitDegree_basis_apply] using h

theorem eCNineUnitDegree_filtered_neg {D : ℕ} {z : ECNineUnitAlgebra}
    (hz : ECNineUnitFiltered D z) : ECNineUnitFiltered D (-z) := by
  have h := eCNineUnitDegree_filtered_base_smul (-1 : ECNineUnitBase) hz
  simpa using h

theorem eCNineUnitDegree_filtered_sub {D : ℕ} {z w : ECNineUnitAlgebra}
    (hz : ECNineUnitFiltered D z) (hw : ECNineUnitFiltered D w) :
    ECNineUnitFiltered D (z - w) := by
  rw [sub_eq_add_neg]
  exact eCNineUnitDegree_filtered_add hz (eCNineUnitDegree_filtered_neg hw)

theorem eCNineUnitDegree_filtered_pow {D n : ℕ} {z : ECNineUnitAlgebra}
    (hz : ECNineUnitFiltered D z) : ECNineUnitFiltered (n * D) (z ^ n) := by
  induction n with
  | zero => simpa using eCNineUnitDegree_filtered_one
  | succ n ih =>
      rw [pow_succ]
      have h := eCNineUnitDegree_filtered_mul ih hz
      simpa [Nat.succ_mul] using h

theorem eCNineUnitDegree_filtered_complex_algebraMap (c : ℂ) :
    ECNineUnitFiltered 0 (algebraMap ℂ ECNineUnitAlgebra c) := by
  have h := eCNineUnitDegree_filtered_base_smul (C c) eCNineUnitDegree_filtered_one
  simpa [Algebra.smul_def, eCNineUnit_algebraMap_C] using h

theorem eCNineUnitDegree_filtered_capitalX : ECNineUnitFiltered 1 eCNineUnitCapitalX := by
  have h := eCNineUnitDegree_filtered_base_smul X eCNineUnitDegree_filtered_one
  simpa [eCNineUnitCapitalX, Algebra.smul_def] using h

theorem eCNineUnitDegree_filtered_t : ECNineUnitFiltered 1 eCNineUnitT := by
  have h := eCNineUnitDegree_filtered_smul_basis (D := 1)
    (1 : ECNineUnitBase) (1, 0)
    (Or.inr (by simp [eCNineUnitBasisWeight]))
  simpa [eCNineUnitDegree_basis_apply] using h

theorem eCNineUnitDegree_filtered_capitalT : ECNineUnitFiltered 1 eCNineUnitCapitalT := by
  have h := eCNineUnitDegree_filtered_smul_basis (D := 1)
    (1 : ECNineUnitBase) (0, 1)
    (Or.inr (by simp [eCNineUnitBasisWeight]))
  simpa [eCNineUnitDegree_basis_apply] using h

theorem eCNineUnitDegree_finsupp_prod_fin_two
    (d : Fin 2 →₀ ℕ) (a b : ECNineUnitAlgebra) :
    d.prod (fun i e => ![a, b] i ^ e) = a ^ d 0 * b ^ d 1 := by
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two]
  · intro i
    simp

theorem eCNineUnitDegree_filtered_eval₂_of_isHomogeneous
    (a b : ECNineUnitAlgebra)
    (ha : ECNineUnitFiltered 1 a) (hb : ECNineUnitFiltered 1 b)
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    ECNineUnitFiltered N
      (MvPolynomial.eval₂ (algebraMap ℂ ECNineUnitAlgebra) ![a, b] R) := by
  induction hR using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      simpa using eCNineUnitDegree_filtered_zero N
  | add p q hp hq ihp ihq =>
      rw [MvPolynomial.eval₂_add]
      exact eCNineUnitDegree_filtered_add ihp ihq
  | monomial d r hr =>
      rw [MvPolynomial.eval₂_monomial, eCNineUnitDegree_finsupp_prod_fin_two]
      have haPow : ECNineUnitFiltered (d 0)
          (a ^ d 0) := by
        simpa using eCNineUnitDegree_filtered_pow (n := d 0) ha
      have hbPow : ECNineUnitFiltered (d 1)
          (b ^ d 1) := by
        simpa using eCNineUnitDegree_filtered_pow (n := d 1) hb
      have hproduct := eCNineUnitDegree_filtered_mul haPow hbPow
      have hcoefficient := eCNineUnitDegree_filtered_complex_algebraMap r
      have hfull := eCNineUnitDegree_filtered_mul hcoefficient hproduct
      have hdegree : d 0 + d 1 = N := by
        have hsum : d.sum (fun _ e => e) = N := by
          simpa [Finsupp.weight_apply] using hr
        rw [Finsupp.sum_fintype] at hsum
        · simpa [Fin.sum_univ_two] using hsum
        · intro i
          rfl
      simpa [hdegree] using hfull

theorem eCNineUnitDifferenceElement_filtered
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    ECNineUnitFiltered N (eCNineUnitDifferenceElement R) := by
  rw [eCNineUnitDifferenceElement]
  have hone : ECNineUnitFiltered 1 (1 : ECNineUnitAlgebra) :=
    eCNineUnitDegree_filtered_mono eCNineUnitDegree_filtered_one (by omega)
  have hleft := eCNineUnitDegree_filtered_eval₂_of_isHomogeneous
    (1 : ECNineUnitAlgebra) eCNineUnitT hone eCNineUnitDegree_filtered_t hR
  have hright := eCNineUnitDegree_filtered_eval₂_of_isHomogeneous
    eCNineUnitCapitalX eCNineUnitCapitalT eCNineUnitDegree_filtered_capitalX
      eCNineUnitDegree_filtered_capitalT hR
  exact eCNineUnitDegree_filtered_sub hleft hright

theorem eCNineUnitDegree_filtered_repr_bound {D : ℕ} {z : ECNineUnitAlgebra}
    (hz : ECNineUnitFiltered D z) (ij : Fin 3 × Fin 3) :
    eCNineUnitBasis.repr z ij = 0 ∨
      (eCNineUnitBasis.repr z ij).natDegree + eCNineUnitBasisWeight ij ≤ D := by
  obtain ⟨c, hc, hcdegree⟩ := hz
  have hcoordinate' : eCNineUnitBasis.repr z ij = c ij := by
    rw [hc, map_sum]
    simp only [map_smul, Basis.repr_self, Finsupp.smul_single,
      Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_mul, mul_one]
    rw [Finset.sum_eq_single ij]
    · simp
    · intro kl _hkl hne
      rw [Finsupp.single_eq_of_ne (Ne.symm hne)]
    · simp
  rw [hcoordinate']
  exact hcdegree ij

theorem eCNineUnitLeftMulMatrix_entry_bound
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (row column : Fin 3 × Fin 3) :
    (Algebra.leftMulMatrix eCNineUnitBasis
        (eCNineUnitDifferenceElement R)) row column = 0 ∨
      ((Algebra.leftMulMatrix eCNineUnitBasis
        (eCNineUnitDifferenceElement R)) row column).natDegree +
          eCNineUnitBasisWeight row ≤ N + eCNineUnitBasisWeight column := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
  change eCNineUnitBasis.repr
      (eCNineUnitDifferenceElement R * eCNineUnitBasis column) row = 0 ∨ _
  have hsection := eCNineUnitDifferenceElement_filtered hR
  have hbasis : ECNineUnitFiltered (eCNineUnitBasisWeight column)
      (eCNineUnitBasis column) := by
    simpa using eCNineUnitDegree_filtered_smul_basis (D := eCNineUnitBasisWeight column)
      (1 : ECNineUnitBase) column (Or.inr (by simp))
  exact eCNineUnitDegree_filtered_repr_bound (eCNineUnitDegree_filtered_mul hsection hbasis) row

theorem eCNineUnitDifferenceNorm_natDegree_le
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    (eCNineUnitDifferenceNorm R).natDegree ≤ 9 * N := by
  rw [eCNineUnitDifferenceNorm_eq_matrix_det]
  have h := ECNineDegree.natDegree_det_le_of_weighted_entries
    (Algebra.leftMulMatrix eCNineUnitBasis
      (eCNineUnitDifferenceElement R)) eCNineUnitBasisWeight N
      (eCNineUnitLeftMulMatrix_entry_bound hR)
  norm_num at h ⊢
  exact h

end OnLeConjecture.DThree
