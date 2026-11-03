/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrderTwoPreparation
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Convergence of cubic residue decompositions

This file regroups the Taylor monomials of a plane analytic germ according
to the exponent of the first coordinate modulo three. The resulting three
series converge and express the germ as

`A(x³,y) + x B(x³,y) + x² C(x³,y)`.

It follows that analytic division by `x³ + h(y)` has an analytic quotient
and a remainder of degree at most two in `x`.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped BigOperators NNReal ENNReal Topology

namespace Germ

/-- The analytic map `(x,y) ↦ (x³,y)`. -/
@[expose] noncomputable def cubicMap (z : Source 2) : Source 2 :=
  fun i ↦ Fin.cases (z 0 ^ 3) (fun j ↦ z j.succ) i

@[simp]
theorem cubicMap_apply_zero (z : Source 2) :
    Germ.cubicMap z 0 = z 0 ^ 3 := by
  simp [Germ.cubicMap]

@[simp]
theorem cubicMap_apply_one (z : Source 2) :
    Germ.cubicMap z 1 = z 1 := by
  change Fin.cases (z 0 ^ 3) (fun j : Fin 1 ↦ z j.succ) 1 = z 1
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide]
  rfl

theorem cubicMap_analyticAt : AnalyticAt ℂ Germ.cubicMap 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact
      ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0).pow 3
  · exact
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0

@[simp]
theorem cubicMap_zero : Germ.cubicMap (0 : Source 2) = 0 := by
  ext i
  fin_cases i <;> simp

/-- The pointed analytic germ represented by `(x,y) ↦ (x³,y)`. -/
@[expose] noncomputable def cubicMapGerm : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction Germ.cubicMap Germ.cubicMap_analyticAt
    Germ.cubicMap_zero

/-- Substitution `(u,y) = (x³,y)` on plane analytic germs. -/
@[expose] noncomputable def cubicSubstitutionAlgHom :
    Germ 2 →ₐ[ℂ] Germ 2 where
  __ := Germ.cubicMapGerm.pullbackRingHom
  commutes' c := Germ.cubicMapGerm.pullback_constRingHom c

@[simp]
theorem cubicSubstitutionAlgHom_coordinate_zero :
    Germ.cubicSubstitutionAlgHom (Germ.coordinate (0 : Fin 2)) =
      Germ.coordinate (0 : Fin 2) ^ 3 := by
  change Germ.cubicMapGerm.pullbackRingHom
    (Germ.coordinate (0 : Fin 2)) = _
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rfl

@[simp]
theorem cubicSubstitutionAlgHom_coordinate_one :
    Germ.cubicSubstitutionAlgHom (Germ.coordinate (1 : Fin 2)) =
      Germ.coordinate (1 : Fin 2) := by
  change Germ.cubicMapGerm.pullbackRingHom
    (Germ.coordinate (1 : Fin 2)) = _
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rfl

/-- Cubic substitution fixes germs extended from the parameter
hyperplane. -/
theorem cubicSubstitution_hyperplaneExtension (r : Germ 1) :
    Germ.cubicSubstitutionAlgHom (Germ.hyperplaneExtension 1 r) =
      Germ.hyperplaneExtension 1 r := by
  rcases r with ⟨r, hr⟩
  induction r using Filter.Germ.inductionOn with
  | _ r =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hr
      change Germ.cubicSubstitutionAlgHom
          (Germ.hyperplaneExtension 1 (Germ.ofFunction r hr)) =
        Germ.hyperplaneExtension 1 (Germ.ofFunction r hr)
      rw [Germ.hyperplaneExtension_ofFunction]
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z ↦ by
        change r (Germ.hyperplaneTail 1 (Germ.cubicMap z)) =
          r (Germ.hyperplaneTail 1 z)
        congr 1

/-- The homogeneous series collecting first coordinate exponents congruent
to `r` modulo three after replacing `x³` by a new coordinate. -/
@[expose] noncomputable def cubicResidueCompressedSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (r : Fin 3) :
    FormalMultilinearSeries ℂ (Source 2) ℂ :=
  fun k ↦ ∑ m : Fin (k + 1),
    Germ.mixedCoefficient p (k + 2 * m.1 + r.1) (3 * m.1 + r.1) •
      Germ.compressedMonomial k m

/-- Evaluation of a cubic residue coefficient on the diagonal. -/
theorem cubicResidueCompressedSeries_apply_diagonal
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (r : Fin 3) (k : ℕ) (u y : ℂ) :
    Germ.cubicResidueCompressedSeries p r k
        (fun _ : Fin k ↦ Germ.planePoint u y) =
      ∑ m : Fin (k + 1),
        Germ.mixedCoefficient p (k + 2 * m.1 + r.1)
            (3 * m.1 + r.1) *
          (u ^ m.1 * y ^ (k - m.1)) := by
  simp only [Germ.cubicResidueCompressedSeries, sum_apply, smul_apply,
    Germ.compressedMonomial_apply_diagonal, smul_eq_mul]

/-- Operator norm estimate for one cubic residue coefficient. -/
theorem norm_cubicResidueCompressedSeries_le_sum
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (r : Fin 3) (k : ℕ) :
    ‖Germ.cubicResidueCompressedSeries p r k‖ ≤
      ∑ m : Fin (k + 1),
        (2 : ℝ) ^ (k + 2 * m.1 + r.1) *
          ‖p (k + 2 * m.1 + r.1)‖ := by
  calc
    ‖Germ.cubicResidueCompressedSeries p r k‖ ≤
        ∑ m : Fin (k + 1),
          ‖Germ.mixedCoefficient p (k + 2 * m.1 + r.1)
              (3 * m.1 + r.1) •
            Germ.compressedMonomial k m‖ := norm_sum_le _ _
    _ ≤ ∑ m : Fin (k + 1),
        (2 : ℝ) ^ (k + 2 * m.1 + r.1) *
          ‖p (k + 2 * m.1 + r.1)‖ := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        ‖Germ.mixedCoefficient p (k + 2 * m.1 + r.1)
              (3 * m.1 + r.1) •
            Germ.compressedMonomial k m‖ =
            ‖Germ.mixedCoefficient p (k + 2 * m.1 + r.1)
              (3 * m.1 + r.1)‖ *
              ‖Germ.compressedMonomial k m‖ := by rw [norm_smul]
        _ ≤ ‖Germ.mixedCoefficient p (k + 2 * m.1 + r.1)
              (3 * m.1 + r.1)‖ * 1 := by
          gcongr
          exact Germ.norm_compressedMonomial_le_one k m
        _ ≤ (2 : ℝ) ^ (k + 2 * m.1 + r.1) *
              ‖p (k + 2 * m.1 + r.1)‖ := by
          simpa using Germ.norm_mixedCoefficient_le_pow_two p
            (k + 2 * m.1 + r.1) (3 * m.1 + r.1)

/-- Each cubic residue compression of a convergent plane series has positive
radius of convergence. -/
theorem cubicResidueCompressedSeries_radius_pos
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hp : 0 < p.radius) (r : Fin 3) :
    0 < (Germ.cubicResidueCompressedSeries p r).radius := by
  obtain ⟨C, ρ, hC, hρ, hpBound⟩ := p.le_mul_pow_of_radius_pos hp
  let A : ℝ := max 1 (2 * ρ)
  let B : ℝ := 2 * A ^ 3
  let D : ℝ := 2 * C * A ^ r.1
  have hAOne : 1 ≤ A := le_max_left _ _
  have hANonneg : 0 ≤ A := zero_le_one.trans hAOne
  have hB : 0 < B := by
    exact mul_pos zero_lt_two (pow_pos (zero_lt_one.trans_le hAOne) 3)
  have hD : 0 < D := by
    exact mul_pos (mul_pos zero_lt_two hC) (pow_pos
      (zero_lt_one.trans_le hAOne) r.1)
  apply Germ.radius_pos_of_norm_le_mul_pow
    (Germ.cubicResidueCompressedSeries p r) hD hB
  intro k
  refine (Germ.norm_cubicResidueCompressedSeries_le_sum p r k).trans ?_
  calc
    (∑ m : Fin (k + 1),
        (2 : ℝ) ^ (k + 2 * m.1 + r.1) *
          ‖p (k + 2 * m.1 + r.1)‖) ≤
        ∑ _m : Fin (k + 1), C * A ^ (3 * k + r.1) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmle : m.1 ≤ k := Nat.lt_succ_iff.mp m.2
      have hdegree : k + 2 * m.1 + r.1 ≤ 3 * k + r.1 := by omega
      calc
        (2 : ℝ) ^ (k + 2 * m.1 + r.1) *
              ‖p (k + 2 * m.1 + r.1)‖ ≤
            (2 : ℝ) ^ (k + 2 * m.1 + r.1) *
              (C * ρ ^ (k + 2 * m.1 + r.1)) := by
          gcongr
          exact hpBound (k + 2 * m.1 + r.1)
        _ = C * (2 * ρ) ^ (k + 2 * m.1 + r.1) := by
          rw [mul_pow]
          ring
        _ ≤ C * A ^ (k + 2 * m.1 + r.1) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg zero_le_two hρ.le)
              (le_max_right _ _) _) hC.le
        _ ≤ C * A ^ (3 * k + r.1) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hAOne hdegree) hC.le
    _ = ((k + 1 : ℕ) : ℝ) * (C * A ^ (3 * k + r.1)) := by simp
    _ ≤ (2 : ℝ) ^ (k + 1) * (C * A ^ (3 * k + r.1)) := by
      gcongr
      exact_mod_cast Nat.le_of_lt (k + 1).lt_two_pow_self
    _ = D * B ^ k := by
      simp only [D, B]
      rw [pow_add, pow_one, pow_add, pow_mul]
      ring

/-- A term in a cubic residue class before regrouping by compressed total
degree. -/
@[expose] noncomputable def cubicResidueTerm
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (r : Fin 3) (m j : ℕ) (x y : ℂ) : ℂ :=
  Germ.mixedCoefficient p (3 * m + r.1 + j) (3 * m + r.1) *
    x ^ (3 * m + r.1) * y ^ j

/-- The double series in one cubic residue class is absolutely summable on
a sufficiently small coordinate polydisc. -/
theorem summable_cubicResidueTerm_of_geometric_bound
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (r : Fin 3) {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ)
    (hp : ∀ d, ‖p d‖ ≤ C * ρ ^ d)
    {x y : ℂ} (hx : 2 * ρ * ‖x‖ < 1)
    (hy : 2 * ρ * ‖y‖ < 1) :
    Summable (fun z : ℕ × ℕ ↦
      Germ.cubicResidueTerm p r z.1 z.2 x y) := by
  have hall := Germ.summable_mixedTerm_of_geometric_bound
    p hC hρ hp hx hy
  have hinjective : Function.Injective
      (fun z : ℕ × ℕ ↦ (3 * z.1 + r.1, z.2)) := by
    rintro ⟨m, j⟩ ⟨m', j'⟩ hzw
    simp only [Prod.mk.injEq] at hzw ⊢
    constructor
    · omega
    · exact hzw.2
  have hresidue := hall.comp_injective hinjective
  refine hresidue.congr (fun z ↦ ?_)
  rfl

/-- Regrouping one cubic residue class by compressed total degree gives the
sum of its compressed formal multilinear series. -/
theorem cubicResidueCompressedSeries_sum_eq_tsum
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (r : Fin 3)
    {x y : ℂ}
    (hsum : Summable (fun z : ℕ × ℕ ↦
      Germ.cubicResidueTerm p r z.1 z.2 x y)) :
    x ^ r.1 * (Germ.cubicResidueCompressedSeries p r).sum
        (Germ.planePoint (x ^ 3) y) =
      ∑' z : ℕ × ℕ, Germ.cubicResidueTerm p r z.1 z.2 x y := by
  have hgrouped := tsum_weightedAntidiagonal 1 zero_lt_one
    (fun m j ↦ Germ.cubicResidueTerm p r m j x y) hsum
  rw [FormalMultilinearSeries.sum, ← hgrouped, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [Germ.cubicResidueCompressedSeries_apply_diagonal]
  rw [Finset.mul_sum]
  let e : Fin (k + 1) ≃ Fin (k / 1 + 1) :=
    (Fin.castOrderIso (by omega)).toEquiv
  apply Fintype.sum_equiv e
  intro m
  simp only [Germ.cubicResidueTerm, one_mul]
  have hem : (e m).1 = m.1 := rfl
  rw [hem]
  have hdegree : 3 * m.1 + r.1 + (k - m.1) =
      k + 2 * m.1 + r.1 := by omega
  rw [hdegree]
  rw [pow_add, pow_mul]
  ring

/-- The unrestricted coordinate double series is the sum of the original
formal multilinear series. -/
theorem formalSeries_sum_eq_tsum_mixedTerm
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {x y : ℂ}
    (hsum : Summable (fun z : ℕ × ℕ ↦
      Germ.mixedTerm p z.1 z.2 x y)) :
    p.sum (Germ.planePoint x y) =
      ∑' z : ℕ × ℕ, Germ.mixedTerm p z.1 z.2 x y := by
  have hgrouped := tsum_weightedAntidiagonal 1 zero_lt_one
    (fun i j ↦ Germ.mixedTerm p i j x y) hsum
  rw [FormalMultilinearSeries.sum, ← hgrouped]
  apply tsum_congr
  intro d
  rw [Germ.homogeneous_apply_planePoint_grouped]
  rw [← Fin.sum_univ_eq_sum_range
    (fun i ↦ x ^ i * y ^ (d - i) * Germ.mixedCoefficient p d i) (d + 1)]
  let e : Fin (d + 1) ≃ Fin (d / 1 + 1) :=
    (Fin.castOrderIso (by omega)).toEquiv
  apply Fintype.sum_equiv e
  intro i
  simp only [Germ.mixedTerm, one_mul]
  have hei : (e i).1 = i.1 := rfl
  rw [hei]
  have hdegree : i.1 + (d - i.1) = d := by omega
  rw [hdegree]
  ring

/-- Reindexing coordinate exponents by their residue modulo three. -/
@[expose] noncomputable def cubicResidueEquiv :
    Fin 3 × (ℕ × ℕ) ≃ ℕ × ℕ :=
  (Equiv.prodAssoc (Fin 3) ℕ ℕ).symm |>.trans
    (Equiv.prodCongr (Equiv.prodComm (Fin 3) ℕ) (Equiv.refl ℕ)) |>.trans
    (Equiv.prodCongr (Nat.divModEquiv 3).symm (Equiv.refl ℕ))

@[simp]
theorem cubicResidueEquiv_apply (r : Fin 3) (m j : ℕ) :
    Germ.cubicResidueEquiv (r, (m, j)) = (3 * m + r.1, j) := by
  simp only [Germ.cubicResidueEquiv, Equiv.trans_apply,
    Equiv.prodAssoc_symm_apply, Equiv.prodCongr_apply]
  change (m * 3 + r.1, j) = (3 * m + r.1, j)
  rw [Nat.mul_comm m 3]

/-- The unrestricted coordinate double series is the sum of its three
residue classes in the first coordinate exponent. -/
theorem tsum_mixedTerm_eq_sum_cubicResidueTerm
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {x y : ℂ}
    (hsum : Summable (fun z : ℕ × ℕ ↦
      Germ.mixedTerm p z.1 z.2 x y)) :
    (∑' z : ℕ × ℕ, Germ.mixedTerm p z.1 z.2 x y) =
      ∑ r : Fin 3, ∑' z : ℕ × ℕ,
        Germ.cubicResidueTerm p r z.1 z.2 x y := by
  let f : ℕ × ℕ → ℂ := fun z ↦
    Germ.mixedTerm p z.1 z.2 x y
  have hsource : Summable (fun z : Fin 3 × (ℕ × ℕ) ↦
      f (Germ.cubicResidueEquiv z)) := by
    exact hsum.comp_injective Germ.cubicResidueEquiv.injective
  calc
    (∑' z : ℕ × ℕ, Germ.mixedTerm p z.1 z.2 x y) =
        ∑' z : ℕ × ℕ, f z := rfl
    _ = ∑' z : Fin 3 × (ℕ × ℕ),
        f (Germ.cubicResidueEquiv z) :=
      (Germ.cubicResidueEquiv.tsum_eq f).symm
    _ = ∑' r : Fin 3, ∑' z : ℕ × ℕ,
        f (Germ.cubicResidueEquiv (r, z)) := hsource.tsum_prod
    _ = ∑ r : Fin 3, ∑' z : ℕ × ℕ,
        f (Germ.cubicResidueEquiv (r, z)) := tsum_fintype _
    _ = ∑ r : Fin 3, ∑' z : ℕ × ℕ,
        Germ.cubicResidueTerm p r z.1 z.2 x y := by
      apply Finset.sum_congr rfl
      intro r hr
      apply tsum_congr
      rintro ⟨m, j⟩
      rw [Germ.cubicResidueEquiv_apply]
      rfl

/-- On a sufficiently small coordinate polydisc, the three compressed series
recover the original formal multilinear series. -/
theorem sum_eq_sum_cubicResidueCompressedSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ)
    (hp : ∀ d, ‖p d‖ ≤ C * ρ ^ d)
    {x y : ℂ} (hx : 2 * ρ * ‖x‖ < 1)
    (hy : 2 * ρ * ‖y‖ < 1) :
    p.sum (Germ.planePoint x y) =
      ∑ r : Fin 3, x ^ r.1 *
        (Germ.cubicResidueCompressedSeries p r).sum
          (Germ.planePoint (x ^ 3) y) := by
  have hall := Germ.summable_mixedTerm_of_geometric_bound
    p hC hρ hp hx hy
  rw [Germ.formalSeries_sum_eq_tsum_mixedTerm p hall]
  rw [Germ.tsum_mixedTerm_eq_sum_cubicResidueTerm p hall]
  apply Finset.sum_congr rfl
  intro r hr
  exact (Germ.cubicResidueCompressedSeries_sum_eq_tsum p r
    (Germ.summable_cubicResidueTerm_of_geometric_bound
      p r hC hρ hp hx hy)).symm

/-- Every plane analytic germ is the sum of three analytic germs after cubic
substitution, with coefficients `1`, `x`, and `x²`. -/
theorem exists_cubicResidue_decomposition (f : Germ 2) :
    ∃ A : Fin 3 → Germ 2,
      f = ∑ r : Fin 3, Germ.coordinate (0 : Fin 2) ^ r.1 *
        Germ.cubicSubstitutionAlgHom (A r) := by
  rcases f with ⟨f, hf⟩
  change IsAnalyticGerm f at hf
  induction f using Filter.Germ.inductionOn with
  | _ F =>
      rw [isAnalyticGerm_ofFun] at hf
      rcases hf with ⟨p, hp⟩
      let q : Fin 3 → FormalMultilinearSeries ℂ (Source 2) ℂ :=
        fun r ↦ Germ.cubicResidueCompressedSeries p r
      have hqRadius (r : Fin 3) : 0 < (q r).radius :=
        Germ.cubicResidueCompressedSeries_radius_pos p hp.radius_pos r
      have hqAnalytic (r : Fin 3) : AnalyticAt ℂ (q r).sum 0 :=
        ((q r).hasFPowerSeriesOnBall (hqRadius r)).analyticAt
      let A : Fin 3 → Germ 2 := fun r ↦
        Germ.ofFunction (q r).sum (hqAnalytic r)
      refine ⟨A, ?_⟩
      obtain ⟨C, ρ, hC, hρ, hpBound⟩ :=
        p.le_mul_pow_of_radius_pos hp.radius_pos
      have hpSum : HasFPowerSeriesAt p.sum p 0 :=
        (p.hasFPowerSeriesOnBall hp.radius_pos).hasFPowerSeriesAt
      have hFSeries : F =ᶠ[nhds 0] p.sum := by
        filter_upwards [hp.eventually_hasSum_sub,
          hpSum.eventually_hasSum_sub] with z hzF hzSum
        simpa only [sub_zero] using hzF.unique hzSum
      have hxSmall :=
        Germ.eventually_geometric_coordinate_bound hρ (0 : Fin 2)
      have hySmall :=
        Germ.eventually_geometric_coordinate_bound hρ (1 : Fin 2)
      have hsubstitution (r : Fin 3) :
          Germ.cubicSubstitutionAlgHom (A r) =
            Germ.ofFunction ((q r).sum ∘ Germ.cubicMap)
              (by
                have hqAt : AnalyticAt ℂ (q r).sum (Germ.cubicMap 0) := by
                  simpa using hqAnalytic r
                exact hqAt.comp Germ.cubicMap_analyticAt) := by
        change Germ.compPointed
            (Germ.ofFunction (q r).sum (hqAnalytic r))
              Germ.cubicMapGerm = _
        rw [Germ.cubicMapGerm, Germ.compPointed_ofFunction]
      simp_rw [hsubstitution]
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hxSmall, hySmall, hFSeries] with z hx hy hzF
      change F z = ∑ r : Fin 3,
        z 0 ^ r.1 * (q r).sum (Germ.cubicMap z)
      rw [hzF]
      have hcubicMap : Germ.cubicMap z =
          Germ.planePoint (z 0 ^ 3) (z 1) := by
        ext i
        fin_cases i <;> simp
      rw [hcubicMap]
      rw [← Germ.planePoint_coordinates z]
      simpa only [q, Germ.planePoint_apply_zero,
        Germ.planePoint_apply_one] using
          Germ.sum_eq_sum_cubicResidueCompressedSeries
            p hC hρ hpBound hx hy

/-- Every plane analytic germ admits a three term cubic substitution
decomposition. -/
theorem exists_cubic_decomposition (f : Germ 2) :
    ∃ A B C : Germ 2,
      f = Germ.cubicSubstitutionAlgHom A +
        Germ.coordinate (0 : Fin 2) * Germ.cubicSubstitutionAlgHom B +
        Germ.coordinate (0 : Fin 2) ^ 2 *
          Germ.cubicSubstitutionAlgHom C := by
  obtain ⟨A, hA⟩ := Germ.exists_cubicResidue_decomposition f
  refine ⟨A 0, A 1, A 2, ?_⟩
  rw [hA, Fin.sum_univ_three]
  norm_num

/-- Analytic division by `x³ + h(y)` with a remainder of degree at most two
in `x`. -/
theorem exists_cubicNormalForm_division
    (h : Germ 1) (hh : h ∈ Germ.maximalIdeal 1) (a : Germ 2) :
    ∃ q : Germ 2, ∃ r₀ r₁ r₂ : Germ 1,
      a = (Germ.coordinate (0 : Fin 2) ^ 3 +
            Germ.hyperplaneExtension 1 h) * q +
          Germ.hyperplaneExtension 1 r₀ +
          Germ.coordinate (0 : Fin 2) * Germ.hyperplaneExtension 1 r₁ +
          Germ.coordinate (0 : Fin 2) ^ 2 *
            Germ.hyperplaneExtension 1 r₂ := by
  obtain ⟨A, B, C, hABC⟩ := Germ.exists_cubic_decomposition a
  obtain ⟨Aq, r₀, hA⟩ := Germ.exists_add_parameter_division h hh A
  obtain ⟨Bq, r₁, hB⟩ := Germ.exists_add_parameter_division h hh B
  obtain ⟨Cq, r₂, hC⟩ := Germ.exists_add_parameter_division h hh C
  let x : Germ 2 := Germ.coordinate (0 : Fin 2)
  let q : Germ 2 := Germ.cubicSubstitutionAlgHom Aq +
    x * Germ.cubicSubstitutionAlgHom Bq +
    x ^ 2 * Germ.cubicSubstitutionAlgHom Cq
  refine ⟨q, r₀, r₁, r₂, ?_⟩
  have hsubstitution (c : Germ 1) :
      Germ.cubicSubstitutionAlgHom (Germ.hyperplaneExtension 1 c) =
        Germ.hyperplaneExtension 1 c :=
    Germ.cubicSubstitution_hyperplaneExtension c
  calc
    a = Germ.cubicSubstitutionAlgHom A +
        x * Germ.cubicSubstitutionAlgHom B +
        x ^ 2 * Germ.cubicSubstitutionAlgHom C := by
      simpa only [x] using hABC
    _ = Germ.cubicSubstitutionAlgHom
          ((Germ.coordinate (0 : Fin 2) +
              Germ.hyperplaneExtension 1 h) * Aq +
            Germ.hyperplaneExtension 1 r₀) +
        x * Germ.cubicSubstitutionAlgHom
          ((Germ.coordinate (0 : Fin 2) +
              Germ.hyperplaneExtension 1 h) * Bq +
            Germ.hyperplaneExtension 1 r₁) +
        x ^ 2 * Germ.cubicSubstitutionAlgHom
          ((Germ.coordinate (0 : Fin 2) +
              Germ.hyperplaneExtension 1 h) * Cq +
            Germ.hyperplaneExtension 1 r₂) := by
      rw [hA, hB, hC]
    _ = (Germ.coordinate (0 : Fin 2) ^ 3 +
            Germ.hyperplaneExtension 1 h) * q +
          Germ.hyperplaneExtension 1 r₀ +
          Germ.coordinate (0 : Fin 2) * Germ.hyperplaneExtension 1 r₁ +
          Germ.coordinate (0 : Fin 2) ^ 2 *
            Germ.hyperplaneExtension 1 r₂ := by
      simp only [map_add, map_mul,
        Germ.cubicSubstitutionAlgHom_coordinate_zero, hsubstitution]
      simp only [x, q]
      ring

end Germ

end OnLeConjecture.Analytic
