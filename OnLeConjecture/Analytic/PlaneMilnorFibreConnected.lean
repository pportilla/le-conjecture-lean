/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibreCover
public import OnLeConjecture.External.OpenAIMath.HolomorphicAlgebraicity.Moments
public import OnLeConjecture.External.OpenAIMath.HolomorphicAlgebraicity.SymmetricRootsOn
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Connectedness of polydisc fibres

Let `polydiscFibre H η ρ s` satisfy `GoodPolydisc H η ρ s d`, let `η₀ < η`, and write
`P = polydiscFibre H η₀ ρ s`. Suppose that the roots of `t ↦ H (t, 0) − s` in the disc of
radius `ρ` lie in the open disc of radius `r₀`, and that over every point `x` of the circle
`‖x‖ = r`, with `0 < r` and `2 r ≤ η₀`, distinct roots of `t ↦ H (t, x) − s` in the disc of
radius `ρ` are at distance at least `κ`, where `2 r₀ < κ`. If `P` is nonempty, then `P` is
connected (`GoodPolydisc.isConnected_of_separated_roots`).

The proof is by contradiction. Let `S ⊆ Source 2` be a set whose membership is locally
constant on `P`, and suppose that `P` meets both `S` and its complement. For `x` in the
closed square of radius `η₀`, let `M₁ x` and `M₂ x` be the multisets of the roots `y` of
`t ↦ H (t, x) − s` in the disc of radius `ρ`, repeated according to their orders, with
`(y, x) ∈ S` and `(y, x) ∉ S` respectively (`weightedRoots`).

* Contour moments around small discs, vendored from openai/math, show that the cardinalities
  of `M₁ x` and `M₂ x` are locally constant, hence constant and positive, and that the power
  sums of `M₁ x` and `M₂ x` are holomorphic functions of `x`
  (`GoodPolydisc.exists_local_weightedRoots`).
* By Newton's identities and the Sylvester determinant, the resultant
  `R x = ∏_{a ∈ M₁ x, b ∈ M₂ x} (a − b)` is holomorphic near the closed disc of radius `r`
  (`differentiableOn_prod_map_sub`). It has no zeros because `S` separates `M₁ x` from
  `M₂ x`.
* With `N = |M₁ x| · |M₂ x| ≥ 1`, the bound `‖R 0‖ ≤ (2 r₀) ^ N` holds, and `‖R x‖ ≥ κ ^ N`
  on the circle `‖x‖ = r`. The maximum modulus principle for `1 / R` gives
  `κ ^ N ≤ ‖R 0‖`, which contradicts `2 r₀ < κ`.

The argument does not use simplicity of the roots over the circle `‖x‖ = r`.
`GoodPolydisc.isConnected_of_separated` is the version of the main result that includes
this simplicity hypothesis.
-/

@[expose] public noncomputable section

open Filter Metric Set Polynomial
open scoped Topology

namespace OnLeConjecture.Analytic

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity
open OnLeConjecture.Analytic.Germ

/-! ### Contour moments and holomorphic resultants -/

/-- **Contour moments as weighted power sums.** For `f` analytic near the closed
disc of radius `R` around `c` and without zeros on its boundary circle, the
normalized contour moment of order `k` is the sum of `e_z z ^ k` over the zeros
`z` of `f` in the disc, where `e_z` is the order of `z`. -/
theorem moment_eq_sum_analyticOrderAt {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : ∀ z ∈ sphere c R, f z ≠ 0)
    {Z : Finset ℂ} (hZ : ∀ z ∈ closedBall c R, f z = 0 ↔ z ∈ Z)
    (hZb : ∀ z ∈ Z, z ∈ closedBall c R) (k : ℕ) :
    RootFamiliesAt.Constructions.RootFamilies.moment f c R k =
      ∑ z ∈ Z, ((analyticOrderAt f z).toNat : ℂ) * z ^ k := by
  classical
  obtain ⟨m, roots, u, hroots, hu, hun, hfu⟩ :=
    ClosedDiskFactorization.Constructions.DiskFactorization.exists_root_tuple_unit_on_closedDisk
      hf (RootFamiliesAt.Constructions.RootFamilies.exists_nonzero_in_ball hR hf.continuousOn hb)
      hb
  rw [RootFamiliesAt.Constructions.RootFamilies.moment_of_factorization roots hR hroots hu hun
    hfu k]
  set ms : Multiset ℂ := Finset.univ.val.map roots with hms
  set Q : Polynomial ℂ := (ms.map fun a => Polynomial.X - Polynomial.C a).prod with hQ
  have hQ0 : Q ≠ 0 :=
    (Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a).ne_zero
  have hQroots : Q.roots = ms := Polynomial.roots_multiset_prod_X_sub_C ms
  have hprod : ∀ w, RootMomentsNe.Constructions.RootMoments.rootProduct roots w = Q.eval w := by
    intro w
    simp only [RootMomentsNe.Constructions.RootMoments.rootProduct, Q, ms,
      Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_multiset_prod]
  have hfu' : ∀ z ∈ closedBall c R, f =ᶠ[𝓝 z] fun w => Q.eval w * u w := by
    intro z hz
    simpa only [hprod] using hfu z hz
  have hord : ∀ z ∈ closedBall c R, analyticOrderAt f z = ms.count z := by
    intro z hz
    rw [analyticOrderAt_congr (hfu' z hz),
      analyticOrderAt_polynomial_mul hQ0 (hu z hz) (hun z hz), ← Polynomial.count_roots,
      hQroots]
  have hZeq : Z = ms.toFinset := by
    ext z
    rw [Multiset.mem_toFinset]
    constructor
    · intro hz
      have hzb := hZb z hz
      have h0 := (hZ z hzb).mpr hz
      rw [(hfu' z hzb).eq_of_nhds, mul_eq_zero, or_iff_left (hun z hzb)] at h0
      rw [← hQroots]
      exact (Polynomial.mem_roots hQ0).mpr h0
    · intro hz
      have hzb : z ∈ closedBall c R := by
        obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hz
        exact ball_subset_closedBall (hroots i)
      apply (hZ z hzb).mp
      rw [(hfu' z hzb).eq_of_nhds]
      rw [← hQroots] at hz
      rw [((Polynomial.mem_roots hQ0).mp hz).eq_zero, zero_mul]
  have hsum : ∑ i, roots i ^ k = (ms.map (· ^ k)).sum := by
    simp only [ms, Multiset.map_map, Function.comp_def, Finset.sum_eq_multiset_sum]
  rw [hsum, Finset.sum_multiset_map_count, ← hZeq]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [hord z (hZb z hz), ENat.toNat_natCast, nsmul_eq_mul]

/-- Every multiset of cardinality `n` is the image of a tuple indexed by `Fin n`. -/
theorem exists_fin_map_eq_multiset {α : Type*} {n : ℕ} (m : Multiset α)
    (hm : Multiset.card m = n) : ∃ t : Fin n → α, Finset.univ.val.map t = m := by
  subst hm
  refine ⟨fun i => m.toList.get (i.cast (Multiset.length_toList m).symm), ?_⟩
  rw [Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList m]
  congr 1
  apply List.ext_get (by simp)
  intro i h1 h2
  simp

/-- **Holomorphic coefficients from power sums.** Let `M x` be a multiset of `n` complex
numbers for every `x ∈ U`. If all power sums of `M x` are holomorphic on `U`, then so are
the coefficients of the monic polynomial `∏_{a ∈ M x} (X − a)`. -/
theorem differentiableOn_coeff_prod_X_sub_C {U : Set ℂ} {M : ℂ → Multiset ℂ} {n : ℕ}
    (hcard : ∀ x ∈ U, Multiset.card (M x) = n)
    (hp : ∀ k : ℕ, DifferentiableOn ℂ (fun x => ((M x).map (· ^ k)).sum) U) (j : ℕ) :
    DifferentiableOn ℂ (fun x => ((M x).map fun a => X - C a).prod.coeff j) U := by
  have htup : ∀ x, ∃ t : Fin n → ℂ,
      Multiset.card (M x) = n → Finset.univ.val.map t = M x := by
    intro x
    by_cases h : Multiset.card (M x) = n
    · obtain ⟨t, ht⟩ := exists_fin_map_eq_multiset (M x) h
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose t ht using htup
  have hsum : ∀ x ∈ U, ∀ k : ℕ, ∑ i, t x i ^ k = ((M x).map (· ^ k)).sum := by
    intro x hx k
    rw [← ht x (hcard x hx), Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  have hprod : ∀ x ∈ U, SymmetricRootsOn.Constructions.SymmetricRoots.rootPolynomial (t x) =
      ((M x).map fun a => X - C a).prod := by
    intro x hx
    rw [← ht x (hcard x hx), Multiset.map_map,
      SymmetricRootsOn.Constructions.SymmetricRoots.rootPolynomial, Finset.prod_eq_multiset_prod]
    rfl
  refine (SymmetricRootsOn.Constructions.SymmetricRoots.differentiableOn_rootPolynomial_coeff t
    (fun k => (hp k).congr fun x hx => hsum x hx k) j).congr fun x hx => ?_
  rw [hprod x hx]

/-- The determinant of a matrix of holomorphic functions is holomorphic. -/
theorem differentiableOn_det {U : Set ℂ} {m : ℕ} {A : ℂ → Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ i j, DifferentiableOn ℂ (fun x => A x i j) U) :
    DifferentiableOn ℂ (fun x => (A x).det) U := by
  simp_rw [Matrix.det_apply']
  exact DifferentiableOn.fun_sum fun σ _ =>
    (DifferentiableOn.fun_finsetProd fun i _ => hA _ _).const_mul _

/-- The Sylvester determinant of two polynomials with holomorphic coefficients is
holomorphic. -/
theorem differentiableOn_det_sylvester {U : Set ℂ} {f g : ℂ → ℂ[X]} (m n : ℕ)
    (hf : ∀ j, DifferentiableOn ℂ (fun x => (f x).coeff j) U)
    (hg : ∀ j, DifferentiableOn ℂ (fun x => (g x).coeff j) U) :
    DifferentiableOn ℂ (fun x => ((f x).sylvester (g x) m n).det) U := by
  apply differentiableOn_det
  intro i j
  induction j using Fin.addCases with
  | left j₁ =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    by_cases hc : (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n)
    · simp only [hc, if_true]
      exact hg _
    · simp only [hc, if_false]
      exact differentiableOn_const 0
  | right j₁ =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    by_cases hc : (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m)
    · simp only [hc, if_true]
      exact hf _
    · simp only [hc, if_false]
      exact differentiableOn_const 0

/-- The product of the differences `a − b` over two multisets of complex numbers is the
resultant of the corresponding monic polynomials. -/
theorem prod_map_sub_eq_det_sylvester (M₁ M₂ : Multiset ℂ) :
    ((M₁ ×ˢ M₂).map fun q => q.1 - q.2).prod =
      (((M₁.map fun a => X - C a).prod).sylvester ((M₂.map fun a => X - C a).prod)
        (Multiset.card M₁) (Multiset.card M₂)).det := by
  have h := Polynomial.resultant_eq_prod_roots_sub ((M₁.map fun a => X - C a).prod)
    ((M₂.map fun a => X - C a).prod)
    (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a)
    (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a)
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h
  rw [← h, Polynomial.resultant, natDegree_multiset_prod_X_sub_C_eq_card,
    natDegree_multiset_prod_X_sub_C_eq_card]

/-- **Holomorphy of the root resultant.** Let `M₁ x` and `M₂ x` be multisets of complex
numbers of constant cardinalities for `x ∈ U` whose power sums are holomorphic on `U`.
Then the product of `a − b` over `a ∈ M₁ x` and `b ∈ M₂ x` is holomorphic on `U`. -/
theorem differentiableOn_prod_map_sub {U : Set ℂ} {M₁ M₂ : ℂ → Multiset ℂ} {n₁ n₂ : ℕ}
    (hc₁ : ∀ x ∈ U, Multiset.card (M₁ x) = n₁) (hc₂ : ∀ x ∈ U, Multiset.card (M₂ x) = n₂)
    (hp₁ : ∀ k : ℕ, DifferentiableOn ℂ (fun x => ((M₁ x).map (· ^ k)).sum) U)
    (hp₂ : ∀ k : ℕ, DifferentiableOn ℂ (fun x => ((M₂ x).map (· ^ k)).sum) U) :
    DifferentiableOn ℂ (fun x => ((M₁ x ×ˢ M₂ x).map fun q => q.1 - q.2).prod) U := by
  refine (differentiableOn_det_sylvester n₁ n₂ (differentiableOn_coeff_prod_X_sub_C hc₁ hp₁)
    (differentiableOn_coeff_prod_X_sub_C hc₂ hp₂)).congr fun x hx => ?_
  rw [prod_map_sub_eq_det_sylvester, hc₁ x hx, hc₂ x hx]

/-- A product of complex numbers of norm at most `c` has norm at most `c` to the power of
the number of factors. -/
theorem norm_multiset_prod_le_pow_card {m : Multiset ℂ} {c : ℝ} (h : ∀ z ∈ m, ‖z‖ ≤ c) :
    ‖m.prod‖ ≤ c ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    have ha := h a (Multiset.mem_cons_self a m)
    exact mul_le_mul ha (ih fun z hz => h z (Multiset.mem_cons_of_mem hz)) (norm_nonneg _)
      ((norm_nonneg a).trans ha)

/-- A product of complex numbers of norm at least `c ≥ 0` has norm at least `c` to the power
of the number of factors. -/
theorem pow_card_le_norm_multiset_prod {m : Multiset ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ z ∈ m, c ≤ ‖z‖) : c ^ Multiset.card m ≤ ‖m.prod‖ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self a m))
      (ih fun z hz => h z (Multiset.mem_cons_of_mem hz)) (pow_nonneg hc _) (norm_nonneg _)

/-- A positive strict lower bound for finitely many positive numbers. -/
theorem exists_pos_lt_of_finset {α : Type*} (T : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ T, 0 < f a) : ∃ δ > 0, ∀ a ∈ T, δ < f a := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_le_of_finite (fun a : T => f a) (fun a => hf a a.2)
  exact ⟨δ / 2, half_pos hδ, fun a ha => (half_lt_self hδ).trans_le (h ⟨a, ha⟩)⟩

/-- Differences of points of `Source 2` in fibre and base coordinates. -/
theorem planePoint_sub (y x y' x' : ℂ) :
    planePoint y x - planePoint y' x' = planePoint (y - y') (x - x') := by
  funext i
  fin_cases i <;> rfl

/-! ### Weighted roots over the base -/

open Classical in
/-- The roots of `t ↦ H (t, x) − s` in the closed disc of radius `ρ`, as a finset. It is
empty when this set of roots is infinite. -/
def rootFinset (H : Source 2 → ℂ) (ρ : ℝ) (s x : ℂ) : Finset ℂ :=
  if h : {y : ℂ | ‖y‖ ≤ ρ ∧ H (planePoint y x) = s}.Finite then h.toFinset else ∅

open Classical in
/-- The roots `y` of `t ↦ H (t, x) − s` in the closed disc of radius `ρ` with
`(y, x) ∈ S`, each repeated according to its order. -/
def weightedRoots (H : Source 2 → ℂ) (ρ : ℝ) (s : ℂ) (S : Set (Source 2)) (x : ℂ) :
    Multiset ℂ :=
  ∑ y ∈ (rootFinset H ρ s x).filter (fun y => planePoint y x ∈ S),
    (rootOrder H s y x).toNat • ({y} : Multiset ℂ)

section weightedRoots

variable {H : Source 2 → ℂ} {ρ : ℝ} {s : ℂ} {S : Set (Source 2)} {x : ℂ}

open Classical in
/-- The number of weighted roots is the sum of the orders of the roots involved. -/
theorem card_weightedRoots :
    Multiset.card (weightedRoots H ρ s S x) =
      ∑ y ∈ (rootFinset H ρ s x).filter (fun y => planePoint y x ∈ S),
        (rootOrder H s y x).toNat := by
  simp [weightedRoots]

open Classical in
/-- Sums over the weighted roots are sums over the roots weighted by their orders. -/
theorem sum_map_weightedRoots (g : ℂ → ℂ) :
    ((weightedRoots H ρ s S x).map g).sum =
      ∑ y ∈ (rootFinset H ρ s x).filter (fun y => planePoint y x ∈ S),
        ((rootOrder H s y x).toNat : ℂ) * g y := by
  have hmap : ∀ (t : Finset ℂ) (f : ℂ → Multiset ℂ),
      (∑ y ∈ t, f y).map g = ∑ y ∈ t, (f y).map g :=
    fun t f => map_sum (Multiset.mapAddMonoidHom g) f t
  have hsum : ∀ (t : Finset ℂ) (f : ℂ → Multiset ℂ),
      (∑ y ∈ t, f y).sum = ∑ y ∈ t, (f y).sum :=
    fun t f => map_sum Multiset.sumAddMonoidHom f t
  rw [weightedRoots, hmap, hsum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton,
    nsmul_eq_mul]

/-- Every weighted root over `x` is a root over `x` whose point lies in `S`. -/
theorem mem_weightedRoots {y : ℂ} (hy : y ∈ weightedRoots H ρ s S x) :
    y ∈ rootFinset H ρ s x ∧ planePoint y x ∈ S := by
  classical
  rw [weightedRoots, Multiset.mem_sum] at hy
  obtain ⟨b, hb, hyb⟩ := hy
  rw [Multiset.mem_nsmul, Multiset.mem_singleton] at hyb
  rw [hyb.2]
  exact Finset.mem_filter.mp hb

end weightedRoots

namespace GoodPolydisc

variable {H : Source 2 → ℂ} {η ρ : ℝ} {s : ℂ} {d : ℕ}

/-- A finset that consists of the roots over `x` in the closed disc of radius `ρ` and lies
in the disc of radius `ρ / 2` is the root finset over `x`. -/
theorem rootFinset_eq (hP : GoodPolydisc H η ρ s d) {x : ℂ} {Z : Finset ℂ}
    (hZ : ∀ y : ℂ, ‖y‖ ≤ ρ → (H (planePoint y x) = s ↔ y ∈ Z)) (hZr : ∀ y ∈ Z, ‖y‖ < ρ / 2) :
    rootFinset H ρ s x = Z := by
  have hZρ : ∀ y ∈ Z, ‖y‖ ≤ ρ := fun y hy => (hZr y hy).le.trans (half_le_self hP.radius_pos.le)
  have hset : {y : ℂ | ‖y‖ ≤ ρ ∧ H (planePoint y x) = s} = ↑Z := by
    ext y
    simp only [mem_ofPred_eq, Finset.mem_coe]
    exact ⟨fun h => (hZ y h.1).mp h.2, fun h => ⟨hZρ y h, (hZ y (hZρ y h)).mpr h⟩⟩
  have hfin : {y : ℂ | ‖y‖ ≤ ρ ∧ H (planePoint y x) = s}.Finite := by
    rw [hset]
    exact Z.finite_toSet
  classical
  rw [rootFinset, dif_pos hfin]
  ext y
  rw [Set.Finite.mem_toFinset, hset, Finset.mem_coe]

/-- The defining properties of the root finset over a point of the square. -/
theorem rootFinset_spec (hP : GoodPolydisc H η ρ s d) {x : ℂ} (hx : squareNorm x ≤ η) :
    (∀ y : ℂ, y ∈ rootFinset H ρ s x ↔ ‖y‖ ≤ ρ ∧ H (planePoint y x) = s) ∧
      (∀ y ∈ rootFinset H ρ s x, ‖y‖ < ρ / 2) ∧
      (∀ y ∈ rootFinset H ρ s x, rootOrder H s y x ≠ ⊤) ∧
      ∑ y ∈ rootFinset H ρ s x, (rootOrder H s y x).toNat = d := by
  obtain ⟨Z, hZ, hZr, hZfin, hZsum⟩ := hP.roots x hx
  rw [hP.rootFinset_eq hZ hZr]
  refine ⟨fun y => ⟨fun hy => ?_, fun hy => (hZ y hy.1).mp hy.2⟩, hZr, hZfin, hZsum⟩
  have hyρ : ‖y‖ ≤ ρ := (hZr y hy).le.trans (half_le_self hP.radius_pos.le)
  exact ⟨hyρ, (hZ y hyρ).mpr hy⟩

/-- Every root over a point of the square has positive order. -/
theorem one_le_rootOrder (hP : GoodPolydisc H η ρ s d) {x y : ℂ} (hx : squareNorm x ≤ η)
    (hy : y ∈ rootFinset H ρ s x) : 1 ≤ (rootOrder H s y x).toNat := by
  obtain ⟨hmem, -, hfin, -⟩ := hP.rootFinset_spec hx
  obtain ⟨hyρ, hyH⟩ := (hmem y).mp hy
  exact one_le_rootOrder_toNat (hP.analytic _ hyρ hx) hyH (hfin y hy)

/-- A point of `S` in the polydisc fibre contributes to the weighted roots over its base
point. -/
theorem one_le_card_weightedRoots (hP : GoodPolydisc H η ρ s d) {η' : ℝ} (hη' : η' ≤ η)
    {S : Set (Source 2)} {p : Source 2} (hp : p ∈ polydiscFibre H η' ρ s) (hpS : p ∈ S) :
    1 ≤ Multiset.card (weightedRoots H ρ s S (p 1)) := by
  classical
  have hx : squareNorm (p 1) ≤ η := hp.1.trans hη'
  have hy : p 0 ∈ rootFinset H ρ s (p 1) := by
    rw [(hP.rootFinset_spec hx).1, planePoint_eta]
    exact ⟨hp.2.1, hp.2.2⟩
  rw [card_weightedRoots]
  refine (hP.one_le_rootOrder hx hy).trans ?_
  exact Finset.single_le_sum (f := fun y => (rootOrder H s y (p 1)).toNat)
    (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨hy, by rwa [planePoint_eta]⟩)

/-- The weighted roots over a point of the square are roots in the closed disc of radius `ρ`
whose points lie in `S`. -/
theorem mem_weightedRoots_spec (hP : GoodPolydisc H η ρ s d) {S : Set (Source 2)} {x y : ℂ}
    (hx : squareNorm x ≤ η) (hy : y ∈ weightedRoots H ρ s S x) :
    ‖y‖ ≤ ρ ∧ H (planePoint y x) = s ∧ planePoint y x ∈ S := by
  obtain ⟨hy, hyS⟩ := mem_weightedRoots hy
  exact ⟨(((hP.rootFinset_spec hx).1 y).mp hy).1, (((hP.rootFinset_spec hx).1 y).mp hy).2, hyS⟩

/-- **Local power sums.** Let `x₀` lie in the open square of radius `η` and let the
closed disc of radius `σ` around `a` lie in the open disc of radius `ρ` and have no
root over `x₀` on its boundary. Near `x₀`, the weighted power sums of the roots in
the open disc are holomorphic functions of the base point, and the sum of their orders is
constant. -/
theorem exists_local_moment (hP : GoodPolydisc H η ρ s d) {x₀ a : ℂ}
    (hx₀ : squareNorm x₀ < η) {σ : ℝ} (hσ : 0 < σ) (hball : ∀ y ∈ closedBall a σ, ‖y‖ < ρ)
    (hsph : ∀ y ∈ sphere a σ, H (planePoint y x₀) ≠ s) :
    ∃ U : Set ℂ, IsOpen U ∧ x₀ ∈ U ∧ (∀ x ∈ U, squareNorm x < η) ∧
      (∀ x ∈ U, ∑ y ∈ (rootFinset H ρ s x).filter (fun y => dist y a < σ),
          (rootOrder H s y x).toNat =
        ∑ y ∈ (rootFinset H ρ s x₀).filter (fun y => dist y a < σ),
          (rootOrder H s y x₀).toNat) ∧
      ∀ k : ℕ, ∃ μ : ℂ → ℂ, DifferentiableOn ℂ μ U ∧ ∀ x ∈ U,
        ∑ y ∈ (rootFinset H ρ s x).filter (fun y => dist y a < σ),
          ((rootOrder H s y x).toNat : ℂ) * y ^ k = μ x := by
  classical
  let F : (Fin 1 → ℂ) × ℂ → ℂ := fun p => H (planePoint p.2 (p.1 0)) - s
  let W : Set ((Fin 1 → ℂ) × ℂ) := {p | squareNorm (p.1 0) < η ∧ ‖p.2‖ < ρ}
  have hWo : IsOpen W :=
    (isOpen_lt (continuous_squareNorm.comp ((continuous_apply 0).comp continuous_fst))
      continuous_const).inter (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
  have hFd : DifferentiableOn ℂ F W := by
    intro p hp
    have hpp : DifferentiableAt ℂ (fun p : (Fin 1 → ℂ) × ℂ => planePoint p.2 (p.1 0)) p := by
      have h : (fun p : (Fin 1 → ℂ) × ℂ => planePoint p.2 (p.1 0)) = fun p =>
          p.2 • coordinateVector (0 : Fin 2) + p.1 0 • coordinateVector (1 : Fin 2) := by
        funext p
        exact planePoint_eq_affine _ _
      rw [h]
      fun_prop
    have hH := (hP.analytic (planePoint p.2 (p.1 0)) (by simpa using hp.2.le)
      (by simpa using hp.1.le)).differentiableAt
    exact ((hH.comp p hpp).sub_const s).differentiableWithinAt
  let ι : ℂ → Fin 1 → ℂ := fun x _ => x
  have hιd : Differentiable ℂ ι := differentiable_pi.mpr fun _ => differentiable_id
  obtain ⟨V, hVo, hx₀V, hVW, hVn⟩ :=
    RootFamiliesAt.Constructions.RootFamilies.exists_disk_family_neighborhood hWo
      hFd.continuousOn (x := ι x₀) (c := a) (R := σ)
      (fun z hz => ⟨by simpa [ι] using hx₀, hball z hz⟩)
      (fun z hz => sub_ne_zero.mpr (hsph z hz))
  let μ : ℕ → ℂ → ℂ := fun k x =>
    RootFamiliesAt.Constructions.RootFamilies.moment (fun z => F (ι x, z)) a σ k
  have hU₁o : IsOpen (ι ⁻¹' V) := hVo.preimage hιd.continuous
  have hμd : ∀ k, DifferentiableOn ℂ (μ k) (ι ⁻¹' V) := fun k =>
    (Moments.Constructions.RootFamilies.differentiableOn_moment hWo hFd hVo hσ.le
      (fun p hp => hVW ⟨hp.1, sphere_subset_closedBall hp.2⟩) hVn k).comp
      hιd.differentiableOn (fun x hx => hx)
  have hη : ∀ x ∈ ι ⁻¹' V, squareNorm x < η := fun x hx =>
    (hVW (show (ι x, a) ∈ V ×ˢ closedBall a σ from ⟨hx, mem_closedBall_self hσ.le⟩)).1
  have hμeq : ∀ x ∈ ι ⁻¹' V, ∀ k, μ k x =
      ∑ y ∈ (rootFinset H ρ s x).filter (fun y => dist y a < σ),
        ((rootOrder H s y x).toNat : ℂ) * y ^ k := by
    intro x hx k
    have hmem := (hP.rootFinset_spec (hη x hx).le).1
    apply moment_eq_sum_analyticOrderAt hσ
      (RootFamiliesAt.Constructions.RootFamilies.analyticOnNhd_slice hWo hFd (ι x)
        (fun z hz => hVW ⟨hx, hz⟩)) (fun z hz => hVn (ι x, z) ⟨hx, hz⟩)
    · intro z hz
      have hz0 : F (ι x, z) = 0 ↔ H (planePoint z x) = s := sub_eq_zero
      rw [hz0, Finset.mem_filter, hmem]
      constructor
      · intro h
        refine ⟨⟨(hball z hz).le, h⟩, ?_⟩
        rcases (mem_closedBall.mp hz).lt_or_eq with hlt | heq
        · exact hlt
        · exact absurd h (by simpa [ι, F, sub_eq_zero] using hVn (ι x, z) ⟨hx, heq⟩)
      · exact fun h => h.1.2
    · intro z hz
      exact mem_closedBall.mpr (Finset.mem_filter.mp hz).2.le
  have hcont : ContinuousAt (μ 0) x₀ :=
    ((hμd 0).differentiableAt (hU₁o.mem_nhds hx₀V)).continuousAt
  have hnat : ∀ᶠ x in 𝓝 x₀, ∃ n : ℕ, μ 0 x = n := by
    filter_upwards [hU₁o.mem_nhds hx₀V] with x hx
    refine ⟨∑ y ∈ (rootFinset H ρ s x).filter (fun y => dist y a < σ),
      (rootOrder H s y x).toNat, ?_⟩
    rw [hμeq x hx 0]
    simp
  have hconst := RootFamiliesAt.Constructions.RootFamilies.eventually_eq_of_continuousAt_nat_values
    hcont hnat
  obtain ⟨U, hUsub, hUo, hx₀U⟩ := _root_.mem_nhds_iff.mp (inter_mem hconst (hU₁o.mem_nhds hx₀V))
  refine ⟨U, hUo, hx₀U, fun x hx => hη x (hUsub hx).2, fun x hx => ?_,
    fun k => ⟨μ k, (hμd k).mono fun y hy => (hUsub hy).2, fun x hx => (hμeq x (hUsub hx).2 k).symm⟩⟩
  have h1 := (hUsub hx).1
  simp only [mem_ofPred_eq] at h1
  rw [hμeq x (hUsub hx).2, hμeq x₀ hx₀V] at h1
  simp only [pow_zero, mul_one] at h1
  exact_mod_cast h1

open Classical in
/-- **Local structure of weighted roots.** Let `0 < η₀ < η` and let `S` be a set whose
membership is locally constant on the polydisc fibre `polydiscFibre H η₀ ρ s`. Around each
point `x₀` of the closed square of radius `η₀` there is an open set `U` such that, over the
points `x` of `U` in this square, the number of roots `y` with `(y, x) ∈ S`, counted with
multiplicity, is constant, and the power sums of these roots agree with holomorphic
functions on `U`. -/
theorem exists_local_weightedRoots (hP : GoodPolydisc H η ρ s d) {η₀ : ℝ} (hη₀ : η₀ < η)
    {S : Set (Source 2)}
    (hS : ∀ p ∈ polydiscFibre H η₀ ρ s, ∀ᶠ q in 𝓝 p,
      q ∈ polydiscFibre H η₀ ρ s → (q ∈ S ↔ p ∈ S))
    {x₀ : ℂ} (hx₀ : squareNorm x₀ ≤ η₀) :
    ∃ U : Set ℂ, IsOpen U ∧ x₀ ∈ U ∧
      (∀ x ∈ U, squareNorm x ≤ η₀ →
        Multiset.card (weightedRoots H ρ s S x) = Multiset.card (weightedRoots H ρ s S x₀)) ∧
      ∀ k : ℕ, ∃ μ : ℂ → ℂ, DifferentiableOn ℂ μ U ∧ ∀ x ∈ U, squareNorm x ≤ η₀ →
        ((weightedRoots H ρ s S x).map (· ^ k)).sum = μ x := by
  set Z₀ := rootFinset H ρ s x₀ with hZ₀
  have hx₀η : squareNorm x₀ < η := hx₀.trans_lt hη₀
  obtain ⟨hmem₀, hlt₀, -, hsum₀⟩ := hP.rootFinset_spec hx₀η.le
  have hP₀ : ∀ a ∈ Z₀, planePoint a x₀ ∈ polydiscFibre H η₀ ρ s := fun a ha =>
    ⟨hx₀, ((hmem₀ a).mp ha).1, ((hmem₀ a).mp ha).2⟩
  have hε : ∀ a ∈ Z₀, ∃ ε > 0, ∀ ⦃q⦄, dist q (planePoint a x₀) < ε →
      q ∈ polydiscFibre H η₀ ρ s → (q ∈ S ↔ planePoint a x₀ ∈ S) := fun a ha =>
    Metric.eventually_nhds_iff.mp (hS _ (hP₀ a ha))
  choose! ε hεpos hεS using hε
  obtain ⟨δ₁, hδ₁, hδ₁ε⟩ := exists_pos_lt_of_finset Z₀ ε hεpos
  obtain ⟨δ₂, hδ₂, hδ₂sep⟩ := exists_pos_lt_of_finset ((Z₀ ×ˢ Z₀).filter fun q => q.1 ≠ q.2)
    (fun q => ‖q.1 - q.2‖)
    (fun q hq => norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hq).2))
  set σ := min δ₁ (min (δ₂ / 2) (ρ / 2)) with hσdef
  have hσ : 0 < σ := lt_min hδ₁ (lt_min (half_pos hδ₂) (half_pos hP.radius_pos))
  have hσε : ∀ a ∈ Z₀, σ < ε a := fun a ha => (min_le_left _ _).trans_lt (hδ₁ε a ha)
  have hσsep : ∀ a ∈ Z₀, ∀ b ∈ Z₀, a ≠ b → 2 * σ < ‖a - b‖ := by
    intro a ha b hb hab
    have h1 := hδ₂sep (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩)
    have h2 : σ ≤ δ₂ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    simp only at h1
    linarith
  have hσρ : σ ≤ ρ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have huniq : ∀ a ∈ Z₀, ∀ b ∈ Z₀, dist b a ≤ σ → b = a := by
    intro a ha b hb hba
    by_contra hne
    have := hσsep a ha b hb (Ne.symm hne)
    rw [dist_eq_norm, ← norm_neg, neg_sub] at hba
    linarith
  have hball : ∀ a ∈ Z₀, ∀ y ∈ closedBall a σ, ‖y‖ < ρ := by
    intro a ha y hy
    have h1 := hlt₀ a ha
    have h2 : ‖y‖ ≤ ‖a‖ + ‖y - a‖ := by
      simpa using norm_add_le a (y - a)
    rw [mem_closedBall, dist_eq_norm] at hy
    linarith
  have hloc : ∀ a ∈ Z₀, ∃ U : Set ℂ, IsOpen U ∧ x₀ ∈ U ∧ (∀ x ∈ U, squareNorm x < η) ∧
      (∀ x ∈ U, ∑ y ∈ (rootFinset H ρ s x).filter (fun y => dist y a < σ),
          (rootOrder H s y x).toNat =
        ∑ y ∈ Z₀.filter (fun y => dist y a < σ), (rootOrder H s y x₀).toNat) ∧
      ∀ k : ℕ, ∃ μ : ℂ → ℂ, DifferentiableOn ℂ μ U ∧ ∀ x ∈ U,
        ∑ y ∈ (rootFinset H ρ s x).filter (fun y => dist y a < σ),
          ((rootOrder H s y x).toNat : ℂ) * y ^ k = μ x := by
    intro a ha
    refine hP.exists_local_moment hx₀η hσ (hball a ha) fun y hy hyH => ?_
    have hyZ : y ∈ Z₀ := (hmem₀ y).mpr ⟨(hball a ha y (sphere_subset_closedBall hy)).le, hyH⟩
    have hya := huniq a ha y hyZ (mem_sphere.mp hy).le
    rw [hya, mem_sphere, dist_self] at hy
    exact hσ.ne hy
  choose! U hUo hx₀U hUη hUcount hUμ using hloc
  choose! μ hμd hμeq using hUμ
  set U' : Set ℂ := (⋂ a ∈ Z₀, U a) ∩ ball x₀ σ with hU'
  have hU'o : IsOpen U' := (isOpen_biInter_finset fun a ha => hUo a ha).inter isOpen_ball
  have hx₀U' : x₀ ∈ U' := ⟨mem_iInter₂.mpr fun a ha => hx₀U a ha, mem_ball_self hσ⟩
  have hU'U : ∀ x ∈ U', ∀ a ∈ Z₀, x ∈ U a := fun x hx a ha => mem_iInter₂.mp hx.1 a ha
  have hdisj : ∀ x, (↑Z₀ : Set ℂ).PairwiseDisjoint
      fun a => (rootFinset H ρ s x).filter (fun y => dist y a < σ) := by
    intro x a ha b hb hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro y hya hyb
    have h1 := (Finset.mem_filter.mp hya).2
    have h2 := (Finset.mem_filter.mp hyb).2
    have h3 := hσsep a ha b hb hab
    have h4 : ‖a - b‖ ≤ dist y a + dist y b := by
      rw [← dist_eq_norm]
      exact dist_triangle_left a b y
    linarith
  have hcover : ∀ x ∈ U', squareNorm x ≤ η₀ → ∀ y ∈ rootFinset H ρ s x,
      ∃ a ∈ Z₀, dist y a < σ := by
    intro x hx hxη₀ y hy
    by_contra hno
    push Not at hno
    have hxη : squareNorm x ≤ η := hxη₀.trans hη₀.le
    obtain ⟨-, -, -, hsum⟩ := hP.rootFinset_spec hxη
    set T := Z₀.biUnion fun a => (rootFinset H ρ s x).filter (fun y => dist y a < σ) with hT
    have hTsub : T ⊆ rootFinset H ρ s x :=
      Finset.biUnion_subset.mpr fun a _ => Finset.filter_subset _ _
    have hyT : y ∉ T := by
      intro hyT
      obtain ⟨a, ha, hya⟩ := Finset.mem_biUnion.mp hyT
      exact (hno a ha).not_gt (Finset.mem_filter.mp hya).2
    have hTsum : ∑ y ∈ T, (rootOrder H s y x).toNat = d := by
      rw [Finset.sum_biUnion (hdisj x), ← hsum₀]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hUcount a ha x (hU'U x hx a ha)]
      have hfa : Z₀.filter (fun y => dist y a < σ) = {a} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_singleton]
        refine ⟨fun h => huniq a ha b h.1 h.2.le, ?_⟩
        rintro rfl
        exact ⟨ha, by simpa using hσ⟩
      rw [hfa, Finset.sum_singleton]
    have h1 := Finset.sum_sdiff hTsub (f := fun y => (rootOrder H s y x).toNat)
    have h2 := Finset.single_le_sum (f := fun y => (rootOrder H s y x).toNat)
      (fun _ _ => Nat.zero_le _) (Finset.mem_sdiff.mpr ⟨hy, hyT⟩)
    have h3 := hP.one_le_rootOrder hxη hy
    omega
  have hSiff : ∀ x ∈ U', squareNorm x ≤ η₀ → ∀ a ∈ Z₀, ∀ y ∈ rootFinset H ρ s x,
      dist y a < σ → (planePoint y x ∈ S ↔ planePoint a x₀ ∈ S) := by
    intro x hx hxη₀ a ha y hy hya
    have hmem := (hP.rootFinset_spec (hxη₀.trans hη₀.le)).1
    apply hεS a ha _ ⟨hxη₀, ((hmem y).mp hy).1, ((hmem y).mp hy).2⟩
    rw [dist_eq_norm, planePoint_sub, norm_planePoint, ← dist_eq_norm, ← dist_eq_norm]
    exact max_lt (hya.trans (hσε a ha)) ((mem_ball.mp hx.2).trans (hσε a ha))
  have hdecomp : ∀ x ∈ U', squareNorm x ≤ η₀ →
      (rootFinset H ρ s x).filter (fun y => planePoint y x ∈ S) =
        (Z₀.filter fun a => planePoint a x₀ ∈ S).biUnion
          fun a => (rootFinset H ρ s x).filter (fun y => dist y a < σ) := by
    intro x hx hxη₀
    ext y
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hy, hyS⟩
      obtain ⟨a, ha, hya⟩ := hcover x hx hxη₀ y hy
      exact ⟨a, ⟨ha, (hSiff x hx hxη₀ a ha y hy hya).mp hyS⟩, hy, hya⟩
    · rintro ⟨a, ⟨ha, haS⟩, hy, hya⟩
      exact ⟨hy, (hSiff x hx hxη₀ a ha y hy hya).mpr haS⟩
  have hdisjS : ∀ x, (↑(Z₀.filter fun a => planePoint a x₀ ∈ S) : Set ℂ).PairwiseDisjoint
      fun a => (rootFinset H ρ s x).filter (fun y => dist y a < σ) := fun x =>
    (hdisj x).subset (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have hcard : ∀ x ∈ U', squareNorm x ≤ η₀ → Multiset.card (weightedRoots H ρ s S x) =
      ∑ a ∈ Z₀.filter (fun a => planePoint a x₀ ∈ S),
        ∑ y ∈ Z₀.filter (fun y => dist y a < σ), (rootOrder H s y x₀).toNat := by
    intro x hx hxη₀
    rw [card_weightedRoots, hdecomp x hx hxη₀, Finset.sum_biUnion (hdisjS x)]
    refine Finset.sum_congr rfl fun a ha => ?_
    exact hUcount a (Finset.mem_filter.mp ha).1 x (hU'U x hx a (Finset.mem_filter.mp ha).1)
  refine ⟨U', hU'o, hx₀U', fun x hx hxη₀ => by rw [hcard x hx hxη₀, hcard x₀ hx₀U' hx₀],
    fun k => ⟨fun x => ∑ a ∈ Z₀.filter (fun a => planePoint a x₀ ∈ S), μ a k x, ?_, ?_⟩⟩
  · exact DifferentiableOn.fun_sum fun a ha =>
      (hμd a (Finset.mem_filter.mp ha).1 k).mono fun x hx => hU'U x hx a (Finset.mem_filter.mp ha).1
  · intro x hx hxη₀
    rw [sum_map_weightedRoots, hdecomp x hx hxη₀, Finset.sum_biUnion (hdisjS x)]
    refine Finset.sum_congr rfl fun a ha => ?_
    exact hμeq a (Finset.mem_filter.mp ha).1 k x (hU'U x hx a (Finset.mem_filter.mp ha).1)


/-! ### Connectedness -/

/-- **Constancy of the weighted root count.** If membership in `S` is locally constant on
the polydisc fibre `polydiscFibre H η₀ ρ s` with `η₀ < η`, then the number of roots `y`
over `x` with `(y, x) ∈ S`, counted with multiplicity, does not depend on the point `x` of
the closed square of radius `η₀`. -/
theorem card_weightedRoots_eq (hP : GoodPolydisc H η ρ s d) {η₀ : ℝ} (hη₀ : η₀ < η)
    {S : Set (Source 2)}
    (hS : ∀ p ∈ polydiscFibre H η₀ ρ s, ∀ᶠ q in 𝓝 p,
      q ∈ polydiscFibre H η₀ ρ s → (q ∈ S ↔ p ∈ S))
    {x y : ℂ} (hx : squareNorm x ≤ η₀) (hy : squareNorm y ≤ η₀) :
    Multiset.card (weightedRoots H ρ s S x) = Multiset.card (weightedRoots H ρ s S y) := by
  refine (convex_closedSquare η₀).isPreconnected.constant
    (f := fun x => Multiset.card (weightedRoots H ρ s S x)) (fun x₀ hx₀ => ?_) hx hy
  obtain ⟨U, hUo, hx₀U, hcard, -⟩ := hP.exists_local_weightedRoots hη₀ hS hx₀
  rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
  filter_upwards [inter_mem_nhdsWithin (closedSquare η₀) (hUo.mem_nhds hx₀U)] with x hx
  exact hcard x hx.2 hx.1

/-- **No separating clopen set.** Under the hypotheses of
`GoodPolydisc.isConnected_of_separated`, no set whose membership is locally constant on the
polydisc fibre `polydiscFibre H η₀ ρ s` contains one point of this fibre and misses
another. -/
theorem false_of_separated (hP : GoodPolydisc H η ρ s d) {η₀ r r₀ κ : ℝ} (hη₀ : η₀ < η)
    (hr : 0 < r) (hrη : 2 * r ≤ η₀)
    (hzero : ∀ y : ℂ, ‖y‖ ≤ ρ → H (planePoint y 0) = s → ‖y‖ < r₀)
    (hsep : ∀ x : ℂ, ‖x‖ = r → ∀ y y' : ℂ, ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ → H (planePoint y x) = s →
      H (planePoint y' x) = s → y ≠ y' → κ ≤ ‖y - y'‖)
    (hκ : 2 * r₀ < κ) {S : Set (Source 2)}
    (hS : ∀ p ∈ polydiscFibre H η₀ ρ s, ∀ᶠ q in 𝓝 p,
      q ∈ polydiscFibre H η₀ ρ s → (q ∈ S ↔ p ∈ S))
    {p₁ p₂ : Source 2} (hp₁ : p₁ ∈ polydiscFibre H η₀ ρ s) (hp₁S : p₁ ∈ S)
    (hp₂ : p₂ ∈ polydiscFibre H η₀ ρ s) (hp₂S : p₂ ∉ S) : False := by
  have hSc : ∀ p ∈ polydiscFibre H η₀ ρ s, ∀ᶠ q in 𝓝 p,
      q ∈ polydiscFibre H η₀ ρ s → (q ∈ Sᶜ ↔ p ∈ Sᶜ) := fun p hp =>
    (hS p hp).mono fun q hq hqP => not_congr (hq hqP)
  have hsq0 : squareNorm 0 ≤ η₀ := by
    have : squareNorm 0 = 0 := by simp [squareNorm]
    rw [this]
    linarith
  set M₁ : ℂ → Multiset ℂ := fun x => weightedRoots H ρ s S x with hM₁
  set M₂ : ℂ → Multiset ℂ := fun x => weightedRoots H ρ s Sᶜ x with hM₂
  set n₁ := Multiset.card (M₁ 0) with hn₁def
  set n₂ := Multiset.card (M₂ 0) with hn₂def
  have hc₁ : ∀ x, squareNorm x ≤ η₀ → Multiset.card (M₁ x) = n₁ := fun x hx =>
    hP.card_weightedRoots_eq hη₀ hS hx hsq0
  have hc₂ : ∀ x, squareNorm x ≤ η₀ → Multiset.card (M₂ x) = n₂ := fun x hx =>
    hP.card_weightedRoots_eq hη₀ hSc hx hsq0
  have hn₁ : 1 ≤ n₁ := by
    rw [← hc₁ _ hp₁.1]
    exact hP.one_le_card_weightedRoots hη₀.le hp₁ hp₁S
  have hn₂ : 1 ≤ n₂ := by
    rw [← hc₂ _ hp₂.1]
    exact hP.one_le_card_weightedRoots hη₀.le hp₂ hp₂S
  set R : ℂ → ℂ := fun x => ((M₁ x ×ˢ M₂ x).map fun q => q.1 - q.2).prod with hR
  have hsmall : ∀ x : ℂ, ‖x‖ ≤ r → squareNorm x < η₀ := fun x hx => by
    have := squareNorm_le_norm x
    linarith
  have hRd : ∀ x ∈ closedBall (0 : ℂ) r, DifferentiableAt ℂ R x := by
    intro x hx
    have hxη : squareNorm x < η₀ := hsmall x (by simpa using hx)
    obtain ⟨U₁, hU₁o, hxU₁, hU₁c, hU₁p⟩ := hP.exists_local_weightedRoots hη₀ hS hxη.le
    obtain ⟨U₂, hU₂o, hxU₂, hU₂c, hU₂p⟩ := hP.exists_local_weightedRoots hη₀ hSc hxη.le
    set V := U₁ ∩ U₂ ∩ {y | squareNorm y < η₀} with hV
    have hVo : IsOpen V :=
      (hU₁o.inter hU₂o).inter (isOpen_lt continuous_squareNorm continuous_const)
    have hxV : x ∈ V := ⟨⟨hxU₁, hxU₂⟩, hxη⟩
    have hRV : DifferentiableOn ℂ R V := by
      refine differentiableOn_prod_map_sub (fun y hy => hU₁c y hy.1.1 hy.2.le)
        (fun y hy => hU₂c y hy.1.2 hy.2.le) (fun k => ?_) (fun k => ?_)
      · obtain ⟨μ, hμd, hμ⟩ := hU₁p k
        exact (hμd.mono fun y hy => hy.1.1).congr fun y hy => hμ y hy.1.1 hy.2.le
      · obtain ⟨μ, hμd, hμ⟩ := hU₂p k
        exact (hμd.mono fun y hy => hy.1.2).congr fun y hy => hμ y hy.1.2 hy.2.le
    exact hRV.differentiableAt (hVo.mem_nhds hxV)
  have hRne : ∀ x, R x ≠ 0 := by
    intro x
    apply Multiset.prod_ne_zero
    intro h0
    obtain ⟨q, hq, hq0⟩ := Multiset.mem_map.mp h0
    rw [Multiset.mem_product] at hq
    have h1 := (mem_weightedRoots hq.1).2
    have h2 := (mem_weightedRoots hq.2).2
    rw [sub_eq_zero.mp hq0] at h1
    exact h2 h1
  set N := n₁ * n₂ with hNdef
  have hN : N ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hcardR : ∀ x, squareNorm x ≤ η₀ →
      Multiset.card ((M₁ x ×ˢ M₂ x).map fun q => q.1 - q.2) = N := by
    intro x hx
    rw [Multiset.card_map, Multiset.card_product, hc₁ x hx, hc₂ x hx]
  obtain ⟨y₀, hy₀⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card (M₁ 0))
  have hr₀ : 0 ≤ r₀ := by
    obtain ⟨h1, h2, -⟩ := hP.mem_weightedRoots_spec (hsq0.trans hη₀.le) hy₀
    exact (norm_nonneg y₀).trans (hzero y₀ h1 h2).le
  have hκpos : 0 < κ := by linarith
  have hR0 : ‖R 0‖ ≤ (2 * r₀) ^ N := by
    rw [← hcardR 0 hsq0]
    apply norm_multiset_prod_le_pow_card
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hz
    rw [Multiset.mem_product] at hq
    obtain ⟨h1ρ, h1H, -⟩ := hP.mem_weightedRoots_spec (hsq0.trans hη₀.le) hq.1
    obtain ⟨h2ρ, h2H, -⟩ := hP.mem_weightedRoots_spec (hsq0.trans hη₀.le) hq.2
    have h1 := hzero q.1 h1ρ h1H
    have h2 := hzero q.2 h2ρ h2H
    calc ‖q.1 - q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := norm_sub_le _ _
      _ ≤ 2 * r₀ := by linarith
  have hRbd : ∀ x ∈ sphere (0 : ℂ) r, κ ^ N ≤ ‖R x‖ := by
    intro x hx
    have hxn : ‖x‖ = r := by simpa using hx
    have hxη : squareNorm x ≤ η₀ := (hsmall x hxn.le).le
    rw [← hcardR x hxη]
    apply pow_card_le_norm_multiset_prod hκpos.le
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hz
    rw [Multiset.mem_product] at hq
    obtain ⟨h1ρ, h1H, h1S⟩ := hP.mem_weightedRoots_spec (hxη.trans hη₀.le) hq.1
    obtain ⟨h2ρ, h2H, h2S⟩ := hP.mem_weightedRoots_spec (hxη.trans hη₀.le) hq.2
    refine hsep x hxn q.1 q.2 h1ρ h2ρ h1H h2H fun heq => ?_
    rw [heq] at h1S
    exact h2S h1S
  have hdc : DiffContOnCl ℂ (fun x => (R x)⁻¹) (ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hr.ne']
    intro x hx
    exact ((hRd x hx).inv (hRne x)).differentiableWithinAt
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
    (C := (κ ^ N)⁻¹) (fun z hz => ?_) (subset_closure (mem_ball_self hr))
  · rw [norm_inv] at hmax
    have hR0pos : 0 < ‖R 0‖ := norm_pos_iff.mpr (hRne 0)
    have hκN : 0 < κ ^ N := pow_pos hκpos N
    have h1 : κ ^ N ≤ ‖R 0‖ := (inv_le_inv₀ hR0pos hκN).mp hmax
    have h2 : (2 * r₀) ^ N < κ ^ N := pow_lt_pow_left₀ hκ (by linarith) hN
    linarith
  · rw [frontier_ball 0 hr.ne'] at hz
    rw [norm_inv]
    exact inv_anti₀ (pow_pos hκpos N) (hRbd z hz)

/-- **Connectedness of a polydisc fibre.** Let `η₀ < η`, `0 < r` and `2 r ≤ η₀`. Suppose
that the roots of `t ↦ H (t, 0) − s` in the disc of radius `ρ` lie in the open disc of
radius `r₀`, and that over every point `x` with `‖x‖ = r`, distinct roots of
`t ↦ H (t, x) − s` in the disc of radius `ρ` are at distance at least `κ`, where
`2 r₀ < κ`. If the polydisc fibre `polydiscFibre H η₀ ρ s` is nonempty, then it is
connected. -/
theorem isConnected_of_separated_roots (hP : GoodPolydisc H η ρ s d) {η₀ r r₀ κ : ℝ}
    (hη₀ : η₀ < η) (hr : 0 < r) (hrη : 2 * r ≤ η₀)
    (hzero : ∀ y : ℂ, ‖y‖ ≤ ρ → H (planePoint y 0) = s → ‖y‖ < r₀)
    (hsep : ∀ x : ℂ, ‖x‖ = r → ∀ y y' : ℂ, ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ → H (planePoint y x) = s →
      H (planePoint y' x) = s → y ≠ y' → κ ≤ ‖y - y'‖)
    (hκ : 2 * r₀ < κ) (hne : (polydiscFibre H η₀ ρ s).Nonempty) :
    IsConnected (polydiscFibre H η₀ ρ s) := by
  refine ⟨hne, ?_⟩
  rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_clopen]
  intro T hT
  by_contra hcon
  push Not at hcon
  obtain ⟨hT0, hT1⟩ := hcon
  set S : Set (Source 2) := Subtype.val '' T with hSdef
  have hmemS : ∀ (q : Source 2) (hq : q ∈ polydiscFibre H η₀ ρ s),
      q ∈ S ↔ (⟨q, hq⟩ : ↥(polydiscFibre H η₀ ρ s)) ∈ T := by
    intro q hq
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro h
      exact ⟨⟨q, hq⟩, h, rfl⟩
  have hS : ∀ p ∈ polydiscFibre H η₀ ρ s, ∀ᶠ q in 𝓝 p,
      q ∈ polydiscFibre H η₀ ρ s → (q ∈ S ↔ p ∈ S) := by
    intro p hp
    by_cases hpT : (⟨p, hp⟩ : ↥(polydiscFibre H η₀ ρ s)) ∈ T
    · obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype _ _ T).mp (hT.isOpen.mem_nhds hpT)
      filter_upwards [hu] with q hq hqP
      rw [hmemS q hqP, hmemS p hp]
      exact iff_of_true (hsub hq) hpT
    · obtain ⟨u, hu, hsub⟩ :=
        (mem_nhds_subtype _ _ Tᶜ).mp (hT.compl.isOpen.mem_nhds hpT)
      filter_upwards [hu] with q hq hqP
      rw [hmemS q hqP, hmemS p hp]
      exact iff_of_false (hsub hq) hpT
  obtain ⟨⟨p₁, hp₁⟩, hp₁T⟩ := hT0
  obtain ⟨⟨p₂, hp₂⟩, hp₂T⟩ := (ne_univ_iff_exists_notMem T).mp hT1
  exact hP.false_of_separated hη₀ hr hrη hzero hsep hκ hS hp₁ ((hmemS p₁ hp₁).mpr hp₁T) hp₂
    (fun h => hp₂T ((hmemS p₂ hp₂).mp h))

/-- **Connectedness of a polydisc fibre**, stated with simple roots over the circle
`‖x‖ = r`. The simplicity hypothesis is not used in the proof, see
`GoodPolydisc.isConnected_of_separated_roots`. -/
theorem isConnected_of_separated {H : Source 2 → ℂ} {η ρ : ℝ} {s : ℂ} {d : ℕ}
    (hP : GoodPolydisc H η ρ s d) {η₀ r r₀ κ : ℝ} (hη₀ : η₀ < η) (hr : 0 < r)
    (hrη : 2 * r ≤ η₀)
    (hzero : ∀ y : ℂ, ‖y‖ ≤ ρ → H (planePoint y 0) = s → ‖y‖ < r₀)
    (hsep : ∀ x : ℂ, ‖x‖ = r → ∀ y y' : ℂ, ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ → H (planePoint y x) = s →
      H (planePoint y' x) = s → y ≠ y' → κ ≤ ‖y - y'‖)
    (_hsimple : ∀ x : ℂ, ‖x‖ = r → ∀ y : ℂ, ‖y‖ ≤ ρ → H (planePoint y x) = s →
      rootOrder H s y x = 1)
    (hκ : 2 * r₀ < κ) (hne : (polydiscFibre H η₀ ρ s).Nonempty) :
    IsConnected (polydiscFibre H η₀ ρ s) :=
  hP.isConnected_of_separated_roots hη₀ hr hrη hzero hsep hκ hne

end GoodPolydisc

end OnLeConjecture.Analytic
