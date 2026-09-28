import Sandpile.Support.LinStep1Sum
import Sandpile.Support.LinMills

/-!
# Step 1 of the path-survival lemma, Gaussian branch

Step 1 of `lem:dgt4-path-survival` (`sandpile.tex:5499-5528`), the factorization of the
threshold events, in the Gaussian branch.

The paper fixes `\varepsilon\in(0,1)` and deterministic nearest-neighbour paths of at most
`(1-\varepsilon)n_R` steps, lets `\Lambda` be the union of their ranges, and proves that
`\P(\bigcap_{x\in\Lambda}\{J(x)\leq b_x\})` and `\prod_{x\in\Lambda}\P(J(0)\leq b_x)` differ
by `o_R(1)`, uniformly over such paths. In the independent branch the difference is zero
(`Sandpile.centeredMassLaw_threshold_factorization`). In the Gaussian branch the normal
comparison inequality bounds it by
`C\sum_{\{x,y\}}|\rho_{xy}|\exp\{-(b_x^2+b_y^2)/(2\Var(J(0))(1+|\rho_{xy}|))\}`
(`Sandpile.exists_gaussian_threshold_factorization`), and what is proved here is that this
sum tends to zero.

The two inputs the paper names are already theorems:
`Sandpile.exists_correlation_gap` (`Support/LinCorrGap.lean`) is `|\rho_{xy}|\leq\rho_*<1`
at distinct sites, and the Green-function form of `eq:dgt4-intersection-first-moment` is
`\sum_zG(x,z)G(y,z)\leq C(1+|x-y|)^{4-d}`. What is added here is the three missing pieces:

* the level, `sandpile.tex:5518-5521`. A threshold whose Gaussian tail lies between
  `1/(KR^2)` and `K/R^2` has `b^2/\Var(J(0))\geq4\log R-\log\log R-C_0`
  (`level_lower_bound_window`). The lower bound on the tail is what caps the level
  (`level_upper_bound`, Chernoff inverted), and the cap is what turns the `-\log b` of the
  Gaussian tail inversion into `-\log\log R`.
* the two counts, `sandpile.tex:5522-5524`. With the near radius
  `L=(\log R)^{2/(d-4)}` the near pairs of an injective family of `m\leq AR^2` sites number
  at most `m(2L+1)^d\leq A3^dR^2(\log R)^{2d/(d-4)}` (`card_nearPairs_fin_le`,
  `near_count_bound`), and all pairs number at most `m^2\leq A^2R^4`
  (`card_pairs_lt_le`).
* the far correlation, `sandpile.tex:5525-5526`. Beyond the near radius the correlation is
  at most `C_f/(\log R)^2` (`greenGram_div_far_le`).

`Sandpile.pair_sum_split_le` (`Support/LinStep1Sum.lean`) then splits the sum and
`Sandpile.tendsto_pair_bound_zero` (`Support/LinPairSum.lean`) sends the two pieces to zero,
which is `eventually_gauss_path_factorization`.

The conclusion is stated as `\forall\eta>0,\ \forall^\infty R,\ \forall` configuration, not as
a supremum over configurations: a `sSup` over an empty or unbounded family carries a junk
value, and the `\forall\eta` form is the paper's uniformity verbatim.
-/

open LatticeProb.Isonormal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### The Euclidean site distance, and the two pair counts -/

/-- `External.latticeNorm` is symmetric: `latticeNorm (x - y) = latticeNorm (y - x)`, since
negating each coordinate difference `(x - y) i = -(y - x) i` does not change its square. -/
theorem latticeNorm_sub_comm (x y : Site d) :
    External.latticeNorm (x - y) = External.latticeNorm (y - x) := by
  unfold External.latticeNorm
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  have h : ((x - y) i : ℤ) = -((y - x) i : ℤ) := by
    simp [Pi.sub_apply]
  rw [h]
  push_cast
  ring

open Classical in
/-- **The near-pair count for an injective family.** For an injective family
`xs : Fin m → Site d`, the ordered index pairs `i < j` with `latticeNorm (xs j - xs i) ≤ L`
number at most `m * (2L+1)^d`; this pushes `card_nearPairs_le` through the injection from
index pairs to a set of at most `m` distinct image points. -/
theorem card_nearPairs_fin_le {m : ℕ} (xs : Fin m → Site d) (hxs : Function.Injective xs)
    (L : ℝ) (hL : 0 ≤ L) :
    ((((Finset.univ : Finset (Fin m × Fin m)).filter
        (fun p => p.1 < p.2 ∧ External.latticeNorm (xs p.2 - xs p.1) ≤ L)).card : ℝ))
      ≤ (m : ℝ) * (2 * L + 1) ^ d := by
  classical
  have hcard : (Finset.image xs (Finset.univ : Finset (Fin m))).card = m := by
    rw [Finset.card_image_of_injective _ hxs, Finset.card_univ, Fintype.card_fin]
  have hle : (((Finset.univ : Finset (Fin m × Fin m)).filter
      (fun p => p.1 < p.2 ∧ External.latticeNorm (xs p.2 - xs p.1) ≤ L)).card)
      ≤ (((Finset.image xs (Finset.univ : Finset (Fin m))) ×ˢ
          (Finset.image xs (Finset.univ : Finset (Fin m)))).filter
            (fun p => External.latticeNorm (p.2 - p.1) ≤ L)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (xs p.1, xs p.2)) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_image_of_mem xs (Finset.mem_univ _),
        Finset.mem_image_of_mem xs (Finset.mem_univ _)⟩, hp.2⟩
    · intro p _ q _ hpq
      exact Prod.ext (hxs (congrArg Prod.fst hpq)) (hxs (congrArg Prod.snd hpq))
  have hkey := Sandpile.card_nearPairs_le (d := d) L hL
    (Finset.image xs (Finset.univ : Finset (Fin m)))
  rw [hcard] at hkey
  refine le_trans ?_ hkey
  exact_mod_cast hle

open Classical in
/-- **The trivial pair count.** All ordered index pairs `i < j` in `Fin m × Fin m` number at
most `m^2`, from `Finset.card_filter_le` and `card (Fin m × Fin m) = m * m`. -/
theorem card_pairs_lt_le (m : ℕ) :
    ((((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2)).card : ℝ))
      ≤ (m : ℝ) ^ 2 := by
  classical
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin m × Fin m))
    (fun p => p.1 < p.2)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  have h3 : (((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2)).card : ℝ)
      ≤ ((m * m : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h3
  nlinarith [h3]

/-! ### The level forced by the two-sided tail bound -/

/-- **The Chernoff-inverted upper bound on the level.** If the Gaussian tail probability
`P(gaussianReal 0 w > a)` is at least `q > 0` with `a ≥ 0`, then `a/√w ≤ √(2 log(1/q))`: the
Chernoff bound `gaussianReal_measure_ge_le` gives `q ≤ exp(-a²/(2w))`, and taking logs and
inverting solves for `a`. -/
theorem level_upper_bound {w : ℝ≥0} (hw : 0 < (w : ℝ)) {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q)
    (hlow : q ≤ ((gaussianReal 0 w).real (Set.Ioi a))) :
    a / Real.sqrt (w : ℝ) ≤ Real.sqrt (2 * Real.log (1 / q)) := by
  have hsub : Set.Ioi a ⊆ {x : ℝ | a ≤ x} :=
    fun x hx => Set.mem_setOf.mpr (le_of_lt (Set.mem_Ioi.mp hx))
  have hmono : ((gaussianReal 0 w).real (Set.Ioi a))
      ≤ ((gaussianReal 0 w).real {x : ℝ | a ≤ x}) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hch := gaussianReal_measure_ge_le w hw a ha
  have hqe : q ≤ Real.exp (-(a ^ 2 / (2 * (w : ℝ)))) := le_trans hlow (le_trans hmono hch)
  have hlog : Real.log q ≤ -(a ^ 2 / (2 * (w : ℝ))) := by
    have h := Real.log_le_log hq hqe
    rwa [Real.log_exp] at h
  have hinv : a ^ 2 / (w : ℝ) ≤ 2 * Real.log (1 / q) := by
    rw [one_div, Real.log_inv]
    have h2 : a ^ 2 / (2 * (w : ℝ)) ≤ -Real.log q := by linarith
    rw [div_le_iff₀ (by positivity)] at h2
    rw [div_le_iff₀ hw]
    linarith
  have hrw : a / Real.sqrt (w : ℝ) = Real.sqrt (a ^ 2 / (w : ℝ)) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq ha]
  rw [hrw]
  exact Real.sqrt_le_sqrt hinv

/-- **The level of Step 1**, `sandpile.tex:5513-5516`: a threshold whose Gaussian tail is
between `1/(K R^2)` and `K/R^2` has `b^2/\Var \geq 4\log R-\log\log R-C_0`. -/
theorem level_lower_bound_window {w : ℝ≥0} (hw : 0 < (w : ℝ)) {a K R : ℝ}
    (hK : 1 ≤ K) (hKR : K ≤ R) (hR1 : Real.exp 1 ≤ R)
    (ha : Real.sqrt (w : ℝ) ≤ a)
    (hup : ((gaussianReal 0 w).real (Set.Ioi a)) ≤ K / R ^ 2)
    (hlow : 1 / (K * R ^ 2) ≤ ((gaussianReal 0 w).real (Set.Ioi a))) :
    4 * Real.log R - Real.log (Real.log R) - (2 * Real.log K + Real.log 6 + 6)
      ≤ a ^ 2 / (w : ℝ) := by
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hR1
  have hlogR : (1 : ℝ) ≤ Real.log R := (Real.le_log_iff_exp_le hR0).mpr hR1
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have ha0 : 0 ≤ a := le_trans (Real.sqrt_nonneg _) ha
  have hq0 : 0 < 1 / (K * R ^ 2) := by positivity
  have hub0 := level_upper_bound hw ha0 hq0 hlow
  rw [one_div_one_div] at hub0
  have hKR2 : (0 : ℝ) < K * R ^ 2 := by positivity
  have hlogKR2 : Real.log (K * R ^ 2) = Real.log K + 2 * Real.log R := by
    rw [Real.log_mul (ne_of_gt hK0) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogKle : Real.log K ≤ Real.log R := Real.log_le_log hK0 hKR
  have hpos2 : (0 : ℝ) < 2 * Real.log (K * R ^ 2) := by
    rw [hlogKR2]
    have : (0 : ℝ) ≤ Real.log K := Real.log_nonneg hK
    linarith
  have hMle : 2 * Real.log (K * R ^ 2) ≤ 6 * Real.log R := by
    rw [hlogKR2]; linarith
  have hM0 : (0 : ℝ) < Real.sqrt (2 * Real.log (K * R ^ 2)) := Real.sqrt_pos.mpr hpos2
  have hlogM : Real.log (Real.sqrt (2 * Real.log (K * R ^ 2)))
      = Real.log (2 * Real.log (K * R ^ 2)) / 2 := Real.log_sqrt hpos2.le
  have hlogMle : Real.log (2 * Real.log (K * R ^ 2)) ≤ Real.log 6 + Real.log (Real.log R) := by
    have h6 : Real.log (6 * Real.log R) = Real.log 6 + Real.log (Real.log R) :=
      Real.log_mul (by norm_num) (by positivity)
    have h1 : Real.log (2 * Real.log (K * R ^ 2)) ≤ Real.log (6 * Real.log R) :=
      Real.log_le_log hpos2 hMle
    rwa [h6] at h1
  have hkey := level_lower_bound hw ha hup hub0
  have hlogp : Real.log (K / R ^ 2) = Real.log K - 2 * Real.log R := by
    rw [Real.log_div (ne_of_gt hK0) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hlogp, hlogM] at hkey
  linarith

/-! ### The far correlation and the near count -/

/-- The far correlation bound of `sandpile.tex:5520-5522`. -/
theorem greenGram_div_far_le (hd : 5 ≤ d) (v : ℝ≥0) (hv : 0 < (v : ℝ)) (Cf : ℝ) (hCf : 0 ≤ Cf)
    (hfar : ∀ x y : Site d, (∑' z : Site d, green d x z * green d y z)
      ≤ Cf * (1 + External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
    {m : ℕ} (xs : Fin m → Site d) (i j : Fin m) (t : ℝ) (ht : 1 ≤ t)
    (hij : t ^ (2 / ((d : ℝ) - 4)) ≤ External.latticeNorm (xs j - xs i)) :
    greenGram d v xs i j / ((v : ℝ) * greenSqSum d) ≤ Cf / t ^ 2 := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ht0 : (0 : ℝ) < t := by linarith
  have hgs1 : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  have hgs : (0 : ℝ) < greenSqSum d := lt_of_lt_of_le zero_lt_one hgs1
  have hval : greenGram d v xs i j
      = (v : ℝ) * ∑' z : Site d, green d (xs i) z * green d (xs j) z := rfl
  have hsym : External.latticeNorm (xs i - xs j) = External.latticeNorm (xs j - xs i) :=
    latticeNorm_sub_comm _ _
  have hL0 : (0 : ℝ) ≤ t ^ (2 / ((d : ℝ) - 4)) := Real.rpow_nonneg ht0.le _
  have hbase : (0 : ℝ) < 1 + t ^ (2 / ((d : ℝ) - 4)) := by linarith
  have hmono : (1 + External.latticeNorm (xs i - xs j)) ^ (4 - (d : ℝ))
      ≤ (1 + t ^ (2 / ((d : ℝ) - 4))) ^ (4 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hbase (by rw [hsym]; linarith) (by linarith)
  have hstep := rpow_far_exponent_le t ht d hd
  have hneg : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
    rw [Real.rpow_neg ht0.le]
    congr 1
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hS : (∑' z : Site d, green d (xs i) z * green d (xs j) z) ≤ Cf / t ^ 2 := by
    have h1 := hfar (xs i) (xs j)
    have h2 : Cf * (1 + External.latticeNorm (xs i - xs j)) ^ (4 - (d : ℝ))
        ≤ Cf * (1 + t ^ (2 / ((d : ℝ) - 4))) ^ (4 - (d : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hmono hCf
    have h3 : Cf * (1 + t ^ (2 / ((d : ℝ) - 4))) ^ (4 - (d : ℝ)) ≤ Cf * t ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left hstep hCf
    rw [hneg] at h3
    have : Cf * (t ^ 2)⁻¹ = Cf / t ^ 2 := by ring
    linarith [h1, h2, h3, this ▸ h3]
  rw [hval]
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hv
  have hrw : (v : ℝ) * (∑' z : Site d, green d (xs i) z * green d (xs j) z) /
      ((v : ℝ) * greenSqSum d)
      = (∑' z : Site d, green d (xs i) z * green d (xs j) z) / greenSqSum d := by
    field_simp
  rw [hrw, div_le_div_iff₀ hgs (by positivity)]
  have h4 : (∑' z : Site d, green d (xs i) z * green d (xs j) z) * t ^ 2 ≤ Cf :=
    (le_div_iff₀ (by positivity)).mp hS
  nlinarith [h4, hgs1, hCf]

/-- The near-pair count with the near radius `L = t^{2/(d-4)}`. -/
theorem near_count_bound (hd : 5 ≤ d) (m : ℕ) (A R t : ℝ) (_hA : 0 < A) (_hR : 0 < R)
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ A * R ^ 2) :
    (m : ℝ) * (2 * t ^ (2 / ((d : ℝ) - 4)) + 1) ^ d
      ≤ A * 3 ^ d * (R ^ 2 * t ^ (2 * (d : ℝ) / ((d : ℝ) - 4))) := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ht0 : (0 : ℝ) < t := by linarith
  have hL1 : (1 : ℝ) ≤ t ^ (2 / ((d : ℝ) - 4)) :=
    Real.one_le_rpow ht (div_nonneg (by norm_num) (by linarith))
  have hstep : (2 * t ^ (2 / ((d : ℝ) - 4)) + 1) ^ d
      ≤ (3 : ℝ) ^ d * t ^ (2 * (d : ℝ) / ((d : ℝ) - 4)) := by
    have h1 : (2 * t ^ (2 / ((d : ℝ) - 4)) + 1) ≤ 3 * t ^ (2 / ((d : ℝ) - 4)) := by linarith
    have h2 : (2 * t ^ (2 / ((d : ℝ) - 4)) + 1) ^ d ≤ (3 * t ^ (2 / ((d : ℝ) - 4))) ^ d :=
      pow_le_pow_left₀ (by linarith) h1 d
    have h3 : (3 * t ^ (2 / ((d : ℝ) - 4))) ^ d
        = (3 : ℝ) ^ d * (t ^ (2 / ((d : ℝ) - 4))) ^ d := mul_pow _ _ _
    rw [h3, rpow_near_radius_pow t ht0.le d] at h2
    exact h2
  have hpow0 : (0 : ℝ) ≤ (2 * t ^ (2 / ((d : ℝ) - 4)) + 1) ^ d := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hrp : (0 : ℝ) ≤ t ^ (2 * (d : ℝ) / ((d : ℝ) - 4)) := Real.rpow_nonneg ht0.le _
  nlinarith [hm, hstep, hm0, hpow0, hrp, sq_nonneg R]

/-! ### Step 1 -/

/-- **Step 1 of `lem:dgt4-path-survival`, Gaussian branch**: the threshold events at the
sites of an injective family factorize, uniformly over families of at most `A R^2` sites
whose levels have Gaussian tail between `1/(K R^2)` and `K/R^2`. -/
theorem eventually_gauss_path_factorization
    (hNormal : External.NormalComparison) (hd : 5 ≤ d) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (A K : ℝ) (hA : 0 < A) (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ R : ℝ in atTop, ∀ (m : ℕ) (xs : Fin m → Site d), Function.Injective xs →
      (m : ℝ) ≤ A * R ^ 2 →
      ∀ b : Fin m → ℝ,
        (∀ i, Real.sqrt ((v : ℝ) * greenSqSum d) ≤ b i) →
        (∀ i, ((gaussianReal 0 (((v : ℝ) * greenSqSum d).toNNReal)).real (Set.Ioi (b i)))
            ≤ K / R ^ 2) →
        (∀ i, 1 / (K * R ^ 2)
            ≤ ((gaussianReal 0 (((v : ℝ) * greenSqSum d).toNNReal)).real (Set.Ioi (b i)))) →
        |((centeredMassLaw d (gaussianReal 0 v))
              {σ : Site d → ℝ | ∀ i, -infiniteGreenField (scenery d σ) (xs i) ≤ b i}).toReal -
            ∏ i, ((centeredMassLaw d (gaussianReal 0 v))
              {σ : Site d → ℝ | -infiniteGreenField (scenery d σ) 0 ≤ b i}).toReal| ≤ η := by
  classical
  obtain ⟨C, hC, hcomp⟩ := exists_gaussian_threshold_factorization hNormal
  obtain ⟨rs, hrs0, hrs1, hgapc⟩ := exists_correlation_gap (d := d) hd
  obtain ⟨-, -, -, ⟨Cf, hCf, hxy⟩, -⟩ := Sandpile.External.greenBoundsHigh d hd
  have hgs1 : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  have hgs : (0 : ℝ) < greenSqSum d := lt_of_lt_of_le zero_lt_one hgs1
  have hw : (0 : ℝ) < (v : ℝ) * greenSqSum d := by positivity
  have hC0 : (0 : ℝ) ≤ 2 * Real.log K + Real.log 6 + 6 := by
    have h1 : (0 : ℝ) ≤ Real.log K := Real.log_nonneg hK
    have h2 : (0 : ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    linarith
  have hFtend : Tendsto (fun R : ℝ =>
      C * (A * 3 ^ d) * (Real.exp (2 * Real.log R) * (Real.log R) ^ (2 * (d : ℝ) / ((d : ℝ) - 4)) *
          Real.exp (-(4 * Real.log R - Real.log (Real.log R) -
            (2 * Real.log K + Real.log 6 + 6)) / (1 + rs)))
        + C * A ^ 2 * (Real.exp (4 * Real.log R) * (Cf / (Real.log R) ^ 2) *
          Real.exp (-(4 * Real.log R - Real.log (Real.log R) -
            (2 * Real.log K + Real.log 6 + 6)) / (1 + Cf / (Real.log R) ^ 2))))
      atTop (𝓝 0) := by
    refine tendsto_pair_bound_zero rs Cf (2 * Real.log K + Real.log 6 + 6) (C * A ^ 2)
      (C * (A * 3 ^ d)) (2 * (d : ℝ) / ((d : ℝ) - 4)) hrs0 hrs1 hCf.le hC0 _ ?_ ?_
    · filter_upwards [eventually_ge_atTop (Real.exp 1)] with R hR
      have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hR
      have hlogR : (1 : ℝ) ≤ Real.log R := (Real.le_log_iff_exp_le hR0).mpr hR
      have h1 : (0 : ℝ) ≤ (Real.log R) ^ (2 * (d : ℝ) / ((d : ℝ) - 4)) :=
        Real.rpow_nonneg (by linarith) _
      have h2 : (0 : ℝ) ≤ Cf / (Real.log R) ^ 2 := by positivity
      have h3 : (0 : ℝ) ≤ C * (A * 3 ^ d) := by positivity
      have h4 : (0 : ℝ) ≤ C * A ^ 2 := by positivity
      positivity
    · exact Eventually.of_forall (fun R => le_refl _)
  have hFη : ∀ᶠ R : ℝ in atTop, (C * (A * 3 ^ d) *
      (Real.exp (2 * Real.log R) * (Real.log R) ^ (2 * (d : ℝ) / ((d : ℝ) - 4)) *
        Real.exp (-(4 * Real.log R - Real.log (Real.log R) -
          (2 * Real.log K + Real.log 6 + 6)) / (1 + rs)))
      + C * A ^ 2 * (Real.exp (4 * Real.log R) * (Cf / (Real.log R) ^ 2) *
        Real.exp (-(4 * Real.log R - Real.log (Real.log R) -
          (2 * Real.log K + Real.log 6 + 6)) / (1 + Cf / (Real.log R) ^ 2)))) ≤ η :=
    (hFtend.eventually (eventually_lt_nhds hη)).mono (fun R h => h.le)
  filter_upwards [hFη, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop K] with
    R hFR hRe hRK
  intro m xs hxs hm b hb hup hlow
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hRe
  have hlogR : (1 : ℝ) ≤ Real.log R := (Real.le_log_iff_exp_le hR0).mpr hRe
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hL0 : (0 : ℝ) ≤ (Real.log R) ^ (2 / ((d : ℝ) - 4)) := Real.rpow_nonneg (by linarith) _
  have hWcoe : ((((v : ℝ) * greenSqSum d).toNNReal : ℝ≥0) : ℝ) = (v : ℝ) * greenSqSum d :=
    Real.coe_toNNReal _ hw.le
  have hW : (0 : ℝ) < ((((v : ℝ) * greenSqSum d).toNNReal : ℝ≥0) : ℝ) := by rw [hWcoe]; exact hw
  have hB : ∀ i, 4 * Real.log R - Real.log (Real.log R) - (2 * Real.log K + Real.log 6 + 6)
      ≤ b i ^ 2 / ((v : ℝ) * greenSqSum d) := by
    intro i
    have h := level_lower_bound_window (w := ((v : ℝ) * greenSqSum d).toNNReal) hW hK hRK hRe
      (by rw [hWcoe]; exact hb i) (hup i) (hlow i)
    rwa [hWcoe] at h
  set S : Finset (Fin m × Fin m) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun q : Fin m × Fin m => q.1 < q.2) with hSdef
  set T : Finset (Fin m × Fin m) :=
    S.filter (fun q => External.latticeNorm (xs q.2 - xs q.1)
      ≤ (Real.log R) ^ (2 / ((d : ℝ) - 4))) with hTdef
  have hsplit := pair_sum_split_le S T ((v : ℝ) * greenSqSum d)
      (4 * Real.log R - Real.log (Real.log R) - (2 * Real.log K + Real.log 6 + 6))
      rs (Cf / (Real.log R) ^ 2) hw hrs0 (by positivity)
      (fun q => greenGram d v xs q.1 q.2 / ((v : ℝ) * greenSqSum d))
      (fun q => b q.1) (fun q => b q.2)
      (fun q => div_nonneg (greenGram_nonneg v xs q.1 q.2) hw.le)
      (by
        intro q hq _
        have hlt : q.1 < q.2 := by
          rw [hSdef, Finset.mem_filter] at hq
          exact hq.2
        exact greenGram_div_le hd v hv rs hgapc xs q.1 q.2
          (fun h => (ne_of_lt hlt) (hxs h)))
      (by
        intro q hq hnot
        have hge : (Real.log R) ^ (2 / ((d : ℝ) - 4))
            ≤ External.latticeNorm (xs q.2 - xs q.1) := by
          by_cases h : External.latticeNorm (xs q.2 - xs q.1)
              ≤ (Real.log R) ^ (2 / ((d : ℝ) - 4))
          · exact absurd (by rw [hTdef, Finset.mem_filter]; exact ⟨hq, h⟩) hnot
          · exact le_of_not_ge h
        exact greenGram_div_far_le hd v hv Cf hCf.le (fun x y => (hxy x y).2) xs q.1 q.2
          (Real.log R) hlogR hge)
      (fun q _ => hB q.1) (fun q _ => hB q.2)
  have hTcard : (T.card : ℝ)
      ≤ A * 3 ^ d * (R ^ 2 * (Real.log R) ^ (2 * (d : ℝ) / ((d : ℝ) - 4))) := by
    have hTeq : T = (Finset.univ : Finset (Fin m × Fin m)).filter
        (fun q => q.1 < q.2 ∧ External.latticeNorm (xs q.2 - xs q.1)
          ≤ (Real.log R) ^ (2 / ((d : ℝ) - 4))) := by
      rw [hTdef, hSdef, Finset.filter_filter, Finset.univ_product_univ]
    rw [hTeq]
    exact le_trans (card_nearPairs_fin_le xs hxs _ hL0)
      (near_count_bound hd m A R (Real.log R) hA hR0 hlogR hm)
  have hScard : (S.card : ℝ) ≤ A ^ 2 * R ^ 4 := by
    have hSeq : S = (Finset.univ : Finset (Fin m × Fin m)).filter (fun q => q.1 < q.2) := by
      rw [hSdef, Finset.univ_product_univ]
    rw [hSeq]
    refine le_trans (card_pairs_lt_le m) ?_
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [hm, hm0, sq_nonneg R]
  refine le_trans (le_trans (hcomp d hd v hv m xs b) ?_) hFR
  rw [sum_Ioi_eq_sum_pairs]
  refine le_trans (mul_le_mul_of_nonneg_left hsplit hC.le) ?_
  have hexp2 : Real.exp (2 * Real.log R) = R ^ 2 := by
    rw [mul_comm, ← Real.rpow_def_of_pos hR0, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hexp4 : Real.exp (4 * Real.log R) = R ^ 4 := by
    rw [mul_comm, ← Real.rpow_def_of_pos hR0, show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rw [hexp2, hexp4]
  have hE1 : (0 : ℝ) < Real.exp (-(4 * Real.log R - Real.log (Real.log R) -
      (2 * Real.log K + Real.log 6 + 6)) / (1 + rs)) := Real.exp_pos _
  have hE2 : (0 : ℝ) < Real.exp (-(4 * Real.log R - Real.log (Real.log R) -
      (2 * Real.log K + Real.log 6 + 6)) / (1 + Cf / (Real.log R) ^ 2)) := Real.exp_pos _
  have hLp : (0 : ℝ) ≤ (Real.log R) ^ (2 * (d : ℝ) / ((d : ℝ) - 4)) :=
    Real.rpow_nonneg (by linarith) _
  have hCfr0 : (0 : ℝ) ≤ Cf / (Real.log R) ^ 2 := by positivity
  have h1 : (T.card : ℝ) * (rs * Real.exp (-(4 * Real.log R - Real.log (Real.log R) -
        (2 * Real.log K + Real.log 6 + 6)) / (1 + rs)))
      ≤ (A * 3 ^ d * (R ^ 2 * (Real.log R) ^ (2 * (d : ℝ) / ((d : ℝ) - 4)))) *
        (1 * Real.exp (-(4 * Real.log R - Real.log (Real.log R) -
          (2 * Real.log K + Real.log 6 + 6)) / (1 + rs))) := by
    refine mul_le_mul hTcard ?_ (by positivity) (by positivity)
    nlinarith [hE1.le, hrs1]
  have h2 : (S.card : ℝ) * ((Cf / (Real.log R) ^ 2) *
        Real.exp (-(4 * Real.log R - Real.log (Real.log R) -
          (2 * Real.log K + Real.log 6 + 6)) / (1 + Cf / (Real.log R) ^ 2)))
      ≤ (A ^ 2 * R ^ 4) * ((Cf / (Real.log R) ^ 2) *
        Real.exp (-(4 * Real.log R - Real.log (Real.log R) -
          (2 * Real.log K + Real.log 6 + 6)) / (1 + Cf / (Real.log R) ^ 2))) :=
    mul_le_mul_of_nonneg_right hScard (by positivity)
  have h1' := mul_le_mul_of_nonneg_left h1 hC.le
  have h2' := mul_le_mul_of_nonneg_left h2 hC.le
  nlinarith [h1', h2']

end Sandpile
