import Sandpile.Support.CriticalScales
import Sandpile.Support.GeomRow

/-! # Correlation matrix rows at geometric scales

The rows of the correlation matrix at the geometric scales.

At the times `n_j = N q^j` the correlation bound `eq:corr-bound` decays
geometrically in `|j-k|` with ratio `q^{-1/4}` in every dimension one to three:
in dimensions one and three that is the bound itself, and in dimension two the
extra logarithm is absorbed by `1 + l log q ≤ 3 q^{l/4}`.  Summing the row then
gives off-diagonal mass at most `12 C q^{-1/4}`, which is what makes the
covariance matrix of the standardized fields nearly isotropic once `q` is large.
-/

namespace Sandpile

/-- For `y ≥ 0`, `1 + 4*y ≤ 3 * Real.exp y`, proved by squaring the tangent-line bound
`1 + y/2 ≤ Real.exp (y/2)` and completing the square in `y`. -/
theorem one_add_four_le_three_exp {y : ℝ} (hy : 0 ≤ y) : 1 + 4 * y ≤ 3 * Real.exp y := by
  have h1 : 1 + y / 2 ≤ Real.exp (y / 2) := by
    have := Real.add_one_le_exp (y / 2)
    linarith
  have h2 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : (0 : ℝ) ≤ 1 + y / 2 := by linarith
  nlinarith [sq_nonneg (y - 2/3)]

/-- `1 + l log q ≤ 3 q^{l/4}` for `q ≥ 1`. -/
theorem one_add_mul_log_le {q : ℕ} (hq : 1 ≤ q) (l : ℕ) :
    1 + (l : ℝ) * Real.log (q : ℝ) ≤ 3 * ((q : ℝ) ^ ((l : ℝ) / 4)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  set y : ℝ := (l : ℝ) * Real.log (q : ℝ) / 4 with hy
  have hy0 : 0 ≤ y := by positivity
  have hpow : ((q : ℝ) ^ ((l : ℝ) / 4)) = Real.exp y := by
    rw [Real.rpow_def_of_pos hq0, hy]
    congr 1
    ring
  rw [hpow]
  have := one_add_four_le_three_exp hy0
  have h4 : 4 * y = (l : ℝ) * Real.log (q : ℝ) := by rw [hy]; ring
  linarith [this, h4]

/-- For `x > 0`, the natural power of a real power is the real power of the product
exponent: `(x^a)^l = x^(a*l)`, via `Real.rpow_natCast` and `Real.rpow_mul`. -/
theorem rpow_pow_eq {x : ℝ} (hx : 0 < x) (a : ℝ) (l : ℕ) :
    (x ^ a) ^ l = x ^ (a * (l : ℝ)) := by
  rw [← Real.rpow_natCast (x ^ a) l, ← Real.rpow_mul hx.le]

/-- The ratio of consecutive geometric scale sizes `N * q ^ j` and `N * q ^ (j + l)` is
exactly `q ^ (-l)`. -/
theorem ratio_geom {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) (j l : ℕ) :
    ((N * q ^ j : ℕ) : ℝ) / ((N * q ^ (j + l) : ℕ) : ℝ) = (q : ℝ) ^ (-(l : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1 : (0 : ℝ) < (q : ℝ) ^ j := by positivity
  have h2 : (0 : ℝ) < (q : ℝ) ^ l := by positivity
  push_cast
  rw [Real.rpow_neg hq0.le, Real.rpow_natCast, pow_add]
  field_simp

/-- The reciprocal of `ratio_geom`: `N * q ^ (j + l)` divided by `N * q ^ j` is exactly
`q ^ l`. -/
theorem ratio_geom_inv {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) (j l : ℕ) :
    ((N * q ^ (j + l) : ℕ) : ℝ) / ((N * q ^ j : ℕ) : ℝ) = (q : ℝ) ^ ((l : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1 : (0 : ℝ) < (q : ℝ) ^ j := by positivity
  push_cast
  rw [Real.rpow_natCast, pow_add]
  field_simp

end Sandpile

namespace Sandpile

/-- The geometric ratio `r = q^{-1/4}` of the correlation decay at the scales
`n_j = N q^j`. -/
noncomputable def geomRatio (q : ℕ) : ℝ := (q : ℝ) ^ (-(1 : ℝ) / 4)

/-- `geomRatio q` is positive for `q ≥ 1`, since it is a real power of the positive
base `q`. -/
theorem geomRatio_pos {q : ℕ} (hq : 1 ≤ q) : 0 < geomRatio q := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  exact Real.rpow_pos_of_pos hq0 _

/-- The `l`-th power of `geomRatio q` equals `q ^ (-l/4)`, via `rpow_pow_eq`. -/
theorem geomRatio_pow {q : ℕ} (hq : 1 ≤ q) (l : ℕ) :
    (geomRatio q) ^ l = (q : ℝ) ^ (-(l : ℝ) / 4) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [geomRatio, rpow_pow_eq hq0 _ l]
  congr 1
  ring

/-- **The correlation rate at the geometric scales decays geometrically.** -/
theorem corrRate_geom_le {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {q N : ℕ} (hq : 1 ≤ q)
    (hN : 1 ≤ N) (j l : ℕ) :
    Sandpile.External.Variance.corrRate d (N * q ^ j) (N * q ^ (j + l))
      ≤ 3 * (geomRatio q) ^ l := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hgp : 0 < geomRatio q := geomRatio_pos hq
  have hgl : (0 : ℝ) < (geomRatio q) ^ l := pow_pos hgp l
  rw [Sandpile.External.Variance.corrRate]
  by_cases h2 : d = 2
  · rw [if_pos h2, ratio_geom hq hN j l, ratio_geom_inv hq hN j l]
    have hlog : Real.log ((q : ℝ) ^ ((l : ℝ))) = (l : ℝ) * Real.log (q : ℝ) :=
      Real.log_rpow hq0 _
    have hsqrt : Real.sqrt ((q : ℝ) ^ (-(l : ℝ))) = (q : ℝ) ^ (-(l : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]
      congr 1
      ring
    rw [hlog, hsqrt]
    have hbound := one_add_mul_log_le hq l
    have hpos : (0 : ℝ) < (q : ℝ) ^ (-(l : ℝ) / 2) := Real.rpow_pos_of_pos hq0 _
    have hprod : (3 : ℝ) * ((q : ℝ) ^ ((l : ℝ) / 4)) * ((q : ℝ) ^ (-(l : ℝ) / 2))
        = 3 * (geomRatio q) ^ l := by
      rw [geomRatio_pow hq l, mul_assoc, ← Real.rpow_add hq0]
      congr 2
      ring
    calc (1 + (l : ℝ) * Real.log (q : ℝ)) * (q : ℝ) ^ (-(l : ℝ) / 2)
        ≤ (3 * ((q : ℝ) ^ ((l : ℝ) / 4))) * (q : ℝ) ^ (-(l : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hbound hpos.le
      _ = 3 * (geomRatio q) ^ l := by rw [← hprod]
  · have h4 : d ≠ 4 := by omega
    rw [if_neg h2, if_neg h4, ratio_geom hq hN j l]
    have hpow : ((q : ℝ) ^ (-(l : ℝ))) ^ ((1 : ℝ) / 4) = (geomRatio q) ^ l := by
      rw [← Real.rpow_mul hq0.le, geomRatio_pow hq l]
      congr 1
      ring
    rw [hpow]
    linarith

end Sandpile

namespace Sandpile

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- `Sandpile.External.BerryEsseen.gram` is symmetric in its row and column indices
`j` and `k`, by commutativity of multiplication inside the defining sum. -/
theorem gram_symm {N m : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) (j k : Fin m) :
    Sandpile.External.BerryEsseen.gram ν a j k
      = Sandpile.External.BerryEsseen.gram ν a k j := by
  show variance (id : ℝ → ℝ) ν * ∑ i, a i j * a i k
      = variance (id : ℝ → ℝ) ν * ∑ i, a i k * a i j
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The product of the two Green-time kernels `greenTime d m x` and `greenTime d n y` is
summable over `Site d`, inherited from `summable_greenTime_mul`. -/
theorem summable_greenTime_mul_greenTime (m n : ℕ) (x y : Site d) :
    Summable fun z : Site d => greenTime d m x z * greenTime d n y z :=
  summable_greenTime_mul m x _

/-- Each Gram entry of the standardized coefficients `stdCoeff` is nonnegative: after
unfolding via `gram_stdCoeff` it is a nonnegative sum of products of Green-time values
divided by a positive normalizing product of `Real.sqrt (greenSq ...)` terms. -/
theorem gram_stdCoeff_nonneg (ν : Measure ℝ) (hvar : 0 < variance (id : ℝ → ℝ) ν)
    {s : Finset (Site d)} {m : ℕ} {ns : Fin m → ℕ} (hns : ∀ j, 1 ≤ ns j)
    (hsub : ∀ j, boxFinset (0 : Site d) (ns j) ⊆ s) (j k : Fin m) :
    0 ≤ Sandpile.External.BerryEsseen.gram ν (stdCoeff d ν s ns) j k := by
  rw [gram_stdCoeff ν hvar hns hsub j k]
  have hnum : 0 ≤ ∑' z : Site d, greenTime d (ns j) 0 z * greenTime d (ns k) 0 z :=
    tsum_nonneg fun z => mul_nonneg (greenTime_nonneg _ _ _) (greenTime_nonneg _ _ _)
  have hden : 0 < Real.sqrt (greenSq d (ns j)) * Real.sqrt (greenSq d (ns k)) :=
    mul_pos (Real.sqrt_pos.mpr (greenSq_pos (hns j))) (Real.sqrt_pos.mpr (greenSq_pos (hns k)))
  positivity

/-- Under the correlation-decay hypothesis `hcorr`, the Gram entry
`gram ν (stdCoeff d ν s ns) j k` for `ns j ≤ ns k` is bounded by
`C * corrRate d (ns j) (ns k)`, obtained by dividing the numerator bound from `hcorr`
by the normalizing product of `Real.sqrt (greenSq ...)` terms. -/
theorem gram_stdCoeff_le (ν : Measure ℝ) (hvar : 0 < variance (id : ℝ → ℝ) ν)
    {C : ℝ}
    (hcorr : ∀ m n : ℕ, 1 ≤ m → m ≤ n →
      (∑' x : Site d, greenTime d m 0 x * greenTime d n 0 x) ≤
        C * Sandpile.External.Variance.corrRate d m n *
          Real.sqrt (∑' x : Site d, greenTime d m 0 x ^ 2) *
          Real.sqrt (∑' x : Site d, greenTime d n 0 x ^ 2))
    {s : Finset (Site d)} {m : ℕ} {ns : Fin m → ℕ} (hns : ∀ j, 1 ≤ ns j)
    (hsub : ∀ j, boxFinset (0 : Site d) (ns j) ⊆ s) {j k : Fin m} (hjk : ns j ≤ ns k) :
    Sandpile.External.BerryEsseen.gram ν (stdCoeff d ν s ns) j k
      ≤ C * Sandpile.External.Variance.corrRate d (ns j) (ns k) := by
  rw [gram_stdCoeff ν hvar hns hsub j k]
  have hsj : 0 < Real.sqrt (greenSq d (ns j)) := Real.sqrt_pos.mpr (greenSq_pos (hns j))
  have hsk : 0 < Real.sqrt (greenSq d (ns k)) := Real.sqrt_pos.mpr (greenSq_pos (hns k))
  rw [div_le_iff₀ (mul_pos hsj hsk)]
  have h := hcorr (ns j) (ns k) (hns j) hjk
  calc ∑' z : Site d, greenTime d (ns j) 0 z * greenTime d (ns k) 0 z
      ≤ C * Sandpile.External.Variance.corrRate d (ns j) (ns k) *
          Real.sqrt (greenSq d (ns j)) * Real.sqrt (greenSq d (ns k)) := h
    _ = C * Sandpile.External.Variance.corrRate d (ns j) (ns k) *
          (Real.sqrt (greenSq d (ns j)) * Real.sqrt (greenSq d (ns k))) := by ring

end Sandpile

namespace Sandpile

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- **The rows of the correlation matrix at the geometric scales.** -/
theorem gram_offRow_geom_le (ν : Measure ℝ) (hvar : 0 < variance (id : ℝ → ℝ) ν)
    {C : ℝ} (hC : 0 ≤ C)
    (hcorr : ∀ m n : ℕ, 1 ≤ m → m ≤ n →
      (∑' x : Site d, greenTime d m 0 x * greenTime d n 0 x) ≤
        C * Sandpile.External.Variance.corrRate d m n *
          Real.sqrt (∑' x : Site d, greenTime d m 0 x ^ 2) *
          Real.sqrt (∑' x : Site d, greenTime d n 0 x ^ 2))
    (hd : 1 ≤ d) (hd3 : d ≤ 3) {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N)
    (hr : geomRatio q ≤ 1 / 2)
    {m : ℕ} {s : Finset (Site d)}
    (hsub : ∀ j : Fin m, boxFinset (0 : Site d) (N * q ^ (j : ℕ)) ⊆ s) (j : Fin m) :
    offRow (Sandpile.External.BerryEsseen.gram ν
        (stdCoeff d ν s (fun j : Fin m => N * q ^ (j : ℕ)))) j
      ≤ 12 * C * geomRatio q := by
  set ns : Fin m → ℕ := fun j => N * q ^ (j : ℕ) with hnsdef
  have hns : ∀ j : Fin m, 1 ≤ ns j := by
    intro j
    have : 1 ≤ q ^ (j : ℕ) := Nat.one_le_pow _ _ (by omega)
    calc 1 = 1 * 1 := by ring
      _ ≤ N * q ^ (j : ℕ) := Nat.mul_le_mul hN this
  have hmono : ∀ (a b : ℕ), a ≤ b → N * q ^ a ≤ N * q ^ b := by
    intro a b hab
    exact Nat.mul_le_mul_left N (Nat.pow_le_pow_right (by omega) hab)
  have hgp : 0 < geomRatio q := geomRatio_pos hq
  set S := Sandpile.External.BerryEsseen.gram ν (stdCoeff d ν s ns) with hSdef
  have hSsymm : ∀ a b : Fin m, S a b = S b a := by
    intro a b
    rw [hSdef]
    exact gram_symm ν _ a b
  have hkey : ∀ k : Fin m, offEntry S j k
      ≤ 3 * C * (if j = k then (0 : ℝ)
        else (geomRatio q) ^ (max (k : ℕ) (j : ℕ) - min (k : ℕ) (j : ℕ))) := by
    intro k
    by_cases hjk : j = k
    · rw [offEntry, if_pos hjk, if_pos hjk]
      norm_num
    rw [offEntry, if_neg hjk, if_neg hjk]
    have hnn : ∀ a b : Fin m, 0 ≤ S a b := fun a b =>
      gram_stdCoeff_nonneg ν hvar hns hsub a b
    rcases le_total (j : ℕ) (k : ℕ) with hle | hle
    · have hns' : ns j ≤ ns k := hmono _ _ hle
      have h1 : S j k ≤ C * Sandpile.External.Variance.corrRate d (ns j) (ns k) :=
        gram_stdCoeff_le ν hvar hcorr hns hsub hns'
      have hidx : ns k = N * q ^ ((j : ℕ) + ((k : ℕ) - (j : ℕ))) := by
        have he : (j : ℕ) + ((k : ℕ) - (j : ℕ)) = (k : ℕ) := by omega
        rw [he]
      have h2 : Sandpile.External.Variance.corrRate d (ns j) (ns k)
          ≤ 3 * (geomRatio q) ^ ((k : ℕ) - (j : ℕ)) := by
        rw [hidx]
        exact corrRate_geom_le hd hd3 hq hN (j : ℕ) ((k : ℕ) - (j : ℕ))
      rw [abs_of_nonneg (hnn j k), max_eq_left hle, min_eq_right hle]
      nlinarith [pow_nonneg hgp.le ((k : ℕ) - (j : ℕ))]
    · have hns' : ns k ≤ ns j := hmono _ _ hle
      have h1 : S k j ≤ C * Sandpile.External.Variance.corrRate d (ns k) (ns j) :=
        gram_stdCoeff_le ν hvar hcorr hns hsub hns'
      have hidx : ns j = N * q ^ ((k : ℕ) + ((j : ℕ) - (k : ℕ))) := by
        have he : (k : ℕ) + ((j : ℕ) - (k : ℕ)) = (j : ℕ) := by omega
        rw [he]
      have h2 : Sandpile.External.Variance.corrRate d (ns k) (ns j)
          ≤ 3 * (geomRatio q) ^ ((j : ℕ) - (k : ℕ)) := by
        rw [hidx]
        exact corrRate_geom_le hd hd3 hq hN (k : ℕ) ((j : ℕ) - (k : ℕ))
      rw [abs_of_nonneg (hnn j k), hSsymm j k, max_eq_right hle, min_eq_left hle]
      nlinarith [pow_nonneg hgp.le ((j : ℕ) - (k : ℕ))]
  have hgeom : ∑ k : Fin m,
      (if j = k then (0 : ℝ)
        else (geomRatio q) ^ (max (k : ℕ) (j : ℕ) - min (k : ℕ) (j : ℕ)))
      ≤ 4 * geomRatio q := sum_geom_offdiag_le hgp.le hr j
  calc offRow S j ≤ ∑ k : Fin m, 3 * C * (if j = k then (0 : ℝ)
        else (geomRatio q) ^ (max (k : ℕ) (j : ℕ) - min (k : ℕ) (j : ℕ))) :=
        Finset.sum_le_sum fun k _ => hkey k
    _ = 3 * C * ∑ k : Fin m, (if j = k then (0 : ℝ)
        else (geomRatio q) ^ (max (k : ℕ) (j : ℕ) - min (k : ℕ) (j : ℕ))) := by
        rw [Finset.mul_sum]
    _ ≤ 3 * C * (4 * geomRatio q) := by
        refine mul_le_mul_of_nonneg_left hgeom (by linarith)
    _ = 12 * C * geomRatio q := by ring

end Sandpile
