import Sandpile.Support.ContDoubleTimeLimit
import Sandpile.Support.ContLcltPoint
import Sandpile.Support.ContGreenFubini
import Sandpile.Support.ContHeatPotentialDoubleTime

/-!
# From the double time limit at one mesh corner to the full interpolated sum

From the double time limit at one pair of mesh sites to the hypothesis of
`Sandpile.Support.heat_potential_fd_of_double_time`.

The doubled coefficient sum of the rescaled linear field is a convex combination, over the `2^d`
corners of the mesh cell of each of the two points of space and the two mesh times of each of the
two times, of the rescaled double time sums of transition probabilities read at those corners and
horizons. The weights depend on the scale and do not converge, but they are nonnegative and sum
to one, so the combination converges as soon as every term does.

Each term is `Sandpile.Support.tendsto_double_time_sum` at the corner sites: the corners of the
mesh cell of a point rescale to that point, so their Euclidean distance is `O(R)` and the squared
distance of the rescalings converges, and the two mesh times are within one step of `R^2 r`.
-/

open LatticeProb.TimeCut

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- The later and earlier mesh time indices `timeIndex R r b` each lie within `1` of `R^2 r`,
since one is `⌊R^2 r⌋` and the other is `⌊R^2 r⌋ + 1`. -/
theorem abs_timeIndex_sub_le {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (b : Bool) :
    |((timeIndex R r b : ℕ) : ℝ) - R ^ 2 * r| ≤ 1 := by
  have hnn : (0:ℝ) ≤ R ^ 2 * r := by positivity
  have hfl : ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * r := Nat.floor_le hnn
  have hlt : R ^ 2 * r < ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  cases b
  · show |((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) - R ^ 2 * r| ≤ 1
    rw [abs_le]
    constructor <;> linarith
  · show |((⌊R ^ 2 * r⌋₊ + 1 : ℕ) : ℝ) - R ^ 2 * r| ≤ 1
    push_cast
    rw [abs_le]
    constructor <;> linarith

/-- The rescaling of a mesh corner `cornerSite d R w ε` differs from the mesh point `meshPoint R w`
by at most `√d / R` in norm: each coordinate differs by at most `1/R`, since the corner shift is
`0` or `1`. -/
theorem norm_scaledSite_cornerSite_sub_le {R : ℝ} (hR : 0 < R) (w : Space d)
    (ε : Fin d → Bool) :
    ‖Sandpile.External.Lclt.scaledSite R (cornerSite d R w ε) - meshPoint R w‖
      ≤ Real.sqrt d / R := by
  set F : Space d := Sandpile.External.Lclt.scaledSite R (cornerSite d R w ε) - meshPoint R w
    with hFdef
  have hcoord : ∀ i : Fin d, |F i| ≤ 1 / R := by
    intro i
    have hval : F i = ((if ε i then (1:ℤ) else 0 : ℤ) : ℝ) / R := by
      show ((cornerSite d R w ε i : ℤ) : ℝ) / R - ((⌊R * w i⌋ : ℤ) : ℝ) / R = _
      rw [cornerSite_def]
      push_cast
      ring
    have hnum : |((if ε i then (1:ℤ) else 0 : ℤ) : ℝ)| ≤ 1 := by
      by_cases h : ε i <;> simp [h]
    rw [hval, abs_div, abs_of_pos hR]
    gcongr
  have hsq : ∑ i : Fin d, (F i) ^ 2 ≤ (d : ℝ) * (1 / R) ^ 2 := by
    calc ∑ i : Fin d, (F i) ^ 2
        ≤ ∑ _i : Fin d, (1 / R) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := hcoord i
          nlinarith [abs_nonneg (F i), sq_abs (F i)]
      _ = (d : ℝ) * (1 / R) ^ 2 := by simp [Finset.sum_const]
  have hnorm : ‖F‖ = Real.sqrt (∑ i : Fin d, (F i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hrhs : Real.sqrt ((d : ℝ) * (1 / R) ^ 2) = Real.sqrt d / R := by
    rw [Real.sqrt_mul hd0, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 / R)]
    field_simp
  calc Real.sqrt (∑ i : Fin d, (F i) ^ 2)
      ≤ Real.sqrt ((d : ℝ) * (1 / R) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt d / R := hrhs

/-- The rescaling of a mesh corner of `w` converges to `w` itself, since by
`norm_scaledSite_cornerSite_sub_le` it differs from `meshPoint R w` by `O(1/R)`, and `meshPoint`
itself converges to `w`. -/
theorem tendsto_scaledSite_cornerSite (w : Space d) (ε : Fin d → Bool) :
    Tendsto (fun R : ℝ => Sandpile.External.Lclt.scaledSite R (cornerSite d R w ε))
      atTop (𝓝 w) := by
  have h0 : Tendsto (fun R : ℝ =>
      Sandpile.External.Lclt.scaledSite R (cornerSite d R w ε) - meshPoint R w)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (?_ : Tendsto (fun R : ℝ => Real.sqrt d / R) atTop (𝓝 0))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact norm_scaledSite_cornerSite_sub_le hR w ε
    · exact tendsto_const_nhds.div_atTop tendsto_id
  have := h0.add (tendsto_meshPoint w)
  simpa using this

/-- The squared distance between the rescalings of two mesh corners converges to `‖w - w'‖^2`,
from `tendsto_scaledSite_cornerSite` at each corner. -/
theorem tendsto_norm_sq_cornerSite (w w' : Space d) (ε ε' : Fin d → Bool) :
    Tendsto (fun R : ℝ => ‖Sandpile.External.Lclt.scaledSite R (cornerSite d R w ε)
        - Sandpile.External.Lclt.scaledSite R (cornerSite d R w' ε')‖ ^ 2)
      atTop (𝓝 (‖w - w'‖ ^ 2)) :=
  (((tendsto_scaledSite_cornerSite w ε).sub (tendsto_scaledSite_cornerSite w' ε')).norm).pow 2

/-- Eventually in `R`, the Euclidean lattice distance between two mesh corners is at most
`(‖w - w'‖ + 1) R`, since their rescaled distance converges to `‖w - w'‖`. -/
theorem eventually_latticeDist_cornerSite (w w' : Space d) (ε ε' : Fin d → Bool) :
    ∀ᶠ R : ℝ in atTop, Sandpile.External.Lclt.latticeDist
        (cornerSite d R w ε) (cornerSite d R w' ε') ≤ (‖w - w'‖ + 1) * R := by
  have hnorm : Tendsto (fun R : ℝ => ‖Sandpile.External.Lclt.scaledSite R (cornerSite d R w ε)
      - Sandpile.External.Lclt.scaledSite R (cornerSite d R w' ε')‖) atTop (𝓝 (‖w - w'‖)) :=
    ((tendsto_scaledSite_cornerSite w ε).sub (tendsto_scaledSite_cornerSite w' ε')).norm
  have hev := hnorm.eventually (gt_mem_nhds (by linarith : ‖w - w'‖ < ‖w - w'‖ + 1))
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with R hR1 hR0
  rw [latticeDist_eq_mul_norm hR0]
  have : ‖Sandpile.External.Lclt.scaledSite R (cornerSite d R w ε)
      - Sandpile.External.Lclt.scaledSite R (cornerSite d R w' ε')‖ ≤ ‖w - w'‖ + 1 := hR1.le
  nlinarith [norm_nonneg (Sandpile.External.Lclt.scaledSite R (cornerSite d R w ε)
      - Sandpile.External.Lclt.scaledSite R (cornerSite d R w' ε'))]

/-- **A convex combination of finitely many families, each converging to the same limit `L`,
converges to `L`**, provided the weights are eventually nonnegative and eventually sum to one.
This is the general mechanism turning a per-corner double time limit into a limit of the whole
interpolated sum. -/
theorem tendsto_convex_comb {ι : Type*} [Fintype ι] {W : ℝ → ι → ℝ} {S : ι → ℝ → ℝ} {L : ℝ}
    (hW0 : ∀ᶠ R : ℝ in atTop, ∀ i, 0 ≤ W R i)
    (hW1 : ∀ᶠ R : ℝ in atTop, ∑ i, W R i = 1)
    (hS : ∀ i, Tendsto (S i) atTop (𝓝 L)) :
    Tendsto (fun R : ℝ => ∑ i, W R i * S i R) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hall : ∀ᶠ R : ℝ in atTop, ∀ i, |S i R - L| ≤ ε / 2 := by
    rw [eventually_all]
    intro i
    have := (hS i).eventually (Metric.closedBall_mem_nhds L (by linarith : (0:ℝ) < ε / 2))
    filter_upwards [this] with R hR
    rwa [Real.dist_eq] at hR
  have hfin : ∀ᶠ R : ℝ in atTop, dist (∑ i, W R i * S i R) L < ε := by
    filter_upwards [hall, hW0, hW1] with R h1 h2 h3
    have hexp : ∑ i, W R i * (S i R - L) = (∑ i, W R i * S i R) - L := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, h3, one_mul]
    have hb : |∑ i, W R i * (S i R - L)| ≤ ∑ i, W R i * (ε / 2) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (h2 i)]
      exact mul_le_mul_of_nonneg_left (h1 i) (h2 i)
    rw [← Finset.sum_mul, h3, one_mul] at hb
    rw [Real.dist_eq, ← hexp]
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfin
  exact ⟨N, hN⟩

set_option maxHeartbeats 1600000 in

/-- **The interpolated double time sum converges to the double time integral `I`.** Written via
`tendsto_convex_comb` as a convex combination over the `2^d × 2` corner-time pairs of each of the
two points, whose weights are `interpTermWeight` (nonnegative, summing to one), and whose terms
each converge to `I` by `tendsto_double_time_sum` applied at the corner sites and time indices,
using `tendsto_norm_sq_cornerSite`, `eventually_latticeDist_cornerSite` and
`abs_timeIndex_sub_le`. -/
theorem tendsto_interpDoubleTimeSum
    (hLCLT : Sandpile.External.LocalCLT) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {r r' I : ℝ} (hr : 0 < r) (hr' : 0 < r') (w w' : Space d)
    (hlim : Tendsto (fun n : ℕ =>
        ∫ s in Set.Ico (0 : ℝ) (r + r' + 1), ∫ u in Set.Ico (0 : ℝ) (r + r' + 1),
          lowerCut n r s * lowerCut n r' u *
            heatKernelBM d (max (s + u) (2 * (1 / ((n : ℝ) + 1)))) w w') atTop (𝓝 I)) :
    Tendsto (fun R : ℝ => interpDoubleTimeSum d R r r' w w') atTop (𝓝 I) := by
  classical
  set W : ℝ → ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool) → ℝ :=
    fun R pq => interpTermWeight d R r w pq.1 * interpTermWeight d R r' w' pq.2 with hWdef
  set S : ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool) → ℝ → ℝ :=
    fun pq R => R ^ ((d : ℝ) - 4) *
      ∑ a ∈ Finset.range (timeIndex R r pq.1.2), ∑ b ∈ Finset.range (timeIndex R r' pq.2.2),
        Sandpile.heatKernel d (a + b) (cornerSite d R w pq.1.1) (cornerSite d R w' pq.2.1)
    with hSdef
  have hrw : ∀ R : ℝ, interpDoubleTimeSum d R r r' w w' = ∑ pq, W R pq * S pq R := by
    intro R
    have hprod : (∑ pq : ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool), W R pq * S pq R)
        = ∑ p : (Fin d → Bool) × Bool, ∑ q : (Fin d → Bool) × Bool, W R (p, q) * S (p, q) R :=
      Fintype.sum_prod_type (f := fun pq => W R pq * S pq R)
    rw [interpDoubleTimeSum, hprod]
  have hW0 : ∀ᶠ R : ℝ in atTop, ∀ pq, 0 ≤ W R pq := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR pq
    exact mul_nonneg (interpTermWeight_nonneg hR hr.le d w pq.1)
      (interpTermWeight_nonneg hR hr'.le d w' pq.2)
  have hW1 : ∀ᶠ R : ℝ in atTop, ∑ pq, W R pq = 1 := by
    filter_upwards with R
    have hprod : (∑ pq : ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool), W R pq)
        = ∑ p : (Fin d → Bool) × Bool, ∑ q : (Fin d → Bool) × Bool, W R (p, q) :=
      Fintype.sum_prod_type (f := fun pq => W R pq)
    rw [hprod, hWdef]
    have : ∀ p : (Fin d → Bool) × Bool,
        ∑ q : (Fin d → Bool) × Bool, interpTermWeight d R r w p * interpTermWeight d R r' w' q
          = interpTermWeight d R r w p := by
      intro p
      rw [← Finset.mul_sum, sum_interpTermWeight, mul_one]
    rw [Finset.sum_congr rfl fun p _ => this p, sum_interpTermWeight]
  have hS : ∀ pq, Tendsto (S pq) atTop (𝓝 I) := by
    intro pq
    refine tendsto_double_time_sum hLCLT hd hd3 hr hr' w w'
      (fun R => cornerSite d R w pq.1.1) (fun R => cornerSite d R w' pq.2.1)
      (fun R => timeIndex R r pq.1.2) (fun R => timeIndex R r' pq.2.2)
      (eventually_latticeDist_cornerSite w w' pq.1.1 pq.2.1)
      (tendsto_norm_sq_cornerSite w w' pq.1.1 pq.2.1) ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact abs_timeIndex_sub_le hR hr.le pq.1.2
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact abs_timeIndex_sub_le hR hr'.le pq.2.2
  have := tendsto_convex_comb hW0 hW1 hS
  exact this.congr fun R => (hrw R).symm

/-! ### The degenerate horizons

At a time horizon zero the double time sum has at most one term in that variable, and
the near-diagonal bound alone sends it to zero, which is the value of the double time
integral there. -/

/-- **A double time sum with at most one term in the first time variable vanishes in the limit.**
When `k R ≤ 1`, the near-diagonal small-time bound `exists_smallTime_bound` alone forces the
rescaled sum to zero, since its error term `Csm (1+T) δ^{1/4}` can be made arbitrarily small by
shrinking `δ`. -/
theorem tendsto_double_time_sum_of_small (hd : 1 ≤ d) (hd3 : d ≤ 3) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (X Y : ℝ → Site d) (k k' : ℝ → ℕ)
    (hk : ∀ᶠ R : ℝ in atTop, ((k R : ℕ) : ℝ) ≤ 1)
    (hk' : ∀ᶠ R : ℝ in atTop, ((k' R : ℕ) : ℝ) ≤ (ρ + 1) * R ^ 2) :
    Tendsto (fun R : ℝ => R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
          Sandpile.heatKernel d (a + b) (X R) (Y R)) atTop (𝓝 0) := by
  obtain ⟨Csm, hCsm, hsm⟩ := exists_smallTime_bound hd hd3
  set T : ℝ := ρ + 1 with hTdef
  have hT : 0 < T := by rw [hTdef]; linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlim0 : Tendsto (fun n : ℕ =>
      Csm * (1 + T) * ((1 : ℝ) / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4)) atTop (𝓝 0) := by
    have := (tendsto_rpow_inv_succ (p := (1:ℝ)/4) (by norm_num)).const_mul (Csm * (1 + T))
    simpa using this
  obtain ⟨n, hn⟩ := (hlim0.eventually (gt_mem_nhds hε)).exists
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hn1]
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hev : ∀ᶠ R : ℝ in atTop, dist (R ^ ((d : ℝ) - 4) *
      ∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
        Sandpile.heatKernel d (a + b) (X R) (Y R)) 0 < ε := by
    filter_upwards [hk, hk', eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (Real.sqrt ((n : ℝ) + 1))] with R hkR hk'R hR1 hRn
    have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
    have hRn2 : ((n : ℝ) + 1) ≤ R ^ 2 := by
      have h := Real.sq_sqrt hn1.le
      nlinarith [Real.sqrt_nonneg ((n : ℝ) + 1)]
    have hA : ((k R : ℕ) : ℝ) ≤ δ * R ^ 2 := by
      have hδR : (1 : ℝ) ≤ δ * R ^ 2 := by
        rw [hδdef, div_mul_eq_mul_div, le_div_iff₀ hn1]
        linarith
      linarith
    have hbound := hsm T hT R δ hR1 hδ0 hδ1 (k R) (k' R) hA hk'R (X R) (Y R)
    have hnn : (0 : ℝ) ≤ R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
          Sandpile.heatKernel d (a + b) (X R) (Y R) :=
      mul_nonneg (Real.rpow_nonneg hR0.le _)
        (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
          Sandpile.heatKernel_nonneg _ _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨N, hN⟩

/-- Both mesh time indices at the degenerate horizon `r = 0` are at most `1`, since
`⌊R^2 · 0⌋ = 0`. -/
theorem timeIndex_zero_le (R : ℝ) (b : Bool) : ((timeIndex R 0 b : ℕ) : ℝ) ≤ 1 := by
  cases b
  · show ((⌊R ^ 2 * 0⌋₊ : ℕ) : ℝ) ≤ 1
    rw [mul_zero, Nat.floor_zero]
    norm_num
  · show ((⌊R ^ 2 * 0⌋₊ + 1 : ℕ) : ℝ) ≤ 1
    rw [mul_zero, Nat.floor_zero]
    norm_num

/-- Both mesh time indices at horizon `ρ` and scale `R ≥ 1` are at most `(ρ + 1) R^2`. -/
theorem timeIndex_le_mul {R ρ : ℝ} (hR : 1 ≤ R) (hρ : 0 ≤ ρ) (b : Bool) :
    ((timeIndex R ρ b : ℕ) : ℝ) ≤ (ρ + 1) * R ^ 2 := by
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hR2 : (1:ℝ) ≤ R ^ 2 := by nlinarith
  have hnn : (0:ℝ) ≤ R ^ 2 * ρ := by positivity
  have hfl : ((⌊R ^ 2 * ρ⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * ρ := Nat.floor_le hnn
  cases b
  · show ((⌊R ^ 2 * ρ⌋₊ : ℕ) : ℝ) ≤ (ρ + 1) * R ^ 2
    nlinarith
  · show ((⌊R ^ 2 * ρ⌋₊ + 1 : ℕ) : ℝ) ≤ (ρ + 1) * R ^ 2
    push_cast
    nlinarith

set_option maxHeartbeats 800000 in

/-- **At the degenerate horizon `r = 0` the interpolated double time sum vanishes in the limit.**
As in `tendsto_interpDoubleTimeSum`, this is `tendsto_convex_comb` applied to the corner-time
terms, but each term now converges to `0` by `tendsto_double_time_sum_of_small`, using
`timeIndex_zero_le` for the degenerate variable and `timeIndex_le_mul` for the other. -/
theorem tendsto_interpDoubleTimeSum_zero_left (hd : 1 ≤ d) (hd3 : d ≤ 3) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (w w' : Space d) :
    Tendsto (fun R : ℝ => interpDoubleTimeSum d R 0 ρ w w') atTop (𝓝 0) := by
  classical
  set W : ℝ → ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool) → ℝ :=
    fun R pq => interpTermWeight d R 0 w pq.1 * interpTermWeight d R ρ w' pq.2 with hWdef
  set S : ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool) → ℝ → ℝ :=
    fun pq R => R ^ ((d : ℝ) - 4) *
      ∑ a ∈ Finset.range (timeIndex R 0 pq.1.2), ∑ b ∈ Finset.range (timeIndex R ρ pq.2.2),
        Sandpile.heatKernel d (a + b) (cornerSite d R w pq.1.1) (cornerSite d R w' pq.2.1)
    with hSdef
  have hrw : ∀ R : ℝ, interpDoubleTimeSum d R 0 ρ w w' = ∑ pq, W R pq * S pq R := by
    intro R
    have hprod : (∑ pq : ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool), W R pq * S pq R)
        = ∑ p : (Fin d → Bool) × Bool, ∑ q : (Fin d → Bool) × Bool, W R (p, q) * S (p, q) R :=
      Fintype.sum_prod_type (f := fun pq => W R pq * S pq R)
    rw [interpDoubleTimeSum, hprod]
  have hW0 : ∀ᶠ R : ℝ in atTop, ∀ pq, 0 ≤ W R pq := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR pq
    exact mul_nonneg (interpTermWeight_nonneg hR le_rfl d w pq.1)
      (interpTermWeight_nonneg hR hρ d w' pq.2)
  have hW1 : ∀ᶠ R : ℝ in atTop, ∑ pq, W R pq = 1 := by
    filter_upwards with R
    have hprod : (∑ pq : ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool), W R pq)
        = ∑ p : (Fin d → Bool) × Bool, ∑ q : (Fin d → Bool) × Bool, W R (p, q) :=
      Fintype.sum_prod_type (f := fun pq => W R pq)
    rw [hprod, hWdef]
    have hin : ∀ p : (Fin d → Bool) × Bool,
        ∑ q : (Fin d → Bool) × Bool, interpTermWeight d R 0 w p * interpTermWeight d R ρ w' q
          = interpTermWeight d R 0 w p := by
      intro p
      rw [← Finset.mul_sum, sum_interpTermWeight, mul_one]
    rw [Finset.sum_congr rfl fun p _ => hin p, sum_interpTermWeight]
  have hS : ∀ pq, Tendsto (S pq) atTop (𝓝 0) := by
    intro pq
    refine tendsto_double_time_sum_of_small hd hd3 hρ
      (fun R => cornerSite d R w pq.1.1) (fun R => cornerSite d R w' pq.2.1)
      (fun R => timeIndex R 0 pq.1.2) (fun R => timeIndex R ρ pq.2.2) ?_ ?_
    · filter_upwards with R
      exact timeIndex_zero_le R pq.1.2
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      exact timeIndex_le_mul hR hρ pq.2.2
  have := tendsto_convex_comb hW0 hW1 hS
  exact this.congr fun R => (hrw R).symm

/-- Swapping the two horizons of a double time sum leaves it unchanged, since `heatKernel` at
`a + b` is symmetric in `a, b` and `Finset.sum_comm` swaps the summation order. -/
theorem doubleTimeSum_swap (k k' : ℕ) (x y : Site d) :
    ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k', Sandpile.heatKernel d (a + b) x y
      = ∑ a ∈ Finset.range k', ∑ b ∈ Finset.range k, Sandpile.heatKernel d (a + b) x y := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [Nat.add_comm]

set_option maxHeartbeats 800000 in

/-- **At the degenerate horizon `r' = 0` the interpolated double time sum vanishes in the limit.**
The mirror image of `tendsto_interpDoubleTimeSum_zero_left`: each corner-time term is reduced to
the already-handled case by `doubleTimeSum_swap`, which exchanges the roles of the two
horizons. -/
theorem tendsto_interpDoubleTimeSum_zero_right (hd : 1 ≤ d) (hd3 : d ≤ 3) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (w w' : Space d) :
    Tendsto (fun R : ℝ => interpDoubleTimeSum d R ρ 0 w w') atTop (𝓝 0) := by
  classical
  set W : ℝ → ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool) → ℝ :=
    fun R pq => interpTermWeight d R ρ w pq.1 * interpTermWeight d R 0 w' pq.2 with hWdef
  set S : ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool) → ℝ → ℝ :=
    fun pq R => R ^ ((d : ℝ) - 4) *
      ∑ a ∈ Finset.range (timeIndex R ρ pq.1.2), ∑ b ∈ Finset.range (timeIndex R 0 pq.2.2),
        Sandpile.heatKernel d (a + b) (cornerSite d R w pq.1.1) (cornerSite d R w' pq.2.1)
    with hSdef
  have hrw : ∀ R : ℝ, interpDoubleTimeSum d R ρ 0 w w' = ∑ pq, W R pq * S pq R := by
    intro R
    have hprod : (∑ pq : ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool), W R pq * S pq R)
        = ∑ p : (Fin d → Bool) × Bool, ∑ q : (Fin d → Bool) × Bool, W R (p, q) * S (p, q) R :=
      Fintype.sum_prod_type (f := fun pq => W R pq * S pq R)
    rw [interpDoubleTimeSum, hprod]
  have hW0 : ∀ᶠ R : ℝ in atTop, ∀ pq, 0 ≤ W R pq := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR pq
    exact mul_nonneg (interpTermWeight_nonneg hR hρ d w pq.1)
      (interpTermWeight_nonneg hR le_rfl d w' pq.2)
  have hW1 : ∀ᶠ R : ℝ in atTop, ∑ pq, W R pq = 1 := by
    filter_upwards with R
    have hprod : (∑ pq : ((Fin d → Bool) × Bool) × ((Fin d → Bool) × Bool), W R pq)
        = ∑ p : (Fin d → Bool) × Bool, ∑ q : (Fin d → Bool) × Bool, W R (p, q) :=
      Fintype.sum_prod_type (f := fun pq => W R pq)
    rw [hprod, hWdef]
    have hin : ∀ p : (Fin d → Bool) × Bool,
        ∑ q : (Fin d → Bool) × Bool, interpTermWeight d R ρ w p * interpTermWeight d R 0 w' q
          = interpTermWeight d R ρ w p := by
      intro p
      rw [← Finset.mul_sum, sum_interpTermWeight, mul_one]
    rw [Finset.sum_congr rfl fun p _ => hin p, sum_interpTermWeight]
  have hS : ∀ pq, Tendsto (S pq) atTop (𝓝 0) := by
    intro pq
    have hswapped := tendsto_double_time_sum_of_small hd hd3 hρ
      (fun R => cornerSite d R w pq.1.1) (fun R => cornerSite d R w' pq.2.1)
      (fun R => timeIndex R 0 pq.2.2) (fun R => timeIndex R ρ pq.1.2)
      (by filter_upwards with R; exact timeIndex_zero_le R pq.2.2)
      (by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
        exact timeIndex_le_mul hR hρ pq.1.2)
    refine hswapped.congr fun R => ?_
    rw [hSdef]
    simp only
    rw [doubleTimeSum_swap]
  have := tendsto_convex_comb hW0 hW1 hS
  exact this.congr fun R => (hrw R).symm

end Sandpile.Support
