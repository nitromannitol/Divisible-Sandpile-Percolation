import Sandpile.Support.PercolationEvents
import Sandpile.Support.AnnularSum
import Sandpile.Frozen.DGT4BlockingToCrossing
import Sandpile.Frozen.DGT4Cascade

/-!
# Exponential bound for failure of the origin to connect to infinity

This file bounds the probability that the origin fails to lie in an infinite component of
`{x | m/2 < u_t(x)}`, where `m` is the mean odometer at the origin. The failure event splits into
the unit box around the origin not clearing the level `m/2` (`measure_unit_box_failure_le`, a
union bound over finitely many sites) and the unit box clearing it while its component stays
finite (`measure_blocked_odometer_le`), which the blocking-to-crossing dichotomy embeds into a
union of annular low-crossing events summed geometrically (`Sandpile.AnnularSum`). Both pieces
decay like `exp(-b m)` for some `b > 0`, giving the exponential bound
`exists_odometer_origin_connection`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

/-- The event that the unit box about the origin lies entirely above level `s` in the odometer
field at time `t`, and the origin's component of `{x | s < odometerOf ω t x}` is infinite. -/
def odometerOriginConnectEvent {d : ℕ} (t : ℕ) (s : ℝ) : Set (Site d → ℝ) :=
  {ω | Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1 ⊆ {x | s < odometerOf ω t x} ∧
    (LatticeProb.componentIn {x | s < odometerOf ω t x} (0 : Site d)).Infinite}

/-- `odometerOriginConnectEvent` is measurable, as the intersection of a countable intersection of
level-set events and the measurable event that a component is infinite. -/
lemma measurableSet_odometerOriginConnectEvent {d : ℕ} (t : ℕ) (s : ℝ) :
    MeasurableSet (odometerOriginConnectEvent (d := d) t s) := by
  have hO (x : Site d) : MeasurableSet {ω : Site d → ℝ | s < odometerOf ω t x} :=
    measurableSet_lt measurable_const (measurable_odometerOf t x)
  have hsub : MeasurableSet {ω : Site d → ℝ |
      Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1 ⊆ {x | s < odometerOf ω t x}} := by
    have he : {ω : Site d → ℝ |
        Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1 ⊆ {x | s < odometerOf ω t x}} =
        ⋂ x ∈ Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1,
          {ω | s < odometerOf ω t x} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.subset_def]
    rw [he]
    exact MeasurableSet.iInter (fun x => MeasurableSet.iInter (fun _ => hO x))
  exact hsub.inter (measurableSet_infinite_componentIn
    (fun ω => {x | s < odometerOf ω t x}) hO 0)

/-- If the unit box about the origin clears level `m/2` but the origin's component stays finite,
then some annulus around the origin carries a low-crossing event at scale `64^n`, by the
blocking-to-crossing dichotomy `Frozen.dgt4_blocking_to_crossing`. -/
lemma blocked_odometer_subset_annular_union (hBoundary : External.ExteriorBoundaryConnected)
    {d : ℕ} (hd : 5 ≤ d) (t : ℕ) (m : ℝ) :
    {ω : Site d → ℝ | Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1 ⊆
        {x | m / 2 < odometerOf ω t x} ∧
      ¬ (LatticeProb.componentIn {x | m / 2 < odometerOf ω t x} (0 : Site d)).Infinite} ⊆
      ⋃ n : ℕ, ⋃ x ∈ boxFinset (0 : Site d) (4 * 64 ^ (n + 1)),
        Frozen.DGT4Cascade.lowCrossingEvent t m x ((64 : ℝ) ^ n) (m / 2) := by
  rintro ω ⟨hS, hi⟩
  obtain ⟨n, x, hx, T, hT, hTc, hin, hout⟩ :=
    Frozen.dgt4_blocking_to_crossing hBoundary d hd _ hS hi
  have hx' : x ∈ boxFinset (0 : Site d) (4 * 64 ^ (n + 1)) := by
    apply mem_boxFinset
    rw [boxDist_comm]
    change (boxDist x 0 : ℝ) ≤ 4 * (64 : ℝ) ^ (n + 1) at hx
    exact_mod_cast hx
  refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx', ?_⟩⟩⟩
  refine ⟨T, fun y hy => ⟨(hT hy).2, ?_⟩, hTc, hin, hout⟩
  have hh : ¬ m / 2 < odometerOf ω t y := (hT hy).1
  change odometerOf ω t y - m ≤ -(m / 2)
  linarith [not_lt.mp hh]

/-- The number of centers `x` with `boxDist 0 x ≤ 4 · 64^(n+1)` is at most `9^d · (64^d)^(n+1)`. -/
lemma card_annular_centers_le (d n : ℕ) :
    ((boxFinset (0 : Site d) (4 * 64 ^ (n + 1))).card : ℝ) ≤
      (9 : ℝ) ^ d * ((64 : ℝ) ^ d) ^ (n + 1) := by
  rw [card_boxFinset]
  push_cast
  have hR : 1 ≤ (64 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
  calc
    (2 * (4 * (64 : ℝ) ^ (n + 1)) + 1) ^ d ≤ (9 * (64 : ℝ) ^ (n + 1)) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]

/-- Given a uniform bound `hcross` on each scale-`64^n` annular low-crossing probability by
`C exp(-b m 2^n)`, the probability of the blocked event (unit box clears `m/2` but the origin's
component is finite) is at most the sum over scales of that bound times the number of centers
at that scale, via `blocked_odometer_subset_annular_union` and `card_annular_centers_le`. -/
lemma measure_blocked_odometer_le (hBoundary : External.ExteriorBoundaryConnected)
    {d : ℕ} (hd : 5 ≤ d) (ν : Measure ℝ) (t : ℕ) (m b C : ℝ) (hC : 0 ≤ C)
    (hcross : ∀ n : ℕ, (⨆ x : Site d, (LatticeProb.iidLaw d ν)
        (Frozen.DGT4Cascade.lowCrossingEvent t m x ((64 : ℝ) ^ n) (m / 2))) ≤
      ENNReal.ofReal (C * Real.exp (-(b * m * (2 : ℝ) ^ n)))) :
    (LatticeProb.iidLaw d ν) {ω : Site d → ℝ |
      Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1 ⊆ {x | m / 2 < odometerOf ω t x} ∧
      ¬ (LatticeProb.componentIn {x | m / 2 < odometerOf ω t x} (0 : Site d)).Infinite} ≤
        ∑' n : ℕ, ENNReal.ofReal ((9 ^ d * C) * ((64 : ℝ) ^ d) ^ (n + 1) *
          Real.exp (-(b * m * (2 : ℝ) ^ n))) := by
  calc
    _ ≤ (LatticeProb.iidLaw d ν) (⋃ n : ℕ, ⋃ x ∈ boxFinset (0 : Site d) (4 * 64 ^ (n + 1)),
        Frozen.DGT4Cascade.lowCrossingEvent t m x ((64 : ℝ) ^ n) (m / 2)) :=
      measure_mono (blocked_odometer_subset_annular_union hBoundary hd t m)
    _ ≤ ∑' n : ℕ, (LatticeProb.iidLaw d ν) (⋃ x ∈ boxFinset (0 : Site d) (4 * 64 ^ (n + 1)),
        Frozen.DGT4Cascade.lowCrossingEvent t m x ((64 : ℝ) ^ n) (m / 2)) := measure_iUnion_le _
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        _ ≤ ∑ x ∈ boxFinset (0 : Site d) (4 * 64 ^ (n + 1)), (LatticeProb.iidLaw d ν)
            (Frozen.DGT4Cascade.lowCrossingEvent t m x ((64 : ℝ) ^ n) (m / 2)) :=
          measure_biUnion_finset_le _ _
        _ ≤ ∑ _x ∈ boxFinset (0 : Site d) (4 * 64 ^ (n + 1)),
            ENNReal.ofReal (C * Real.exp (-(b * m * (2 : ℝ) ^ n))) :=
          Finset.sum_le_sum (fun x _ => (le_iSup _ x).trans (hcross n))
        _ = ENNReal.ofReal (((boxFinset (0 : Site d) (4 * 64 ^ (n + 1))).card : ℝ) *
            (C * Real.exp (-(b * m * (2 : ℝ) ^ n)))) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
            Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hh := mul_le_mul_of_nonneg_right (card_annular_centers_le d n)
            (show 0 ≤ C * Real.exp (-(b * m * (2 : ℝ) ^ n)) by positivity)
          nlinarith

/-- Given a per-site concentration bound `hpoint` on `|odometerOf ω t x - m| ≥ m/2` by
`C exp(-bm)`, the probability that the unit box about the origin fails to clear level `m/2`
somewhere is at most `3^d C exp(-bm)`, by a union bound over the `3^d` sites of the box. -/
lemma measure_unit_box_failure_le {d : ℕ} (ν : Measure ℝ) (t : ℕ) (m b C : ℝ)
    (hC : 0 ≤ C)
    (hpoint : ∀ x : Site d, (LatticeProb.iidLaw d ν)
      {ω | m / 2 ≤ |odometerOf ω t x - m|} ≤ ENNReal.ofReal (C * Real.exp (-(b * m)))) :
    (LatticeProb.iidLaw d ν) {ω : Site d → ℝ |
      ¬ Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1 ⊆ {x | m / 2 < odometerOf ω t x}} ≤
        ENNReal.ofReal (3 ^ d * C * Real.exp (-(b * m))) := by
  have hsub : {ω : Site d → ℝ |
      ¬ Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1 ⊆ {x | m / 2 < odometerOf ω t x}} ⊆
      ⋃ x ∈ boxFinset (0 : Site d) 1, {ω | m / 2 ≤ |odometerOf ω t x - m|} := by
    intro ω hω
    obtain ⟨x, hx, hox⟩ := Set.not_subset.mp hω
    have hx' : x ∈ boxFinset (0 : Site d) 1 := by
      apply mem_boxFinset
      rw [boxDist_comm]
      change (boxDist x 0 : ℝ) ≤ 1 at hx
      exact_mod_cast hx
    refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx', ?_⟩⟩
    have hh : odometerOf ω t x ≤ m / 2 := not_lt.mp hox
    change m / 2 ≤ |odometerOf ω t x - m|
    linarith [neg_le_abs (odometerOf ω t x - m)]
  calc
    _ ≤ (LatticeProb.iidLaw d ν) (⋃ x ∈ boxFinset (0 : Site d) 1,
        {ω | m / 2 ≤ |odometerOf ω t x - m|}) := measure_mono hsub
    _ ≤ ∑ x ∈ boxFinset (0 : Site d) 1, (LatticeProb.iidLaw d ν)
        {ω | m / 2 ≤ |odometerOf ω t x - m|} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ boxFinset (0 : Site d) 1,
        ENNReal.ofReal (C * Real.exp (-(b * m))) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        Finset.sum_const, nsmul_eq_mul, card_boxFinset]
      congr 1
      push_cast
      ring

/-- **Exponential bound for failure of the origin to connect to infinity.** There are `b, C > 0`
and `M ≥ 1`, depending only on `d, θ, K`, such that whenever the mean odometer at the origin at
time `t` is at least `M`, the probability of its complementary connection event
(`odometerOriginConnectEvent`) is at most `C exp(-b · (mean odometer))`. This combines
`measure_unit_box_failure_le` and `measure_blocked_odometer_le` through the concentration bound
`exists_odometerOf_conc` and the cascade estimate `Frozen.dgt4_cascade`. -/
lemma exists_odometer_origin_connection (hBoundary : External.ExteriorBoundaryConnected)
    (hGH : External.GreenBoundsHigh) (d : ℕ) (hd : 5 ≤ d) (θ K : ℝ) (hθ : 0 < θ) :
    ∃ b C M : ℝ, 0 < b ∧ 0 < C ∧ 1 ≤ M ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        0 < evariance id ν → evariance id ν < ⊤ →
        Integrable (fun z => Real.exp (θ * |z|)) ν →
        ∫ z, Real.exp (θ * |z|) ∂ν ≤ K →
        ∀ t : ℕ, M ≤ (∫ ω, odometerOf ω t (0 : Site d) ∂(LatticeProb.iidLaw d ν)) →
          (LatticeProb.iidLaw d ν) (odometerOriginConnectEvent t
            ((∫ ω, odometerOf ω t (0 : Site d) ∂(LatticeProb.iidLaw d ν)) / 2))ᶜ ≤
              ENNReal.ofReal (C * Real.exp (-(b *
                (∫ ω, odometerOf ω t (0 : Site d) ∂(LatticeProb.iidLaw d ν))))) := by
  obtain ⟨b₀, C₀, M₀, hb₀, hC₀, hcascade⟩ := Frozen.dgt4_cascade d hd θ K hθ
  obtain ⟨b₁, C₁, hb₁, hC₁, hconc⟩ := exists_odometerOf_conc hGH hd θ K hθ
  obtain ⟨M₁, hM₁, hsum⟩ := exists_weighted_double_exp_sum_bound ((64 : ℝ) ^ d) b₀
    (one_le_pow₀ (by norm_num)) hb₀
  let b := min b₀ (b₁ / 4)
  let C := 3 ^ d * C₁ + 2 * (9 ^ d * C₀) * (64 : ℝ) ^ d
  let M := max 1 (max M₀ M₁)
  have hb : 0 < b := lt_min hb₀ (by positivity)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨b, C, M, hb, hC, le_max_left _ _, ?_⟩
  intro ν hν hmean hvar hvarfin hexp hK t hm
  letI := hν
  let m := ∫ ω, odometerOf ω t (0 : Site d) ∂(LatticeProb.iidLaw d ν)
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hm0 : 0 ≤ m := le_trans zero_le_one hm1
  have hmM₀ : M₀ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hmM₁ : M₁ ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hcr := hcascade ν hν hmean hvar hvarfin hexp hK t hmM₀
  have hblocked := (measure_blocked_odometer_le hBoundary hd ν t m b₀ C₀ hC₀.le hcr).trans
    (hsum m hmM₁ (9 ^ d * C₀) (by positivity))
  have hpoint (x : Site d) : (LatticeProb.iidLaw d ν)
      {ω | m / 2 ≤ |odometerOf ω t x - m|} ≤
        ENNReal.ofReal (C₁ * Real.exp (-(b₁ / 4 * m))) := by
    apply (hconc ν hν hexp hK x t (m / 2) (by positivity)).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC₁.le
    apply Real.exp_le_exp.mpr
    have hmin : m / 4 ≤ min ((m / 2) ^ 2) (m / 2) := by
      apply le_min <;> nlinarith [sq_nonneg (m - 1)]
    have hh := mul_le_mul_of_nonneg_left hmin hb₁.le
    nlinarith
  have hbox := measure_unit_box_failure_le ν t m (b₁ / 4) C₁ hC₁.le hpoint
  have hsub : (odometerOriginConnectEvent (d := d) t (m / 2))ᶜ ⊆
      {ω : Site d → ℝ | ¬ Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1 ⊆
        {x | m / 2 < odometerOf ω t x}} ∪
      {ω : Site d → ℝ | Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1 ⊆
        {x | m / 2 < odometerOf ω t x} ∧
        ¬ (LatticeProb.componentIn {x | m / 2 < odometerOf ω t x} (0 : Site d)).Infinite} := by
    intro ω hω
    by_cases hS : Frozen.DGT4BlockingToCrossing.boxAt (0 : Site d) 1 ⊆
        {x | m / 2 < odometerOf ω t x}
    · exact Or.inr ⟨hS, fun hi => hω ⟨hS, hi⟩⟩
    · exact Or.inl hS
  apply (measure_mono hsub).trans
    ((measure_union_le _ _).trans ((add_le_add hbox hblocked).trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he₀ : Real.exp (-(b₀ * m)) ≤ Real.exp (-(b * m)) := Real.exp_le_exp.mpr
    (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hm0))
  have he₁ : Real.exp (-(b₁ / 4 * m)) ≤ Real.exp (-(b * m)) := Real.exp_le_exp.mpr
    (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hm0))
  have hh₀ := mul_le_mul_of_nonneg_left he₀
    (show 0 ≤ 2 * (9 ^ d * C₀) * (64 : ℝ) ^ d by positivity)
  have hh₁ := mul_le_mul_of_nonneg_left he₁ (show 0 ≤ 3 ^ d * C₁ by positivity)
  dsimp only [C]
  nlinarith

/-- If the complement of `odometerOriginConnectEvent` has probability at most `r`, then the event
itself has probability at least `1 - r`. -/
lemma origin_connection_lower_of_compl_le {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (t : ℕ) (s r : ℝ) (hr : 0 ≤ r)
    (h : (LatticeProb.iidLaw d ν) (odometerOriginConnectEvent (d := d) t s)ᶜ ≤ ENNReal.ofReal r) :
    ENNReal.ofReal (1 - r) ≤ (LatticeProb.iidLaw d ν) (odometerOriginConnectEvent t s) := by
  calc
    ENNReal.ofReal (1 - r) = 1 - ENNReal.ofReal r := by rw [ENNReal.ofReal_sub 1 hr]; simp
    _ ≤ 1 - (LatticeProb.iidLaw d ν) (odometerOriginConnectEvent (d := d) t s)ᶜ :=
      tsub_le_tsub_left h 1
    _ = _ := by
      rw [← measure_univ (μ := LatticeProb.iidLaw d ν),
        ← measure_compl (measurableSet_odometerOriginConnectEvent t s).compl (measure_ne_top _ _),
        compl_compl]


end Sandpile
