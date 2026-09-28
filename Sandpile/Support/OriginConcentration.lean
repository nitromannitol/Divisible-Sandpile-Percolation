import Sandpile.Support.OriginKernel
import Sandpile.Support.OriginProfile
import LatticeProb.Prob.WeightedConc
import Sandpile.Support.Norms
import Sandpile.External.GreenBoundsHigh

/-!
# Concentration of the origin-frozen odometer average

Uniform moments and sharp exponential lower tails for the average of the origin-frozen
odometer. The finite-box coordinate representation permits the product concentration bounds,
with square-summable hitting probabilities as the bounded-difference constants
(`originInfluence`, `summable_originInfluence_sq`). The moment bound is
`exists_avg_originOdometer_moment_bound`, transferred to the scenery law in
`origin_frozen_moment_bound`, and the sharp exponential lower tail is
`exists_avg_originOdometer_lower_tail`, transferred to the scenery law in
`origin_frozen_lower_tail`.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The infinite-time Green function at the origin, `green d 0 z`, equals
`LatticeProb.srwGreenInf d z`: the paper's own Green identity `External.Sec16.green_eq`
combined with the time-reversal symmetry `LatticeProb.srwHeat_neg` of the heat kernel. -/
theorem green_origin_eq_srwGreenInf (z : Site d) : green d 0 z = LatticeProb.srwGreenInf d z := by
  rw [External.Sec16.green_eq, zero_sub, LatticeProb.srwGreenInf, LatticeProb.srwGreenInf]
  exact tsum_congr fun k => LatticeProb.srwHeat_neg k z

/-- `originInfluence z` is at most the Green ratio `green d 0 z / green d 0 0`, by unfolding
the case split in the definition of `originInfluence` and applying, via
`green_origin_eq_srwGreenInf`, the simple random walk hitting-probability identity
`LatticeProb.srwHitProb_eq_green_ratio`. -/
theorem originInfluence_le_green_ratio (hd : 3 ≤ d) (z : Site d) :
    originInfluence z ≤ green d 0 z / green d 0 0 := by
  rw [green_origin_eq_srwGreenInf, green_origin_eq_srwGreenInf,
    ← LatticeProb.srwHitProb_eq_green_ratio hd]
  unfold originInfluence
  split_ifs
  · exact LatticeProb.srwHitProb_nonneg z
  · exact le_rfl

/-- The squared origin influences are summable: `GreenBoundsHigh` gives square-summability of
the Green ratios `green d 0 z / green d 0 0`, and `originInfluence_le_green_ratio` compares
`originInfluence z ^ 2` termwise to that summable family. -/
theorem summable_originInfluence_sq (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) :
    Summable fun z : Site d => originInfluence z ^ 2 := by
  have hg := ((hGH d hd).2.1).div_const (green d 0 0 ^ 2)
  have hgr : Summable fun z : Site d => (green d 0 z / green d 0 0) ^ 2 := by
    simpa only [div_pow] using hg
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun z => ?_) hgr
  exact pow_le_pow_left₀ (originInfluence_nonneg z) (originInfluence_le_green_ratio (by omega) z) 2

/-- A uniform bound `B` on the hitting probabilities `LatticeProb.srwHitProb d z` at every
`z ≠ 0` transfers to the same bound `B` on `originInfluence z` for every `z`, by unfolding the
case split in the definition of `originInfluence`. -/
theorem originInfluence_le_sup {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z : Site d, z ≠ 0 → LatticeProb.srwHitProb d z ≤ B) (z : Site d) :
    originInfluence z ≤ B := by
  unfold originInfluence
  split_ifs with hz
  · exact hB
  · exact hbound z hz

/-- `localizedOdometer D ζ n x` depends on the scenery `ζ` only through its values on the box
`boxFinset x n`: if two sceneries agree there, the bounded-difference estimate
`abs_localizedOdometer_sub_le` forces the localized odometer values to be exactly equal. -/
theorem localizedOdometer_congr_box (hd : 1 ≤ d) (D : Set (Site d)) (n : ℕ) (x : Site d)
    (ζ η : Site d → ℝ) (he : ∀ z ∈ boxFinset x n, ζ z = η z) :
    localizedOdometer D ζ n x = localizedOdometer D η n x := by
  have h := abs_localizedOdometer_sub_le hd D ζ η n x
  have hs : ∑ z ∈ boxFinset x n, |ζ z - η z| = 0 :=
    Finset.sum_eq_zero fun z hz => by rw [he z hz, sub_self, abs_zero]
  rw [hs, mul_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- `avg (originOdometer ζ n) 0` depends on `ζ` only through its values on the enlarged box
`boxFinset 0 (n + 1)`: the neighbor average at the origin reads `originOdometer` at the `2d`
unit-distance sites, each of which lies within distance `1` of the origin, so
`localizedOdometer_congr_box` applies at each of them. -/
theorem avg_originOdometer_congr_box (hd : 1 ≤ d) (n : ℕ) (ζ η : Site d → ℝ)
    (he : ∀ z ∈ boxFinset (0 : Site d) (n + 1), ζ z = η z) :
    avg (originOdometer ζ n) 0 = avg (originOdometer η n) 0 := by
  have hnbr : ∀ x : Site d, boxDist 0 x ≤ 1 → originOdometer ζ n x = originOdometer η n x := by
    intro x hx
    refine localizedOdometer_congr_box hd _ n x ζ η fun z hz => he z ?_
    have hd0 := boxDist_trans (0 : Site d) x z
    have hn := mem_boxFinset_iff.mp hz
    exact mem_boxFinset (by omega)
  unfold avg LatticeProb.walkOp LatticeProb.nbrSum
  congr 1
  exact Finset.sum_congr rfl fun i _ => congrArg₂ (· + ·)
    (hnbr _ (boxDist_add_unit 0 i)) (hnbr _ (boxDist_sub_unit 0 i))

/-- The origin-averaged odometer at time `n`, read as a function of the finitely many
coordinates `ξ` indexing the enlarged box `boxFinset 0 (n + 1)`, by extending `ξ` to a full
scenery with `siteExtend` before evaluating `avg (originOdometer · n) 0`. -/
noncomputable def boxOriginAverage (n : ℕ)
    (ξ : Fin (boxFinset (0 : Site d) (n + 1)).card → ℝ) : ℝ :=
  avg (originOdometer (siteExtend (boxFinset (0 : Site d) (n + 1)) ξ) n) 0

/-- `boxOriginAverage n` is measurable, being the composite of the measurable extension map
`siteExtend` and the measurable averaged odometer `measurable_avg_originOdometer`. -/
theorem measurable_boxOriginAverage (hd : 1 ≤ d) (n : ℕ) :
    Measurable (boxOriginAverage (d := d) n) :=
  (measurable_avg_originOdometer hd n).comp (measurable_siteExtend _)

/-- `boxOriginAverage` evaluated at the coordinates a full scenery `ζ` takes on `boxFinset 0
(n + 1)` recovers `avg (originOdometer ζ n) 0` exactly, since `siteExtend` composed with
`siteEnum` restores `ζ`'s values on that box and `avg_originOdometer_congr_box` sees only
those values. -/
theorem boxOriginAverage_pick (hd : 1 ≤ d) (n : ℕ) (ζ : Site d → ℝ) :
    boxOriginAverage n (fun i => ζ (siteEnum (boxFinset (0 : Site d) (n + 1)) i)) =
      avg (originOdometer ζ n) 0 :=
  avg_originOdometer_congr_box hd n _ ζ fun _ hz => siteExtend_siteEnum _ ζ hz

/-- **The bounded-difference constant of `boxOriginAverage` at coordinate `i` is
`originInfluence (siteEnum ... i)`.**  Changing the `i`-th coordinate of `ξ` from `ξ i` to `v`
moves `boxOriginAverage n ξ` by at most that influence times `|ξ i - v|`, transported from the
scenery-level bound `abs_avg_originOdometer_update_le` through `siteExtend`. -/
theorem abs_boxOriginAverage_update_le (hd : 1 ≤ d) (n : ℕ)
    (ξ : Fin (boxFinset (0 : Site d) (n + 1)).card → ℝ)
    (i : Fin (boxFinset (0 : Site d) (n + 1)).card) (v : ℝ) :
    |boxOriginAverage n ξ - boxOriginAverage n (Function.update ξ i v)| ≤
      originInfluence (siteEnum (boxFinset (0 : Site d) (n + 1)) i) * |ξ i - v| := by
  have h := abs_avg_originOdometer_update_le hd
    (siteExtend (boxFinset (0 : Site d) (n + 1)) ξ)
    (siteEnum (boxFinset (0 : Site d) (n + 1)) i) v n
  have hv : siteExtend (boxFinset (0 : Site d) (n + 1)) ξ
      (siteEnum (boxFinset (0 : Site d) (n + 1)) i) = ξ i := by
    simp [siteExtend, siteEnum]
  simpa only [boxOriginAverage, siteExtend_update, hv] using h

/-- **A `p`-th moment bound on the centered origin-averaged odometer, uniform in the time
`n`.**  `boxOriginAverage n` is a function of finitely many i.i.d. coordinates with
bounded-difference constants `originInfluence (siteEnum s ·)` (`abs_boxOriginAverage_update_le`),
so the product moment inequality `exists_pick_moment_bound` bounds its centered `p`-th moment
by a constant times the `p/2`-th power of the sum of squared constants, uniformly bounded by
`summable_originInfluence_sq`. -/
theorem exists_avg_originOdometer_moment_bound (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ} (hp : 2 ≤ p)
    (hmom : Integrable (fun z => |z| ^ p) ν) :
    ∃ M : ℝ, ∀ n : ℕ,
      ∫ ζ, |avg (originOdometer ζ n) 0 -
          ∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν| ^ p
        ∂LatticeProb.iidLaw d ν ≤ M := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC, hb⟩ := exists_pick_moment_bound (d := d) hp
  refine ⟨C * pairMoment ν p * (∑' z : Site d, originInfluence z ^ 2) ^ (p / 2), ?_⟩
  intro n
  set s := boxFinset (0 : Site d) (n + 1)
  have h := hb ν inferInstance hmom s.card (siteEnum s) (siteEnum_injective s)
    (boxOriginAverage n) (measurable_boxOriginAverage hd1 n)
    (fun i => originInfluence (siteEnum s i)) (fun _ => originInfluence_nonneg _)
    (abs_boxOriginAverage_update_le hd1 n)
  simp only [s, boxOriginAverage_pick hd1 n] at h
  refine h.trans ?_
  have hsum : (∑ i : Fin s.card, originInfluence (siteEnum s i) ^ 2) ≤
      ∑' z : Site d, originInfluence z ^ 2 := by
    rw [sum_siteEnum s (fun z => originInfluence z ^ 2)]
    exact (summable_originInfluence_sq hGH hd).sum_le_tsum s (fun _ _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => sq_nonneg _) hsum (by linarith))
    (mul_nonneg hC.le (pairMoment_nonneg ν p))

/-- **A uniform-in-`n` exponential moment bound on the centered origin-averaged odometer.**
Provided the tilt `lam` satisfies `|lam| * B < θ`, where `B` bounds the hitting probabilities
away from the origin and `θ` is the exponential-moment rate of `ν`, the product concentration
bound `exp_conc_pi` applied to `boxOriginAverage n` with bounded-difference constants
`originInfluence (siteEnum s ·)` gives an exponential moment bound uniform in `n`, since the
sum of squared constants is uniformly controlled by `summable_originInfluence_sq`. -/
theorem exists_avg_originOdometer_exp_bound (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] {θ B lam : ℝ}
    (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hB : 0 ≤ B) (hbound : ∀ z : Site d, z ≠ 0 → LatticeProb.srwHitProb d z ≤ B)
    (hgap : |lam| * B < θ) :
    ∃ C : ℝ, ∀ n : ℕ,
      Integrable (fun ζ => Real.exp (lam * (avg (originOdometer ζ n) 0 -
        ∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν))) (LatticeProb.iidLaw d ν) ∧
      ∫ ζ, Real.exp (lam * (avg (originOdometer ζ n) 0 -
        ∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν)) ∂LatticeProb.iidLaw d ν ≤ C := by
  have hd1 : 1 ≤ d := by omega
  set K := ∫ z, Real.exp (θ * |z|) ∂ν
  set δ := θ - |lam| * B
  have hδ : 0 < δ := sub_pos.mpr hgap
  have hδθ : δ ≤ θ := sub_le_self _ (mul_nonneg (abs_nonneg _) hB)
  set A := 4 * (Real.exp K * K) / δ ^ 2 * lam ^ 2
  have hA : 0 ≤ A := by
    have hK : 0 ≤ K := integral_nonneg fun _ => Real.exp_nonneg _
    positivity
  refine ⟨Real.exp (A * ∑' z : Site d, originInfluence z ^ 2), ?_⟩
  intro n
  set s := boxFinset (0 : Site d) (n + 1)
  set F := boxOriginAverage (d := d) n
  set ℓ := fun i : Fin s.card => originInfluence (siteEnum s i)
  have hLip := abs_boxOriginAverage_update_le hd1 n
  have hℓ : ∀ i, |lam| * ℓ i ≤ θ - δ := by
    intro i
    have h := mul_le_mul_of_nonneg_left
      (originInfluence_le_sup hB hbound (siteEnum s i)) (abs_nonneg lam)
    dsimp [δ]
    linarith
  have hi := integrable_exp_lip ν θ hexp F (measurable_boxOriginAverage hd1 n) ℓ hLip lam
    (fun i => (hℓ i).trans (by dsimp [δ]; linarith [mul_nonneg (abs_nonneg lam) hB]))
    (∫ ξ, F ξ ∂Measure.pi (fun _ : Fin s.card => ν))
  have hb := exp_conc_pi ν θ K δ hθ hδ hδθ hexp le_rfl lam s.card F
    (measurable_boxOriginAverage hd1 n) ℓ (fun _ => originInfluence_nonneg _) hLip hℓ
  have hm : (∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν) =
      ∫ ξ, F ξ ∂Measure.pi (fun _ : Fin s.card => ν) := by
    rw [← integral_pick ν (siteEnum s) (siteEnum_injective s) F
      (measurable_boxOriginAverage hd1 n).aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun ζ => (boxOriginAverage_pick hd1 n ζ).symm)
  have hmp := LatticeProb.measurePreserving_pick _ ν (siteEnum s) (siteEnum_injective s)
  constructor
  · have hi' := hmp.integrable_comp_of_integrable hi
    simpa only [Function.comp_def, F, s, boxOriginAverage_pick hd1 n, hm] using hi'
  · rw [hm]
    have he := integral_pick ν (siteEnum s) (siteEnum_injective s)
      (fun ξ => Real.exp (lam * (F ξ - ∫ η, F η ∂Measure.pi (fun _ : Fin s.card => ν))))
      hi.aestronglyMeasurable
    have hsum : (∑ i : Fin s.card, ℓ i ^ 2) ≤ ∑' z : Site d, originInfluence z ^ 2 := by
      rw [show (∑ i : Fin s.card, ℓ i ^ 2) = ∑ z ∈ s, originInfluence z ^ 2 from
        sum_siteEnum s (fun z => originInfluence z ^ 2)]
      exact (summable_originInfluence_sq hGH hd).sum_le_tsum s (fun _ _ => sq_nonneg _)
    have hh := hb.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum hA))
    rw [← he] at hh
    simpa only [F, s, boxOriginAverage_pick hd1 n] using hh

/-- **A sharp exponential lower tail for the centered origin-averaged odometer.**  Applying the
exponential moment bound `exists_avg_originOdometer_exp_bound` at the tilt `-lam` and then the
Chernoff bound `measure_ge_le_exp_mul_mgf` gives a bound `C·exp(-lam·r)` on the probability
that the centered average falls below `-r`, uniform in the time `n`. -/
theorem exists_avg_originOdometer_lower_tail (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] {θ B lam : ℝ}
    (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hB : 0 ≤ B) (hbound : ∀ z : Site d, z ≠ 0 → LatticeProb.srwHitProb d z ≤ B)
    (hlam : 0 < lam) (hgap : lam * B < θ) :
    ∃ C : ℝ, ∀ (n : ℕ) (r : ℝ),
      LatticeProb.iidLaw d ν {ζ | avg (originOdometer ζ n) 0 -
          ∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν ≤ -r} ≤
        ENNReal.ofReal (C * Real.exp (-(lam * r))) := by
  obtain ⟨C, hC⟩ := exists_avg_originOdometer_exp_bound hGH hd ν hθ hexp hB hbound
    (lam := -lam) (by simpa only [abs_neg, abs_of_pos hlam] using hgap)
  refine ⟨C, ?_⟩
  intro n r
  set X := fun ζ : Site d → ℝ => -(avg (originOdometer ζ n) 0 -
    ∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν)
  have hi : Integrable (fun ζ => Real.exp (lam * X ζ)) (LatticeProb.iidLaw d ν) := by
    simpa only [X, mul_neg, neg_mul] using (hC n).1
  have hm : mgf X (LatticeProb.iidLaw d ν) lam ≤ C := by
    simpa only [mgf, X, mul_neg, neg_mul] using (hC n).2
  have hch := measure_ge_le_exp_mul_mgf (μ := LatticeProb.iidLaw d ν) (X := X) r hlam.le hi
  have he : {ζ : Site d → ℝ | r ≤ X ζ} = {ζ | avg (originOdometer ζ n) 0 -
      ∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν ≤ -r} := by
    ext ζ
    simp only [X, Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [he] at hch
  apply measure_le_ofReal
  have hb := mul_le_mul_of_nonneg_left hm (Real.exp_nonneg (-lam * r))
  refine hch.trans (hb.trans_eq ?_)
  rw [neg_mul, mul_comm]

/-- The moment bound `exists_avg_originOdometer_moment_bound` transported from the i.i.d.
scenery law to the origin-frozen `centeredMassLaw`, via the change-of-variables identity
`integral_scenery`. -/
theorem origin_frozen_moment_bound (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ} (hp : 2 ≤ p)
    (hmom : Integrable (fun z => |z| ^ p) ν) :
    ∃ M : ℝ, ∀ n : ℕ,
      ∫ σ, |avg (originOdometer (scenery d σ) n) 0 -
          ∫ σ', avg (originOdometer (scenery d σ') n) 0 ∂centeredMassLaw d ν| ^ p
        ∂centeredMassLaw d ν ≤ M := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨M, hM⟩ := exists_avg_originOdometer_moment_bound hGH hd ν hp hmom
  refine ⟨M, fun n => ?_⟩
  have hme := measurable_avg_originOdometer hd1 n
  rw [integral_scenery d ν hd1 (F := fun ζ => avg (originOdometer ζ n) 0) hme.aestronglyMeasurable,
    integral_scenery d ν hd1 (F := fun ζ => |avg (originOdometer ζ n) 0 -
      ∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν| ^ p)
        ((hme.sub measurable_const).abs.pow_const p).aestronglyMeasurable]
  exact hM n

/-- The lower-tail bound `exists_avg_originOdometer_lower_tail` transported from the i.i.d.
scenery law to the origin-frozen `centeredMassLaw`, via the preimage identity
`centeredMassLaw_scenery_preimage`. -/
theorem origin_frozen_lower_tail (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] {θ B lam : ℝ}
    (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hB : 0 ≤ B) (hbound : ∀ z : Site d, z ≠ 0 → LatticeProb.srwHitProb d z ≤ B)
    (hlam : 0 < lam) (hgap : lam * B < θ) :
    ∃ C : ℝ, ∀ (n : ℕ) (r : ℝ),
      centeredMassLaw d ν {σ | avg (originOdometer (scenery d σ) n) 0 -
          ∫ σ', avg (originOdometer (scenery d σ') n) 0 ∂centeredMassLaw d ν ≤ -r} ≤
        ENNReal.ofReal (C * Real.exp (-(lam * r))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC⟩ := exists_avg_originOdometer_lower_tail hGH hd ν hθ hexp hB hbound hlam hgap
  refine ⟨C, fun n r => ?_⟩
  have hme := measurable_avg_originOdometer hd1 n
  rw [integral_scenery d ν hd1 (F := fun ζ => avg (originOdometer ζ n) 0) hme.aestronglyMeasurable]
  have hs : MeasurableSet {ζ : Site d → ℝ | avg (originOdometer ζ n) 0 -
      ∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν ≤ -r} :=
    measurableSet_le (hme.sub measurable_const) measurable_const
  have htr := centeredMassLaw_scenery_preimage d ν hd1 hs
  change centeredMassLaw d ν {σ | avg (originOdometer (scenery d σ) n) 0 -
      ∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν ≤ -r} = _ at htr
  rw [htr]
  exact hC n r

end Sandpile
