/-
The Kolmogorov condition of the Gaussian heat potential on a time strip.

The frozen statements of `ssec:scaling-dlt4` quantify over a field `Z` that is a
modification of `eq:dlt4-linear-gaussian-potential`, almost surely continuous on
every strip `[0,T] × ℝ^d`.  The paper fixes that version at
`sandpile.tex:1019-1021` and cites nothing for it; this module produces it.

The increment of the potential is a centred Gaussian whose variance is the `L²`
increment of the Green kernel, and `MeanAIncrement` bounds that by a quarter
power of the space-time distance on the strip.  A moment of order `8(d+2)`
therefore obeys the Kolmogorov condition with exponent `d+2`, which is above the
`d+1` the multi-parameter Kolmogorov-Chentsov theorem asks for.  The time is
clamped to the strip so that the condition holds at every pair of points of
`ℝ × ℝ^d`, not only at the pairs inside the strip; clamping is one-Lipschitz, so
it does not spoil the bound, and it is the identity on the strip, so the field it
produces is the potential there.
-/
import Sandpile.Support.MeanAGauss
import Sandpile.Support.ExplFieldEvent
import LatticeProb.Prob.ChentsovPiModification

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The time clamped to the strip `[0,T]`. -/
noncomputable def clampTimeK (T t : ℝ) : ℝ := max 0 (min t T)

theorem clampTimeK_nonneg (T t : ℝ) : 0 ≤ clampTimeK T t := le_max_left _ _

theorem clampTimeK_le {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampTimeK T t ≤ T :=
  max_le hT (min_le_right _ _)

theorem clampTimeK_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampTimeK T t ∈ Set.Icc (0 : ℝ) T :=
  ⟨clampTimeK_nonneg T t, clampTimeK_le hT t⟩

theorem clampTimeK_eq_self {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) : clampTimeK T t = t := by
  rw [clampTimeK, min_eq_left htT, max_eq_right ht]

/-- Clamping does not increase distances. -/
theorem abs_clampTimeK_sub_le (T t s : ℝ) : |clampTimeK T t - clampTimeK T s| ≤ |t - s| := by
  have h1 : |min t T - min s T| ≤ |t - s| := by
    refine le_trans (abs_min_sub_min_le_max t T s T) ?_
    exact max_le le_rfl (by simp)
  have h2 : |max 0 (min t T) - max 0 (min s T)| ≤ |min t T - min s T| := by
    refine le_trans (abs_max_sub_max_le_max (0 : ℝ) (min t T) 0 (min s T)) ?_
    exact max_le (by simp) le_rfl
  exact le_trans h2 h1

/-- The Gaussian heat potential as a process indexed by `ℝ × (Fin d → ℝ)`, with
the time clamped to the strip `[0,T]`. -/
noncomputable def potStrip {ΩW : Type*} (d : ℕ) (ν2 : ℝ) (W : (Space d → ℝ) → ΩW → ℝ)
    (T : ℝ) : ℝ × (Fin d → ℝ) → ΩW → ℝ :=
  fun z ω => gaussianPotential d ν2 W (clampTimeK T z.1) (WithLp.toLp 2 z.2) ω

/-- The Euclidean norm on `ℝ^d` is bounded by a multiple of the sup norm. -/
theorem exists_toLp_norm_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ a b : Fin d → ℝ,
      ‖(WithLp.toLp 2 a : Space d) - WithLp.toLp 2 b‖ ≤ K * dist a b := by
  refine ⟨Real.sqrt d, ?_, ?_⟩
  · have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    simpa using Real.sqrt_le_sqrt this
  · intro a b
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hdist : (0 : ℝ) ≤ dist a b := dist_nonneg
    have hnorm : ‖(WithLp.toLp 2 a : Space d) - WithLp.toLp 2 b‖
        = Real.sqrt (∑ i : Fin d, (a i - b i) ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    have hbd : ∑ i : Fin d, (a i - b i) ^ 2 ≤ (d : ℝ) * dist a b ^ 2 := by
      have hterm : ∀ i : Fin d, (a i - b i) ^ 2 ≤ dist a b ^ 2 := by
        intro i
        have h := dist_le_pi_dist a b i
        rw [Real.dist_eq] at h
        nlinarith [abs_nonneg (a i - b i), sq_abs (a i - b i), h, hdist]
      calc ∑ i : Fin d, (a i - b i) ^ 2 ≤ ∑ _i : Fin d, dist a b ^ 2 :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = (d : ℝ) * dist a b ^ 2 := by simp
    refine le_trans (Real.sqrt_le_sqrt hbd) (le_of_eq ?_)
    rw [Real.sqrt_mul hd0, Real.sqrt_sq hdist]

/-- **The Kolmogorov condition of the Gaussian heat potential on a strip.**  The
moment of order `8(d+2)` of an increment is bounded by the `d+2` power of the
space-time distance, an exponent above the `d+1` of the index space. -/
theorem exists_isKolmogorovProcess_potStrip (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2)
    {T : ℝ} (hT : 0 < T) {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW) :
    ∃ M : ℝ≥0, IsKolmogorovProcess (potStrip d ν2 W T) PW
      (8 * ((d : ℝ) + 2)) ((d : ℝ) + 2) M := by
  obtain ⟨MH, hMH0, hMH⟩ := exists_greenTimeBM_holder hd hd3 hT
  obtain ⟨KL, hKL1, hKL⟩ := exists_toLp_norm_bound d hd
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  set p : ℝ := 8 * ((d : ℝ) + 2) with hpdef
  set q : ℝ := (d : ℝ) + 2 with hqdef
  have hp : 0 < p := by rw [hpdef]; linarith
  have hq : 0 < q := by rw [hqdef]; linarith
  have hKL0 : (0 : ℝ) ≤ KL := by linarith
  set base : ℝ := ν2 * MH * KL ^ ((1 : ℝ) / 4) with hbase
  have hbase0 : 0 ≤ base := by
    rw [hbase]
    exact mul_nonneg (mul_nonneg hν2 hMH0) (Real.rpow_nonneg hKL0 _)
  set Kc : ℝ := gaussAbsMoment p * base ^ (p / 2) with hKc
  have hKc0 : 0 ≤ Kc :=
    mul_nonneg (gaussAbsMoment_nonneg p) (Real.rpow_nonneg hbase0 _)
  refine ⟨Real.toNNReal Kc, ?_⟩
  have hmeas : ∀ z : ℝ × (Fin d → ℝ), Measurable (potStrip d ν2 W T z) := fun z =>
    (hW.meas _ (memLp_greenTimeBM hd hd3 (clampTimeK_nonneg T z.1) _)).const_mul _
  refine IsKolmogorovProcess.mk_of_secondCountableTopology hmeas (fun u v => ?_) hp hq
  set t : ℝ := clampTimeK T u.1 with htdef
  set s : ℝ := clampTimeK T v.1 with hsdef
  set x : Space d := WithLp.toLp 2 u.2 with hxdef
  set y : Space d := WithLp.toLp 2 v.2 with hydef
  have ht : t ∈ Set.Icc (0 : ℝ) T := clampTimeK_mem hT.le u.1
  have hs : s ∈ Set.Icc (0 : ℝ) T := clampTimeK_mem hT.le v.1
  have hL := hMH t ht s hs x y
  have hL0 : (0 : ℝ) ≤ ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2 :=
    integral_nonneg fun w => by positivity
  have hDle : max |t - s| ‖x - y‖ ≤ KL * dist u v := by
    refine max_le ?_ ?_
    · calc |t - s| ≤ |u.1 - v.1| := abs_clampTimeK_sub_le T u.1 v.1
        _ = dist u.1 v.1 := (Real.dist_eq _ _).symm
        _ ≤ dist u v := by rw [Prod.dist_eq]; exact le_max_left _ _
        _ ≤ KL * dist u v := le_mul_of_one_le_left dist_nonneg hKL1
    · calc ‖x - y‖ ≤ KL * dist u.2 v.2 := hKL u.2 v.2
        _ ≤ KL * dist u v := by
            refine mul_le_mul_of_nonneg_left ?_ hKL0
            rw [Prod.dist_eq]; exact le_max_right _ _
  have hbound : ∫ ω, |potStrip d ν2 W T u ω - potStrip d ν2 W T v ω| ^ p ∂PW
      ≤ Kc * dist u v ^ q := by
    have heq : (fun ω => |potStrip d ν2 W T u ω - potStrip d ν2 W T v ω| ^ p)
        = fun ω => |gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω| ^ p := rfl
    rw [heq, integral_abs_rpow_gaussianPotential_sub PW W hW hd hd3 hν2 ht.1 hs.1 x y hp.le]
    have h1 : ν2 * (∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2)
        ≤ base * dist u v ^ ((1 : ℝ) / 4) := by
      have hstep2 : (max |t - s| ‖x - y‖) ^ ((1 : ℝ) / 4) ≤ (KL * dist u v) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (le_trans (abs_nonneg _) (le_max_left _ _)) hDle (by norm_num)
      have hsplit : (KL * dist u v) ^ ((1 : ℝ) / 4)
          = KL ^ ((1 : ℝ) / 4) * dist u v ^ ((1 : ℝ) / 4) :=
        Real.mul_rpow hKL0 dist_nonneg
      rw [hsplit] at hstep2
      have hchain : (∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2)
          ≤ MH * (KL ^ ((1 : ℝ) / 4) * dist u v ^ ((1 : ℝ) / 4)) :=
        le_trans hL (mul_le_mul_of_nonneg_left hstep2 hMH0)
      have := mul_le_mul_of_nonneg_left hchain hν2
      rw [hbase]
      linarith [this]
    have h2 : (ν2 * ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2) ^ (p / 2)
        ≤ (base * dist u v ^ ((1 : ℝ) / 4)) ^ (p / 2) :=
      Real.rpow_le_rpow (mul_nonneg hν2 hL0) h1 (by positivity)
    have h3 : (base * dist u v ^ ((1 : ℝ) / 4)) ^ (p / 2) = base ^ (p / 2) * dist u v ^ q := by
      rw [Real.mul_rpow hbase0 (Real.rpow_nonneg dist_nonneg _),
        ← Real.rpow_mul dist_nonneg]
      congr 2
      rw [hpdef, hqdef]; ring
    rw [h3] at h2
    have hm0 := gaussAbsMoment_nonneg p
    rw [hKc]
    have hdq : (0 : ℝ) ≤ dist u v ^ q := Real.rpow_nonneg (dist_nonneg (x := u) (y := v)) q
    nlinarith [h2, hm0, hdq]
  have hint : Integrable
      (fun ω => |potStrip d ν2 W T u ω - potStrip d ν2 W T v ω| ^ p) PW :=
    integrable_abs_rpow_gaussianPotential_sub PW W hW hd hd3 hν2 ht.1 hs.1 x y hp
  have hlin : ∫⁻ ω, edist (potStrip d ν2 W T u ω) (potStrip d ν2 W T v ω) ^ p ∂PW
      = ENNReal.ofReal (∫ ω, |potStrip d ν2 W T u ω - potStrip d ν2 W T v ω| ^ p ∂PW) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p)]
    refine lintegral_congr fun ω => ?_
    rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
  rw [hlin]
  calc ENNReal.ofReal (∫ ω, |potStrip d ν2 W T u ω - potStrip d ν2 W T v ω| ^ p ∂PW)
      ≤ ENNReal.ofReal (Kc * dist u v ^ q) := ENNReal.ofReal_le_ofReal hbound
    _ = (Real.toNNReal Kc : ℝ≥0∞) * edist u v ^ q := by
        rw [ENNReal.ofReal_mul hKc0,
          ← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg (x := u) (y := v)) hq.le, ← edist_dist]
        rfl

/-- **The potential has a version whose every path is continuous on the whole of
`ℝ × ℝ^d` and which is the potential on the strip `[0,T]`.** -/
theorem exists_version_continuous_on_strip (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2)
    {T : ℝ} (hT : 0 < T) {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW) :
    ∃ Y : ℝ × (Fin d → ℝ) → ΩW → ℝ,
      (∀ z : ℝ × (Fin d → ℝ), z.1 ∈ Set.Icc (0 : ℝ) T →
        Y z =ᵐ[PW] fun ω => gaussianPotential d ν2 W z.1 (WithLp.toLp 2 z.2) ω) ∧
      (∀ ω, Continuous fun z => Y z ω) := by
  obtain ⟨M, hM⟩ := exists_isKolmogorovProcess_potStrip hd hd3 hν2 hT PW W hW
  have hq : ((d : ℝ) + 1) < (d : ℝ) + 2 := by linarith
  obtain ⟨Y, -, hYmod, hYcont⟩ :=
    LatticeProb.exists_continuous_modification_spaceTime_all hM hq
  refine ⟨Y, fun z hz => ?_, hYcont⟩
  have h := (hYmod z).symm
  have heq : potStrip d ν2 W T z
      = fun ω => gaussianPotential d ν2 W z.1 (WithLp.toLp 2 z.2) ω := by
    funext ω
    show gaussianPotential d ν2 W (clampTimeK T z.1) (WithLp.toLp 2 z.2) ω
      = gaussianPotential d ν2 W z.1 (WithLp.toLp 2 z.2) ω
    rw [clampTimeK_eq_self hz.1 hz.2]
  rwa [heq] at h

/-- **The Gaussian heat potential has a continuous version.**  This is the field
`Z` of `sandpile.tex:1019-1021`: a modification of
`eq:dlt4-linear-gaussian-potential` whose paths are almost surely continuous on
every strip `[0,T] × ℝ^d`.  The versions built on the strips `[0,n+1]` are
indistinguishable on the smaller strips, so reading the version of the strip
above the time gives one field continuous on all of them. -/
theorem exists_continuous_version (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW) :
    ∃ Z : ℝ → Space d → ΩW → ℝ,
      (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) ∧
      (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
        ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)))) := by
  classical
  have hex : ∀ n : ℕ, ∃ Y : ℝ × (Fin d → ℝ) → ΩW → ℝ,
      (∀ z : ℝ × (Fin d → ℝ), z.1 ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1) →
        Y z =ᵐ[PW] fun ω => gaussianPotential d ν2 W z.1 (WithLp.toLp 2 z.2) ω) ∧
      (∀ ω, Continuous fun z => Y z ω) := fun n =>
    exists_version_continuous_on_strip hd hd3 hν2 (by positivity) PW W hW
  choose Y hYmod hYcont using hex
  refine ⟨fun t x ω => if 0 ≤ t then Y ⌈t⌉₊ (t, WithLp.ofLp x) ω
      else gaussianPotential d ν2 W t x ω, ?_, ?_⟩
  · intro t x
    by_cases ht : 0 ≤ t
    · have hmem : ((t, WithLp.ofLp x) : ℝ × (Fin d → ℝ)).1
          ∈ Set.Icc (0 : ℝ) ((⌈t⌉₊ : ℝ) + 1) := ⟨ht, by
        have := Nat.le_ceil t; linarith⟩
      have h := hYmod ⌈t⌉₊ (t, WithLp.ofLp x) hmem
      filter_upwards [h] with ω hω
      simp only [if_pos ht]
      simpa using hω
    · exact Filter.Eventually.of_forall fun ω => by simp only [if_neg ht]
  · intro T hT
    set N : ℕ := ⌈T⌉₊ with hN
    have hagree : ∀ᵐ ω ∂PW, ∀ m : ℕ, m ≤ N →
        ∀ z : ℝ × (Fin d → ℝ), z.1 ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1) →
          Y m z ω = Y N z ω := by
      rw [ae_all_iff]
      intro m
      by_cases hm : m ≤ N
      · set S : Set (ℝ × (Fin d → ℝ)) :=
          Set.Icc (0 : ℝ) ((m : ℝ) + 1) ×ˢ (Set.univ : Set (Fin d → ℝ)) with hS
        haveI : Nonempty ↥S := ⟨⟨(0, 0), ⟨⟨le_rfl, by positivity⟩, Set.mem_univ _⟩⟩⟩
        have hmodS : ∀ z : ↥S, (fun ω => Y m (z : ℝ × (Fin d → ℝ)) ω)
            =ᵐ[PW] fun ω => Y N (z : ℝ × (Fin d → ℝ)) ω := by
          intro z
          have hz1 : (z : ℝ × (Fin d → ℝ)).1 ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1) := z.2.1
          have hmN : ((m : ℝ) + 1) ≤ ((N : ℝ) + 1) := by
            have : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
            linarith
          have h1 := hYmod m (z : ℝ × (Fin d → ℝ)) hz1
          have h2 := hYmod N (z : ℝ × (Fin d → ℝ)) ⟨hz1.1, le_trans hz1.2 hmN⟩
          exact h1.trans h2.symm
        have hsub := ae_forall_eq_of_continuous_modifications PW
          (fun z : ↥S => fun ω => Y m (z : ℝ × (Fin d → ℝ)) ω)
          (fun z : ↥S => fun ω => Y N (z : ℝ × (Fin d → ℝ)) ω)
          (Filter.Eventually.of_forall fun ω => (hYcont m ω).comp continuous_subtype_val)
          (Filter.Eventually.of_forall fun ω => (hYcont N ω).comp continuous_subtype_val)
          hmodS
        filter_upwards [hsub] with ω hω _ z hz
        exact hω ⟨z, ⟨hz, Set.mem_univ _⟩⟩
      · exact Filter.Eventually.of_forall fun ω h => absurd h hm
    filter_upwards [hagree] with ω hω
    have hcont : Continuous fun p : ℝ × Space d => Y N (p.1, WithLp.ofLp p.2) ω :=
      (hYcont N ω).comp (continuous_fst.prodMk
        ((PiLp.lipschitzWith_ofLp 2 (fun _ : Fin d => ℝ)).continuous.comp continuous_snd))
    refine ContinuousOn.congr hcont.continuousOn ?_
    intro p hp
    have hp0 : 0 ≤ p.1 := hp.1.1
    have hpT : p.1 ≤ T := hp.1.2
    have hceil : ⌈p.1⌉₊ ≤ N := Nat.ceil_le_ceil hpT
    simp only [if_pos hp0]
    exact hω ⌈p.1⌉₊ hceil (p.1, WithLp.ofLp p.2) ⟨hp0, by have := Nat.le_ceil p.1; linarith⟩
