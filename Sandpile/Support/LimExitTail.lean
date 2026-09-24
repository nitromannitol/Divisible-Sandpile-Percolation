/-
The exponential tail of the exit time of a Euclidean ball for Brownian motion
(`sandpile.tex:2495-2513`): "the exit time of a ball has
exponential moments".  This is the quantitative input `BallStoppedApproximation`
needs to control the error between the `T`-truncated ball-stopped field and the
untruncated one: the truncated and untruncated stopping rules disagree only on
the event that the ball has not yet been exited by time `T`, so it suffices that
this event have probability decaying exponentially in `T`, uniformly in the
starting point (a fact of the motion alone, not of the reward `h`).

The route is elementary and needs no reflection principle: split `[0,T]` into
blocks of a fixed length `T0` scaled to the ball radius, and bound the
probability that a real Brownian motion stays inside a fixed interval throughout
every block by a Markov/independent-increments argument, using only that the
motion's value at the END of each block is itself Gaussian (an anticoncentration
bound on a single Gaussian coordinate, not on the whole path).  Reducing the
ball-exit event to a SINGLE coordinate of the `d`-dimensional motion (via
`IsBrownian`'s definition, `coord`) avoids any need for a union bound over
dimensions.
-/
import Sandpile.Continuum.Stopping
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open Sandpile.Continuum

namespace Sandpile.Support

/-- A centred real Gaussian gives an interval of length `L` probability at most
`L / √(2πv)`, uniformly in the interval's position.  This is the anticoncentration
bound behind the block argument: the density of `gaussianReal 0 v` is bounded by
its value at the mean, `(√(2πv))⁻¹`. -/
theorem gaussianReal_zero_Ioo_le {v : ℝ≥0} (hv : v ≠ 0) (c L : ℝ) :
    ProbabilityTheory.gaussianReal 0 v (Set.Ioo c (c + L))
      ≤ ENNReal.ofReal (L / Real.sqrt (2 * Real.pi * v)) := by
  have hpos : (0:ℝ) < Real.sqrt (2 * Real.pi * v) := by
    have hv' : (0:ℝ) < (v:ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hv
    positivity
  have hbound : ∀ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 v x
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    intro x
    rw [ProbabilityTheory.gaussianPDFReal]
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * v)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      exact neg_nonpos.mpr (by positivity)
    calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * v))
        ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (Real.sqrt (2 * Real.pi * v))⁻¹ := mul_one _
  rw [ProbabilityTheory.gaussianReal_apply 0 hv]
  calc ∫⁻ x in Set.Ioo c (c + L), ProbabilityTheory.gaussianPDF 0 v x
      ≤ ∫⁻ _x in Set.Ioo c (c + L), ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_Ioo
        intro x _
        rw [ProbabilityTheory.gaussianPDF]
        exact ENNReal.ofReal_le_ofReal (hbound x)
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) * volume (Set.Ioo c (c + L)) := by
        rw [MeasureTheory.setLIntegral_const]
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) * ENNReal.ofReal L := by
        rw [Real.volume_Ioo]
        congr 1
        ring_nf
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹ * L) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (L / Real.sqrt (2 * Real.pi * v)) := by rw [div_eq_mul_inv]; ring_nf

/-- The `k`-th block boundary for a block length `T0`. -/
noncomputable def blockTime (T0 : ℝ≥0) (k : ℕ) : ℝ≥0 := (k : ℝ≥0) * T0

theorem blockTime_mono (T0 : ℝ≥0) : Monotone (blockTime T0) := by
  intro a b hab
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) bot_le

theorem blockTime_succ (T0 : ℝ≥0) (n : ℕ) :
    blockTime T0 (n + 1) = blockTime T0 n + T0 := by
  unfold blockTime
  push_cast
  ring

/-- The past values at the block boundaries `0,T0,...,nT0` (an `(n+1)`-tuple) are
independent of the NEXT increment `X((n+1)T0) - X(nT0)`: this is the weak Markov
property (`IsPreBrownianReal.indepFun_shift`) read at the finitely many times the
block argument needs, composed with the coordinate evaluations. -/
theorem indepFun_blockPast_increment {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} (hX : IsPreBrownianReal X P) (T0 : ℝ≥0) (n : ℕ) :
    IndepFun (fun ω => (fun k : Fin (n + 1) => X (blockTime T0 k) ω))
      (fun ω => X (blockTime T0 n + T0) ω - X (blockTime T0 n) ω) P := by
  have hshift := hX.indepFun_shift (blockTime T0 n)
  have hmeas_past : Measurable (fun f : (Set.Iic (blockTime T0 n) : Set ℝ≥0) → ℝ =>
      (fun k : Fin (n + 1) => f ⟨blockTime T0 k,
        blockTime_mono T0 (by exact_mod_cast (Nat.lt_succ_iff.mp k.isLt))⟩)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hmeas_fut : Measurable (fun g : ℝ≥0 → ℝ => g T0) := measurable_pi_apply T0
  exact (hshift.comp hmeas_fut hmeas_past).symm

/-- The block event: the motion stays within `(-A,A)` of its start at every one of
the `n+1` sampled times `0,T0,...,nT0`. -/
def blockEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (T0 : ℝ≥0) (A : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ k : Fin (n + 1), |X (blockTime T0 k) ω| < A}

theorem blockEvent_succ {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (T0 : ℝ≥0) (A : ℝ) (n : ℕ) :
    blockEvent X T0 A (n + 1)
      = blockEvent X T0 A n ∩ {ω | |X (blockTime T0 (n + 1)) ω| < A} := by
  ext ω
  simp only [blockEvent, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun k => h k.castSucc, h (Fin.last (n + 1))⟩
  · rintro ⟨h1, h2⟩ k
    refine Fin.lastCases ?_ ?_ k
    · simpa using h2
    · intro i
      exact h1 i

/-- The block event's probability contracts by the anticoncentration factor at
each new block: this is the induction step of the exponential tail bound,
using only that the increment at the new block is independent of the past and
Gaussian. -/
theorem measure_blockEvent_succ_le {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P] (hX : IsPreBrownianReal X P)
    (T0 : ℝ≥0) (hT0 : T0 ≠ 0) (A : ℝ) (n : ℕ) :
    P (blockEvent X T0 A (n + 1)) ≤
      ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) * P (blockEvent X T0 A n) := by
  classical
  set U : Ω → (Fin (n + 1) → ℝ) := fun ω k => X (blockTime T0 k) ω with hUdef
  set V : Ω → ℝ := fun ω => X (blockTime T0 n + T0) ω - X (blockTime T0 n) ω with hVdef
  have hind : IndepFun U V P := indepFun_blockPast_increment hX T0 n
  have hVlaw : HasLaw V (ProbabilityTheory.gaussianReal 0 T0) P :=
    (hX.shift (blockTime T0 n)).hasLaw_eval T0
  have hUmeas : AEMeasurable U P := aemeasurable_pi_lambda _ (fun k => hX.aemeasurable _)
  have hVmeas : AEMeasurable V P := hVlaw.aemeasurable
  have hprod : P.map (fun ω => (U ω, V ω)) = (P.map U).prod (P.map V) :=
    hind.map_prod_eq_prod_map_map hUmeas hVmeas
  have hSmeas : MeasurableSet {f : Fin (n + 1) → ℝ | ∀ k, |f k| < A} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun k =>
      measurableSet_lt ((continuous_apply k).abs.measurable) measurable_const)
  set C : Set ((Fin (n + 1) → ℝ) × ℝ) :=
    {p | (∀ k, |p.1 k| < A) ∧ |p.1 (Fin.last n) + p.2| < A} with hCdef
  have hCmeas : MeasurableSet C := by
    apply MeasurableSet.inter
    · exact hSmeas.preimage measurable_fst
    · exact measurableSet_lt
        (((continuous_apply (Fin.last n)).comp continuous_fst).add continuous_snd).abs.measurable
        measurable_const
  have hev : blockEvent X T0 A (n + 1) = (fun ω => (U ω, V ω)) ⁻¹' C := by
    rw [blockEvent_succ]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, hCdef, Set.mem_setOf_eq, blockEvent, hUdef,
      hVdef, Fin.val_last]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have heq : X (blockTime T0 n) ω + (X (blockTime T0 n + T0) ω - X (blockTime T0 n) ω)
          = X (blockTime T0 (n + 1)) ω := by rw [blockTime_succ]; ring
      rwa [heq]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have heq : X (blockTime T0 n) ω + (X (blockTime T0 n + T0) ω - X (blockTime T0 n) ω)
          = X (blockTime T0 (n + 1)) ω := by rw [blockTime_succ]; ring
      rwa [heq] at h2
  have hUevent : blockEvent X T0 A n = U ⁻¹' {f : Fin (n + 1) → ℝ | ∀ k, |f k| < A} := by
    ext ω; simp [blockEvent, hUdef]
  have hkey : ∀ f : Fin (n + 1) → ℝ,
      (P.map V) {v | (f, v) ∈ C} ≤
        ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) *
          {f' : Fin (n + 1) → ℝ | ∀ k, |f' k| < A}.indicator (fun _ => (1 : ℝ≥0∞)) f := by
    intro f
    by_cases hf : ∀ k, |f k| < A
    · have hfmem : f ∈ {f' : Fin (n + 1) → ℝ | ∀ k, |f' k| < A} := hf
      rw [Set.indicator_of_mem hfmem, mul_one]
      have hset : {v | (f, v) ∈ C} = Set.Ioo (-A - f (Fin.last n)) (A - f (Fin.last n)) := by
        ext v
        show ((∀ k, |f k| < A) ∧ |f (Fin.last n) + v| < A) ↔ v ∈ Set.Ioo _ _
        rw [Set.mem_Ioo]
        constructor
        · rintro ⟨-, h2⟩
          rw [abs_lt] at h2
          exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
        · rintro ⟨h1, h2⟩
          refine ⟨hf, ?_⟩
          rw [abs_lt]
          exact ⟨by linarith, by linarith⟩
      rw [hset, hVlaw.map_eq]
      have hgauss := gaussianReal_zero_Ioo_le hT0 (-A - f (Fin.last n)) (2 * A)
      have heq2 : (-A - f (Fin.last n)) + 2 * A = A - f (Fin.last n) := by ring
      rwa [heq2] at hgauss
    · have hfmem : f ∉ {f' : Fin (n + 1) → ℝ | ∀ k, |f' k| < A} := hf
      rw [Set.indicator_of_notMem hfmem, mul_zero, nonpos_iff_eq_zero]
      convert measure_empty (μ := P.map V)
      ext v
      simp only [Set.mem_setOf_eq, hCdef, Set.mem_empty_iff_false, iff_false]
      intro hcon
      exact hf hcon.1
  calc P (blockEvent X T0 A (n + 1)) = P ((fun ω => (U ω, V ω)) ⁻¹' C) := by rw [hev]
    _ = P.map (fun ω => (U ω, V ω)) C :=
        (Measure.map_apply_of_aemeasurable (hUmeas.prodMk hVmeas) hCmeas).symm
    _ = ((P.map U).prod (P.map V)) C := by rw [hprod]
    _ = ∫⁻ f, (P.map V) {v | (f, v) ∈ C} ∂(P.map U) := Measure.prod_apply hCmeas
    _ ≤ ∫⁻ f, ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) *
          {f' : Fin (n + 1) → ℝ | ∀ k, |f' k| < A}.indicator (fun _ => (1 : ℝ≥0∞)) f
          ∂(P.map U) := lintegral_mono hkey
    _ = ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) *
          ∫⁻ f, {f' : Fin (n + 1) → ℝ | ∀ k, |f' k| < A}.indicator (fun _ => (1 : ℝ≥0∞)) f
            ∂(P.map U) := lintegral_const_mul _ (measurable_const.indicator hSmeas)
    _ = ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) *
          (P.map U) {f' : Fin (n + 1) → ℝ | ∀ k, |f' k| < A} := by
        rw [lintegral_indicator hSmeas]
        simp
    _ = ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) * P (blockEvent X T0 A n) := by
        rw [hUevent, Measure.map_apply_of_aemeasurable hUmeas hSmeas]

/-- The exponential contraction of the block event's probability over `n` blocks:
the induction of `measure_blockEvent_succ_le`. -/
theorem measure_blockEvent_le {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P] (hX : IsPreBrownianReal X P)
    (T0 : ℝ≥0) (hT0 : T0 ≠ 0) (A : ℝ) (n : ℕ) :
    P (blockEvent X T0 A n) ≤ ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) ^ n := by
  induction n with
  | zero => simpa using (measure_mono (Set.subset_univ (blockEvent X T0 A 0))).trans_eq measure_univ
  | succ m ih =>
    calc P (blockEvent X T0 A (m + 1))
        ≤ ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) * P (blockEvent X T0 A m) :=
          measure_blockEvent_succ_le hX T0 hT0 A m
      _ ≤ ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) *
            ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) ^ m := by gcongr
      _ = ENNReal.ofReal (2 * A / Real.sqrt (2 * Real.pi * T0)) ^ (m + 1) := (pow_succ' _ m).symm

/-- **The exit time of a Euclidean ball has exponential moments, uniformly in
the starting point** (`sandpile.tex:2495-2513`): with
`T0 := 4ds²`, the probability that a `d`-dimensional Brownian motion started at
`y` has not left the ball of radius `s` about `y` by any of the `n+1` sampled
times `0,T0,...,nT0` is at most `(1/√(2π))^n`, a bound depending on neither the
starting point `y` nor the reward.  Only a single coordinate of the motion is
used (`IsBrownian.coord`), so this needs no union bound over dimensions and no
path continuity: the event compares finitely many values of the motion, so its
probability is already meaningful without any stopping-time machinery.  This is
the quantitative fact behind `BallStoppedApproximation`: the `T`-truncated and
untruncated ball-stopped rules disagree only on the event that the ball is not
yet exited by time `T`, i.e. (for a motion with continuous paths) on the event
this theorem bounds. -/
theorem ballBlockEvent_measure_le {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    {y : Space d} {B : ℝ≥0 → Ω → Space d} {PB : Measure Ω} [IsProbabilityMeasure PB]
    (hB : IsBrownian d y B PB) (s : ℝ) (hs : 0 < s) (n : ℕ) :
    PB {ω | ∀ k : Fin (n + 1), dist (B (blockTime ⟨4 * d * s ^ 2, by positivity⟩ k) ω) y < s}
      ≤ ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi)) ^ n := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set T0 : ℝ≥0 := ⟨4 * d * s ^ 2, by positivity⟩ with hT0def
  set i0 : Fin d := ⟨0, hd⟩ with hi0def
  set X : ℝ≥0 → Ω → ℝ := fun t ω => Real.sqrt d * (B t ω i0 - y i0) with hXdef
  have hXbrown : IsBrownianReal X PB := hB.coord i0
  have hsub : {ω | ∀ k : Fin (n + 1), dist (B (blockTime T0 k) ω) y < s}
      ⊆ blockEvent X T0 (s * Real.sqrt d) n := by
    intro ω hω k
    have hdk := hω k
    have hcoord : |B (blockTime T0 k) ω i0 - y i0| ≤ dist (B (blockTime T0 k) ω) y := by
      have h1 : ‖(B (blockTime T0 k) ω - y) i0‖ ≤ ‖B (blockTime T0 k) ω - y‖ :=
        PiLp.norm_apply_le (B (blockTime T0 k) ω - y) i0
      rwa [show (B (blockTime T0 k) ω - y) i0 = B (blockTime T0 k) ω i0 - y i0 from rfl,
        Real.norm_eq_abs, ← dist_eq_norm] at h1
    show |X (blockTime T0 k) ω| < s * Real.sqrt d
    rw [hXdef]
    simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (d : ℝ))]
    calc Real.sqrt d * |B (blockTime T0 k) ω i0 - y i0|
        ≤ Real.sqrt d * dist (B (blockTime T0 k) ω) y :=
          mul_le_mul_of_nonneg_left hcoord (Real.sqrt_nonneg _)
      _ < Real.sqrt d * s := by
          apply mul_lt_mul_of_pos_left hdk
          positivity
      _ = s * Real.sqrt d := mul_comm _ _
  refine (measure_mono hsub).trans ?_
  have hT0ne : T0 ≠ 0 := by
    rw [ne_eq, ← NNReal.coe_eq_zero]
    show ¬ (4 * (d:ℝ) * s ^ 2 = 0)
    positivity
  have hthis := measure_blockEvent_le hXbrown.toIsPreBrownianReal T0 hT0ne (s * Real.sqrt d) n
  have hsimplify : 2 * (s * Real.sqrt d) / Real.sqrt (2 * Real.pi * T0)
      = 1 / Real.sqrt (2 * Real.pi) := by
    have hcast : (T0 : ℝ) = 4 * d * s ^ 2 := rfl
    rw [hcast]
    have hrw : (2 : ℝ) * Real.pi * (4 * d * s ^ 2) = (2 * s * Real.sqrt d) ^ 2 * (2 * Real.pi) := by
      rw [mul_pow, Real.sq_sqrt hd0.le]
      ring
    rw [hrw, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have ha : (2 : ℝ) * s * Real.sqrt d ≠ 0 := by positivity
    have hb : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    field_simp
  rwa [hsimplify] at hthis

end Sandpile.Support
