import Sandpile.Support.ManyLStep3Build
import Sandpile.Support.Dgt4ABandLawNormalized
import Sandpile.Support.Dgt4ABandLawDensity
import Sandpile.Support.Dgt4ABandLawLower
import Sandpile.Support.Dgt4ABandLawParameters
import LatticeProb.Walk.SRWPos

/-!
# The many-limits theorem, assembled

Step 1 constructs the law; Step 2 gives the contact estimates; the bridge takes a subsequence
for each exponent; Step 3 turns those into the field limits. All four are proved. What is
missing is that Step 1 does not EXPOSE three of the five band predicates its own construction
satisfies, so the chain cannot be joined.

`BandParameters.exists_admissible` already supplies every parameter condition the three need:
`1/A < ℓ₁`, `1 - λ₀ℓ₁ + (λ₀-1)/A < 0`, `∑ ω < 1` and `1/ℓ₁ < λ₀`. The predicates themselves are
proved at the constructed law by `bandProfile_law`, `bandDensity_law` and
`bandLowerIsolation_law`. So the first theorem below is a matter of applying what exists, not of
new mathematics.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- The Green ratio is positive in every transient dimension: the return
probability `1 - 1/G(0,0)` is positive because `G(0,0)` counts the time-two visit
as well as the time-zero one, and it is at most the ratio. -/
theorem greenRatioSup_pos {d : ℕ} (hd : 3 ≤ d) : 0 < LatticeProb.greenRatioSup d := by
  have hd1 : 1 ≤ d := by omega
  have hs := LatticeProb.summable_srwHeat hd (0 : Site d)
  have h2 : 0 < LatticeProb.srwHeat d 2 (0 : Site d) :=
    LatticeProb.srwHeat_pos hd1 (by simp) (by simp)
  have hG : 1 < LatticeProb.srwGreenInf d (0 : Site d) := by
    have hsum := hs.sum_le_tsum ({0, 2} : Finset ℕ)
      (fun j _ => LatticeProb.srwHeat_nonneg j (0 : Site d))
    have h0 : LatticeProb.srwHeat d 0 (0 : Site d) = 1 := by simp
    rw [Finset.sum_pair (by norm_num), h0] at hsum
    unfold LatticeProb.srwGreenInf
    linarith
  have hle := LatticeProb.one_sub_inv_le_greenRatioSup hd
  have hpos : 0 < 1 - 1 / LatticeProb.srwGreenInf d (0 : Site d) := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hG
  linarith

/-- **The gap clause of `exists_step1_law_banded` is unsatisfiable in dimension `0`.**
There `greenRatioSup 0` is a supremum over the empty type, hence `0`, so the quotient
`θ0 / greenRatioSup 0` is `0` and cannot exceed the positive `P.lam0`.  So
`exists_step1_law_banded` is FALSE at `d = 0`, and its statement needs a dimension
hypothesis; `exists_step1_law_banded` below is the statement with one. -/
theorem not_exists_gap_zero :
    ¬ ∃ (P : BandParameters) (θ0 : ℝ), P.lam0 < θ0 / LatticeProb.greenRatioSup 0 := by
  rintro ⟨P, θ0, h⟩
  have hempty : IsEmpty {z : Site 0 // z ≠ 0} :=
    ⟨fun z => z.2 (Subsingleton.elim _ _)⟩
  have h0 : LatticeProb.greenRatioSup 0 = 0 := Real.iSup_of_isEmpty _
  rw [h0, div_zero] at h
  exact absurd P.hlam0 (not_lt.mpr h.le)

/-- **Step 1, with every band predicate exposed, in a transient dimension.**  The same
construction as `exists_step1_law`, additionally returning the three predicates its
parameters already satisfy, and the gap `lam0 < θ0 / ℓ₀` between the exponential
moment and the Green ratio.

The dimension hypothesis is needed: at `d = 0` the gap clause is unsatisfiable
(`not_exists_gap_zero`).  The parameters are taken from `exists_admissible_small` at
`max l0 ℓ₀`, so that `ℓ₁ > ℓ₀` and `lam0 < 1/ℓ₀`; the exponential moment is then
taken at `θ0 = (lam0 ℓ₀ + 1)/2`, which lies below the threshold `1` of the band
weights and above `lam0 ℓ₀`. -/
theorem exists_step1_law_banded (hd : 3 ≤ d) (l0 : ℝ) (hl0 : 0 < l0)
    (hl01 : l0 < 1) :
    ∃ (P : BandParameters) (m : ℕ → ℕ) (mu : ℝ) (v : ℝ≥0),
      l0 < P.l1 ∧ v ≠ 0 ∧
      IsProbabilityMeasure (P.law m mu v) ∧
      (∀ z : ℝ, (P.law m mu v) {z} = 0) ∧
      Integrable (id : ℝ → ℝ) (P.law m mu v) ∧
      Integrable (fun z : ℝ => z ^ 2) (P.law m mu v) ∧
      (∀ z : ℝ, (P.law m mu v) ≠ Measure.dirac z) ∧
      ∫ z : ℝ, z ∂(P.law m mu v) = 0 ∧
      variance (id : ℝ → ℝ) (P.law m mu v) = 1 ∧
      (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
        P.law m mu v = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) ∧
      (∃ c C θ0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ0 ∧
        Integrable (fun z : ℝ => Real.exp (θ0 * |z|)) (P.law m mu v) ∧
        P.lam0 < θ0 / LatticeProb.greenRatioSup d ∧
        ∀ᶠ r : ℝ in atTop,
          c * r ≤ -Real.log ((P.law m mu v) (Iic (-r))).toReal ∧
            -Real.log ((P.law m mu v) (Iic (-r))).toReal ≤ C * r) ∧
      BandIntegratedProfile P (P.law m mu v) ∧
      BandProfile P (P.law m mu v) ∧
      BandDensity P (P.law m mu v) ∧
      BandLowerIsolation P (P.law m mu v) ∧
      (∀ κ : ℝ, κ ∈ Icc ((3 : ℝ) / 2) 2 →
        ∃ kl : ℕ → ℕ, StrictMono kl ∧
          Tendsto (fun n => 1 + 1 / P.theta (kl n)) atTop (𝓝 κ)) := by
  classical
  have hgpos : 0 < LatticeProb.greenRatioSup d := greenRatioSup_pos hd
  have hg1 : LatticeProb.greenRatioSup d < 1 := LatticeProb.greenRatioSup_lt_one hd
  obtain ⟨P, h1, h2, h3, h4, h5, h6, h7, h9, hsmall⟩ :=
    BandParameters.exists_admissible_small (max l0 (LatticeProb.greenRatioSup d))
      (lt_max_of_lt_left hl0) (max_lt hl01 hg1) (fun k => k + 1) (fun k => Nat.succ_pos k)
  obtain ⟨mu, v, hv, hmean, hvar⟩ :=
    exists_centered_law P (fun k => k + 1) (fun k => Nat.succ_pos k) h7 hsmall
  have hl1pos : 0 < P.l1 := P.hl1.1
  have hA : P.A⁻¹ ≤ P.l1 := by
    rw [inv_eq_one_div]
    exact h4.le
  have hlam1 : 1 < P.lam0 * P.l1 := (div_lt_iff₀ hl1pos).mp h2
  have hmtop : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hθpos : ∀ k, 0 < P.theta k := fun k => lt_of_lt_of_le one_pos (P.htheta k).1
  have hprob : IsProbabilityMeasure (P.law (fun k => k + 1) mu v) :=
    isProbabilityMeasure_bandLaw (by linarith) (fun k => (P.weight_pos k).le) hθpos
      hl1pos P.hl1.2 P.level_pos (fun k => Nat.succ_pos k) P.level_tendsto hv
      P.summable_weight (by ring)
  haveI := hprob
  obtain ⟨f, hfpos, hfsm, hfeq⟩ : ∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
      P.law (fun k => k + 1) mu v
        = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z) :=
    exists_density_bandLaw (by linarith) hv
      (fun k => le_trans zero_le_one (P.htheta k).1) (fun k => (P.weight_pos k).le)
      hl1pos P.hl1.2 P.level_pos (fun k => Nat.succ_pos k) P.level_tendsto
  have hatom : ∀ z : ℝ, (P.law (fun k => k + 1) mu v) {z} = 0 := fun z => by
    rw [hfeq]
    exact withDensity_absolutelyContinuous _ _ Real.volume_singleton
  have hnd : ∀ z : ℝ, (P.law (fun k => k + 1) mu v) ≠ Measure.dirac z := by
    intro z h
    have hz := hatom z
    rw [h] at hz
    simp at hz
  have hsq : Integrable (fun z : ℝ => z ^ 2) (P.law (fun k => k + 1) mu v) :=
    integrable_sq_bandLaw (by linarith) (fun k => (P.weight_pos k).le) hθpos hl1pos P.hl1.2
      P.level_pos (fun k => Nat.succ_pos k) P.level_tendsto hv
      (P.summable_weight_exp (1 / 2) (by norm_num))
  have hint : Integrable (id : ℝ → ℝ) (P.law (fun k => k + 1) mu v) :=
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq).integrable one_le_two
  -- the gap between the exponential moment and the Green ratio
  have hlamg : P.lam0 * LatticeProb.greenRatioSup d < 1 := by
    have hle : 1 / max l0 (LatticeProb.greenRatioSup d) ≤ 1 / LatticeProb.greenRatioSup d :=
      one_div_le_one_div_of_le hgpos (le_max_right _ _)
    exact (lt_div_iff₀ hgpos).mp (h3.trans_le hle)
  have hlampos : 0 < P.lam0 := P.hlam0
  have hθ0pos : 0 < (P.lam0 * LatticeProb.greenRatioSup d + 1) / 2 := by
    have := mul_pos hlampos hgpos
    linarith
  have hθ01 : (P.lam0 * LatticeProb.greenRatioSup d + 1) / 2 < 1 := by linarith
  have hexp : Integrable
      (fun z : ℝ => Real.exp ((P.lam0 * LatticeProb.greenRatioSup d + 1) / 2 * |z|))
      (P.law (fun k => k + 1) mu v) :=
    integrable_exp_abs_law P (fun k => k + 1) (fun k => Nat.succ_pos k) mu v hv h7.le
      hθ0pos hθ01
  have hgap : P.lam0 < (P.lam0 * LatticeProb.greenRatioSup d + 1) / 2
      / LatticeProb.greenRatioSup d := by
    rw [lt_div_iff₀ hgpos]
    linarith
  obtain ⟨c, C, -, hc, hC, -, -, htail⟩ :=
    exists_log_tail_law P (fun k => k + 1) (fun k => Nat.succ_pos k) mu v hv h7.le
  exact ⟨P, fun k => k + 1, mu, v, lt_of_le_of_lt (le_max_left _ _) h1, hv, hprob, hatom,
    hint, hsq, hnd, hmean, hvar, ⟨f, hfpos, hfsm, hfeq⟩,
    ⟨c, C, (P.lam0 * LatticeProb.greenRatioSup d + 1) / 2, hc, hC, hθ0pos, hexp, hgap, htail⟩,
    bandIntegratedProfile_law P hA _ (fun k => Nat.succ_pos k) hmtop mu v hv h7.le,
    bandProfile_law P hA _ (fun k => Nat.succ_pos k) hmtop mu v hv h7.le,
    bandDensity_law P hA _ (fun k => Nat.succ_pos k) mu v hv h7.le,
    bandLowerIsolation_law P hlam1 h5 _ (fun k => Nat.succ_pos k) mu v hv h7.le, h9⟩

/-- **Step 1, with every band predicate exposed.**  The same construction as
`exists_step1_law`, additionally returning the three predicates its parameters
already satisfy.

Proof.  Take the parameters from `BandParameters.exists_admissible`, build the law
as `exists_step1_law` does, and apply `bandProfile_law`, `bandDensity_law` and
`bandLowerIsolation_law`; each of their hypotheses is one of the admissibility
clauses. -/
theorem dgt4_many_limits_assembled (d : ℕ) (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (hHeat : Sandpile.External.HeatKernelBounds)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ)) :
    ∃ ν : Measure ℝ, ∃ _ : IsProbabilityMeasure ν,
      ∫ z, z ∂ν = 0 ∧ variance (id : ℝ → ℝ) ν = 1 ∧
      (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
        ν = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) ∧
      (∃ c C θ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ ∧
        Integrable (fun z => Real.exp (θ * |z|)) ν ∧
        ∀ᶠ r : ℝ in atTop,
          c * r ≤ -Real.log (ν (Set.Iic (-r))).toReal ∧
            -Real.log (ν (Set.Iic (-r))).toReal ≤ C * r) ∧
      ManyLStep3Input (d := d) (ν := ν) ∧
      ∀ T : ℝ, 0 < T → ∀ κ κ' : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
        κ' ∈ Set.Icc ((3 : ℝ) / 2) 2 → κ ≠ κ' →
        ∃ φ : Sandpile.Continuum.Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ ∧
          Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ ≠
            Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ' T φ φ := by
  have hd3 : 3 ≤ d := by omega
  obtain ⟨P, m, mu, v, -, hv, hprob, hatom, hint, hsq, hnd, hmean, hvar, hdens,
    ⟨c, C, θ0, hc, hC, hθ0, hexp, hgap, htail⟩, hprof, hbp, hbd, hlow, hsub⟩ :=
    exists_step1_law_banded (d := d) hd3 (LatticeProb.greenRatioSup d)
      (greenRatioSup_pos hd3) (LatticeProb.greenRatioSup_lt_one hd3)
  haveI := hprob
  obtain ⟨R, hRmono, hRtop, hR⟩ :=
    exists_uniformContactThresholdsAlong P hd (P.law m mu v) hatom hint hmean hsq hnd hθ0
      hexp hgap hprof hbp hbd hlow hsub
  have hLp : MemLp (id : ℝ → ℝ) 2 (P.law m mu v) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq
  have hvar' : evariance (id : ℝ → ℝ) (P.law m mu v) < ⊤ := hLp.evariance_lt_top
  have hvar0 : 0 < evariance (id : ℝ → ℝ) (P.law m mu v) := by
    rw [← ofReal_variance hLp, hvar]
    simp
  haveI : NullSingletonClass (P.law m mu v) := ⟨fun z => hatom z⟩
  have hvarpos : 0 < variance (id : ℝ → ℝ) (P.law m mu v) := by rw [hvar]; norm_num
  refine ⟨P.law m mu v, hprob, hmean, hvar, hdens, ⟨c, C, θ0, hc, hC, hθ0, hexp, htail⟩,
    manyLStep3Input_of_thresholds d hd hGreen hInter hHeat hLocalCLT hBesov (P.law m mu v)
      hmean hvar0 hvar' ⟨R, hRmono, hRtop, hR⟩, ?_⟩
  intro T hT κ κ' hκ hκ' hne
  exact Sandpile.Support.exists_testFn_weightedMembraneCov_ne d (by omega) hT hvarpos
    (by linarith [hκ.1]) (by linarith [hκ'.1]) hne

end Sandpile.Support
