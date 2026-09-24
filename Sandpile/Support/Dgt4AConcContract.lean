/-
The rank-one reduction of `sandpile.tex:5270-5271` at every configuration.

`Support/Dgt4AConcLp.lean` has the contraction as an identity in `lp 2`.  What the
conditioning needs is the contraction for the everywhere-defined reduction
`projUnit` of `Support/Dgt4AConcProj.lean`, whose pairing is the box limit where that
limit exists and zero elsewhere.  The two branches match along a pair at finite
`\ell^2` distance, because the partial sums of the two configurations differ by a
series that converges absolutely by Cauchy-Schwarz: either both configurations have
the limit, and then the reduction removes exactly the component along the conditioned
direction, or neither has it, and then the reduction is the identity on the
difference.  In both branches the squared distance does not increase, which is the
hypothesis of the Gaussian concentration inequality.
-/
import Sandpile.Support.Dgt4AConcLp
import Sandpile.Support.Dgt4AConcProj

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The partial sums of a configuration and of its translate by a square-summable
difference converge together. -/
theorem mem_unitConv_of_hasSum (hd : 5 ≤ d) {ω η : Site d → ℝ} {c : ℝ}
    (hc : HasSum (fun z => (greenUnit d hd : Site d → ℝ) z * (ω z - η z)) c)
    (hω : ω ∈ unitConv d hd) :
    η ∈ unitConv d hd ∧ unitPairing d hd η = unitPairing d hd ω - c := by
  have hsum : Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n,
      (greenUnit d hd : Site d → ℝ) z * (ω z - η z)) atTop (𝓝 c) := by
    have hb := tendsto_sum_boxFinset hc.summable
    rwa [hc.tsum_eq] at hb
  have hdiff : ∀ n : ℕ, unitPartial d hd n ω - unitPartial d hd n η
      = ∑ z ∈ boxFinset (0 : Site d) n, (greenUnit d hd : Site d → ℝ) z * (ω z - η z) := by
    intro n
    rw [unitPartial, unitPartial, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hη : Tendsto (fun n => unitPartial d hd n η) atTop (𝓝 (unitPairing d hd ω - c)) := by
    have h2 := (tendsto_unitPartial_unitPairing hd hω).sub hsum
    refine h2.congr fun n => ?_
    rw [← hdiff n]
    ring
  exact ⟨⟨_, hη⟩, unitPairing_eq_of_tendsto hd hη⟩

/-- **The rank-one reduction is a contraction at every configuration.** -/
theorem hasSum_sq_projUnit_sub_le (hd : 5 ≤ d) (ω η : Site d → ℝ) (M : ℝ)
    (h : HasSum (fun z => (ω z - η z) ^ 2) M) :
    ∃ M' : ℝ, HasSum (fun z => (projUnit d hd ω z - projUnit d hd η z) ^ 2) M' ∧ M' ≤ M := by
  obtain ⟨c, hc, hsq⟩ := hasSum_sq_sub_smul (greenUnit d hd) (norm_greenUnit hd)
    (fun z => ω z - η z) M h
  by_cases hω : ω ∈ unitConv d hd
  · obtain ⟨hηmem, hval⟩ := mem_unitConv_of_hasSum hd hc hω
    refine ⟨M - c ^ 2, ?_, by nlinarith [sq_nonneg c]⟩
    refine hsq.congr_fun fun z => ?_
    rw [projUnit, projUnit, hval]
    ring
  · have hη : η ∉ unitConv d hd := by
      intro hηmem
      have hc' : HasSum (fun z => (greenUnit d hd : Site d → ℝ) z * (η z - ω z)) (-c) := by
        refine hc.neg.congr_fun fun z => ?_
        ring
      exact hω (mem_unitConv_of_hasSum hd hc' hηmem).1
    refine ⟨M, ?_, le_rfl⟩
    refine h.congr_fun fun z => ?_
    rw [projUnit, projUnit, unitPairing_of_notMem hd hω, unitPairing_of_notMem hd hη]
    ring

end Sandpile
