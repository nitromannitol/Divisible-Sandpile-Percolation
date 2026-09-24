/-
The Green field is Lipschitz for the `\ell^2` distance between sceneries.

Step 4 of case (a) needs a Lipschitz constant for `\Theta_n` in the `\ell^2` distance and
not only in each coordinate separately, because the conditioning of `sandpile.tex:5270-5271`
moves every coordinate at once.  The crude constant proved here, `\|G(0,\cdot)\|`, is the
one Cauchy-Schwarz gives from `eq:dgt4-green-l2` alone: the field is the pairing of the
scenery with the Green coefficients, and a bounded stopping time cannot enlarge that
pairing, so the deviation `V_\infty-u_n` and each of its averages move by at most
`\|G(0,\cdot)\|` times the distance.  It is the continuity that the sharp constant
`\|\sum_{j\geq k+1}p_j(0,\cdot)\|` is read off by approximation with finitely supported
differences.
-/
import Sandpile.Support.Dgt4AConcLp
import Sandpile.Support.Dgt4AIterateAbs
import Sandpile.Support.Dgt4AIterateConst
import Sandpile.Support.Dgt4AIterateSub
import Sandpile.Support.Dgt4ACovStop
import Sandpile.Support.Dgt4FieldRecursion
import Sandpile.Support.LinGreenTail

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- **The pairing of the Green coefficients with a square-summable scenery**, with the
Cauchy-Schwarz bound of `eq:dgt4-green-l2`. -/
theorem exists_hasSum_green_mul (hd : 5 ≤ d) (y : Site d) (δ : Site d → ℝ) (M : ℝ)
    (h : HasSum (fun z => δ z ^ 2) M) :
    ∃ L : ℝ, HasSum (fun z => green d y z * δ z) L ∧
      |L| ≤ ‖greenLp d hd (0 : Site d)‖ * Real.sqrt M := by
  have hδ : Memℓp δ 2 := memLp_two_of_hasSum_sq δ M h
  have hgc : ((⟨δ, hδ⟩ : lp (fun _ : Site d => ℝ) 2) : Site d → ℝ) = δ := rfl
  refine ⟨(inner ℝ (greenLp d hd y) (⟨δ, hδ⟩ : lp (fun _ : Site d => ℝ) 2) : ℝ), ?_, ?_⟩
  · have hi := lp.hasSum_inner (𝕜 := ℝ) (greenLp d hd y)
      (⟨δ, hδ⟩ : lp (fun _ : Site d => ℝ) 2)
    simpa [RCLike.inner_apply, conj_trivial, coeFn_greenLp, hgc, mul_comm] using hi
  · have hcs := abs_real_inner_le_norm (greenLp d hd y)
      (⟨δ, hδ⟩ : lp (fun _ : Site d => ℝ) 2)
    have hsq := hasSum_sq_coeFn_lp (⟨δ, hδ⟩ : lp (fun _ : Site d => ℝ) 2)
    rw [hgc] at hsq
    have hM : ‖(⟨δ, hδ⟩ : lp (fun _ : Site d => ℝ) 2)‖ ^ 2 = M := hsq.unique h
    have hn : ‖(⟨δ, hδ⟩ : lp (fun _ : Site d => ℝ) 2)‖ = Real.sqrt M := by
      rw [← hM, Real.sqrt_sq (norm_nonneg _)]
    rwa [norm_greenLp_eq hd y, hn] at hcs

/-- **The Green field moves by at most `\|G(0,\cdot)\|` times the `\ell^2` distance.** -/
theorem exists_tendsto_infiniteGreenField_sub (hd : 5 ≤ d) (ξ η : Site d → ℝ) (M : ℝ)
    (h : HasSum (fun z => (ξ z - η z) ^ 2) M)
    (hξ : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ξ y) atTop (𝓝 L)) :
    (∀ y : Site d, ∃ L : ℝ,
        Tendsto (fun n => infiniteGreenFieldPartial n η y) atTop (𝓝 L)) ∧
      ∀ y : Site d, |infiniteGreenField ξ y - infiniteGreenField η y|
        ≤ ‖greenLp d hd (0 : Site d)‖ * Real.sqrt M := by
  have key : ∀ y : Site d, ∃ L : ℝ, HasSum (fun z => green d y z * (ξ z - η z)) L ∧
      |L| ≤ ‖greenLp d hd (0 : Site d)‖ * Real.sqrt M :=
    fun y => exists_hasSum_green_mul hd y (fun z => ξ z - η z) M h
  have hpart : ∀ (y : Site d) (n : ℕ), infiniteGreenFieldPartial n η y
      = infiniteGreenFieldPartial n ξ y
        - ∑ z ∈ boxFinset (0 : Site d) n, green d y z * (ξ z - η z) := by
    intro y n
    rw [infiniteGreenFieldPartial_boxFinset_site, infiniteGreenFieldPartial_boxFinset_site,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hmain : ∀ y : Site d, Tendsto (fun n => infiniteGreenFieldPartial n η y) atTop
      (𝓝 (infiniteGreenField ξ y - (key y).choose)) := by
    intro y
    obtain ⟨hL, -⟩ := (key y).choose_spec
    have hb : Tendsto (fun n => ∑ z ∈ boxFinset (0 : Site d) n, green d y z * (ξ z - η z))
        atTop (𝓝 (key y).choose) := by
      have hbb := tendsto_sum_boxFinset hL.summable
      rwa [hL.tsum_eq] at hbb
    refine ((tendsto_infiniteGreenFieldPartial (hξ y)).sub hb).congr fun n => (hpart y n).symm
  refine ⟨fun y => ⟨_, hmain y⟩, fun y => ?_⟩
  obtain ⟨-, hbound⟩ := (key y).choose_spec
  have hval : infiniteGreenField η y = infiniteGreenField ξ y - (key y).choose :=
    tendsto_nhds_unique (tendsto_infiniteGreenFieldPartial ⟨_, hmain y⟩) (hmain y)
  rw [hval]
  simpa using hbound

/-- **The deviation `V_\infty-u_n` moves by at most `\|G(0,\cdot)\|` times the `\ell^2`
distance**, at every site. -/
theorem abs_deviation_sub_le_of_hasSum_sq (hd : 5 ≤ d) (ξ η : Site d → ℝ) (M : ℝ)
    (h : HasSum (fun z => (ξ z - η z) ^ 2) M)
    (hξ : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ξ y) atTop (𝓝 L))
    (n : ℕ) (x : Site d) :
    |(infiniteGreenField ξ x - odometerOf ξ n x)
        - (infiniteGreenField η x - odometerOf η n x)|
      ≤ ‖greenLp d hd (0 : Site d)‖ * Real.sqrt M := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  obtain ⟨hη, hfield⟩ := exists_tendsto_infiniteGreenField_sub hd ξ η M h hξ
  refine abs_infiniteGreenField_sub_odometer_gap_le (by omega) ξ η hξ hη n x _ ?_
  intro τ hτ hτn
  have hi1 := integrable_stopped_value (d := d) (by omega) x n (fun _ => infiniteGreenField ξ) hτ hτn
  have hi2 := integrable_stopped_value (d := d) (by omega) x n (fun _ => infiniteGreenField η) hτ hτn
  rw [← integral_sub hi1 hi2]
  have hbd : ∀ X : ℕ → Site d,
      ‖infiniteGreenField ξ (X (τ X)) - infiniteGreenField η (X (τ X))‖
        ≤ ‖greenLp d hd (0 : Site d)‖ * Real.sqrt M := fun X => hfield _
  have := norm_integral_le_of_norm_le_const (μ := walkLaw d x)
    (C := ‖greenLp d hd (0 : Site d)‖ * Real.sqrt M) (Filter.Eventually.of_forall hbd)
  simpa using this

/-- **The iterated average of the deviation is `\ell^2`-Lipschitz with the crude
constant.** -/
theorem abs_avgIterate_deviation_sub_le_of_hasSum_sq (hd : 5 ≤ d) (ξ η : Site d → ℝ) (M : ℝ)
    (h : HasSum (fun z => (ξ z - η z) ^ 2) M)
    (hξ : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ξ y) atTop (𝓝 L))
    (n j : ℕ) :
    |(avg^[j] (fun y => infiniteGreenField ξ y - odometerOf ξ n y)) 0
        - (avg^[j] (fun y => infiniteGreenField η y - odometerOf η n y)) 0|
      ≤ ‖greenLp d hd (0 : Site d)‖ * Real.sqrt M := by
  refine (abs_avgIterate_sub_le (fun y => infiniteGreenField ξ y - odometerOf ξ n y)
    (fun y => infiniteGreenField η y - odometerOf η n y) j 0).trans ?_
  have h2 := avg_iterate_abs_le (fun y => infiniteGreenField ξ y - odometerOf ξ n y)
    (fun y => infiniteGreenField η y - odometerOf η n y) (fun _ => (1 : ℝ))
    (‖greenLp d hd (0 : Site d)‖ * Real.sqrt M) j
    (fun y => by
      simpa using abs_deviation_sub_le_of_hasSum_sq hd ξ η M h hξ n y)
  rwa [avg_iterate_const (by omega) j (1 : ℝ) 0, one_mul] at h2

end Sandpile
