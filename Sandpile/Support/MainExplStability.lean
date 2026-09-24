/-
The stability gap `E₂` of the four-term bound at TWO rewards.

`Sandpile.abs_rescaled_odometer_sub_brownianValue_le` needs the distance between
the walk value of the cut-off rescaled field and the Brownian discount of the
cut-off LIMIT field, and those are two different rewards: the walk carries
`χ_A Z_R^{lin}` and the motion carries `χ_A Z`.  `stability_gap_of_close` of
`ExplStability` compares a single reward with itself on the two sides, which is
what the killed route never needed; the unkilled route of `sandpile.tex:1890-1907`
needs the two-reward form, and it is the same argument: the threshold of
`stability_uniform_of_finite` does not see either reward, both values are
1-Lipschitz in their reward, and a triangle inequality through the member of the
finite family that both rewards are near gives the gap.  This is the unkilled
analogue of `Sandpile.killed_stability_gap_of_two_rewards`.

The two side conditions of the discrete value are discharged here and not left to
the caller: at a reward that reads the walk through its position at the stopping
time, the attainable payoffs are bounded above by `bddAbove_walk_stopped_value`
and the stopped reward is integrable by `integrable_stopped_value`, both without
any bound on the reward.
-/
import Sandpile.Support.MainExplWalkValue
import Sandpile.Support.StopValue

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace Sandpile

variable {d : ℕ}

/-- **The stability gap `E₂` at two rewards.**  A walk reward within `ηF` of a member of the
finite family and a Brownian reward within `ηH` of the SAME member give a gap of
`ε + ηF + ηH`, uniformly over the scale beyond a threshold and over the starting points in the
compact set.  Neither reward is seen by the threshold, so both may be random. -/
theorem stability_gap_of_two_rewards
    (hStab : Sandpile.External.ContinuumStoppingStability.{u}) (d : ℕ) (hd : 1 ≤ d)
    (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (T : ℝ) (hT : 0 < T)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (N : ℕ) (G : Fin N → ℝ → Sandpile.Continuum.Space d → ℝ)
    (hGc : ∀ i, Continuous fun p : ℝ × Sandpile.Continuum.Space d => G i p.1 p.2)
    (M : ℝ) (hGM : ∀ (i : Fin N) (s : ℝ) (y : Sandpile.Continuum.Space d), |G i s y| ≤ M)
    (ε ηF ηH : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → 0 < R → ∀ x ∈ K,
      ∀ (F H : ℝ → Sandpile.Continuum.Space d → ℝ) (i : Fin N),
        ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => H p.1 p.2)
          (Set.Icc 0 T ×ˢ Set.univ) →
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Sandpile.Continuum.Space d, |F s y - G i s y| ≤ ηF) →
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Sandpile.Continuum.Space d, |H s y - G i s y| ≤ ηH) →
        |Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -H s y) T|
          ≤ ε + ηF + ηH := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := Sandpile.stability_uniform_of_finite hStab d hd ΩB PB B hB
    T T hT le_rfl K hK N G hGc M hGM ε hε
  refine ⟨R₀, hR₀pos, ?_⟩
  intro R hR hRp x hx F H i hHc hF hH
  set n : ℕ := ⌊R ^ 2 * T⌋₊ with hn
  set z : Sandpile.Site d := fun j => ⌊R * x j⌋ with hz
  set f : ℕ → Sandpile.Site d → ℝ := fun k y =>
    F (((n : ℕ) - (k : ℝ)) / R ^ 2) (Sandpile.External.Lclt.scaledSite R y) with hf
  set g : ℕ → Sandpile.Site d → ℝ := fun k y =>
    G i (((n : ℕ) - (k : ℝ)) / R ^ 2) (Sandpile.External.Lclt.scaledSite R y) with hg
  have hw : |Sandpile.stoppingSup n z (fun k X => f k (X k)) -
      Sandpile.stoppingSup n z (fun k X => g k (X k))| ≤ ηF :=
    Sandpile.abs_stoppingSup_sub_le_of_reward hd n z _ _ ηF
      (Sandpile.bddAbove_walk_stopped_value hd z n f)
      (Sandpile.bddAbove_walk_stopped_value hd z n g)
      (fun τ ht hnn => Sandpile.integrable_stopped_value hd z n f ht hnn)
      (fun τ ht hnn => Sandpile.integrable_stopped_value hd z n g ht hnn)
      (Sandpile.reward_gap_of_uniform R T T hRp hT.le le_rfl F (G i) ηF hF)
  have hbH : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y, |H s y| ≤ M + ηH := by
    intro s hs y
    have ha := abs_sub_le (H s y) (G i s y) 0
    simp only [sub_zero] at ha
    linarith [hH s hs y, hGM i s y]
  have hm : |Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -H s y) T -
      Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T| ≤ ηH := by
    refine Sandpile.Continuum.abs_brownianDiscount_sub_le_of_continuousOn (hB x)
      (fun s y => -H s y) (fun s y => -G i s y) T (M + ηH) M ηH hT.le
      hHc.neg ((hGc i).continuousOn.neg) ?_ ?_ ?_
    · intro s hs y
      simpa only [abs_neg] using hbH s hs y
    · intro s _hs y
      simpa only [abs_neg] using hGM i s y
    · intro s hs y
      simpa only [neg_sub_neg, abs_sub_comm] using hH s hs y
  have hmid := hR₀ R hR i T ⟨le_rfl, le_rfl⟩ x hx
  have ha := abs_sub_le (Sandpile.stoppingSup n z (fun k X => f k (X k)))
    (Sandpile.stoppingSup n z (fun k X => g k (X k)))
    (Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -H s y) T)
  have hb := abs_sub_le (Sandpile.stoppingSup n z (fun k X => g k (X k)))
    (Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T)
    (Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -H s y) T)
  rw [abs_sub_comm] at hm
  change |Sandpile.stoppingSup n z (fun k X => f k (X k)) -
    Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -H s y) T| ≤ ε + ηF + ηH
  change |Sandpile.stoppingSup n z (fun k X => g k (X k)) -
    Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T| ≤ ε at hmid
  linarith

end Sandpile
