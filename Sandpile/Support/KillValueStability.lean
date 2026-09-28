import Sandpile.Support.KillStability
import Sandpile.Support.StopValue
import Sandpile.Support.StoppedOdometer

/-!
# Stability of killed-walk stopping values

Finite-horizon killed walk rewards have bounded attainable values. A finite
family of continuous rewards gives one stability threshold for a source reward
and a continuous limit reward approximated by the same family member.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

/-- The set of stopped values `Sandpile.killedSet D n x (fun k X => F k (X k))` is
bounded above, by the finite constant `M = ∑_{j ≤ n} ∑_{z ∈ boxFinset x n} |F j z|`:
every stopped reward is dominated, in absolute value, by the sum of `|F j z|` over
the times `j` and sites `z` the walk can reach before time `n`. -/
theorem Sandpile.bddAbove_killedSet_stopped_value {d : ℕ} (hd : 1 ≤ d)
    (D : Set (Sandpile.Site d)) (x : Sandpile.Site d) (n : ℕ)
    (F : ℕ → Sandpile.Site d → ℝ) :
    BddAbove (Sandpile.killedSet D n x (fun k X => F k (X k))) := by
  letI : NeZero d := ⟨by omega⟩
  letI : IsProbabilityMeasure (Sandpile.walkLaw d x) := Sandpile.walkLaw_isProbabilityMeasure d x
  let M : ℝ := ∑ j ∈ Finset.range (n + 1), ∑ z ∈ Sandpile.boxFinset x n, |F j z|
  refine ⟨M, ?_⟩
  rintro a ⟨τ, hτ, ht, _hc, rfl⟩
  have hb : ∀ᵐ X ∂(Sandpile.walkLaw d x), F (τ X) (X (τ X)) ≤ M := by
    filter_upwards [Sandpile.ae_boxDist_walk hd x] with X hX
    have ha : |F (τ X) (X (τ X))| ≤ ∑ z ∈ Sandpile.boxFinset x n, |F (τ X) z| :=
      Finset.single_le_sum (f := fun z => |F (τ X) z|) (fun _ _ => abs_nonneg _)
        (Sandpile.mem_boxFinset ((hX _).trans (ht X)))
    have hb : (∑ z ∈ Sandpile.boxFinset x n, |F (τ X) z|) ≤ M :=
      Finset.single_le_sum (f := fun j => ∑ z ∈ Sandpile.boxFinset x n, |F j z|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (ht X)))
    exact (le_abs_self _).trans (ha.trans hb)
  have he := integral_mono_ae (Sandpile.integrable_stopped_value hd x n F hτ ht)
    (integrable_const M) hb
  simpa using he

/-- For a compact `K`, a finite family `G` of continuous, uniformly bounded reward
functions, and error thresholds `ηF`, `ηH`, all rescaled discrete killed-walk
stopping values built from a reward `F` within `ηF` of some `G i` are, for large
enough `R`, within `ε + ηF + ηH` of the continuum Brownian discounted value built
from any continuous `H` within `ηH` of that same `G i`. Proved by comparing both
sides to the value at `G i` via
`Sandpile.abs_killedStoppingSup_sub_le_of_reward` and
`Sandpile.Continuum.abs_brownianDiscountCube_sub_le_of_continuousOn`, and closing
with `Sandpile.killed_stability_uniform_of_finite`. -/
theorem Sandpile.killed_stability_gap_of_two_rewards
    (hStab : Sandpile.External.CubeStoppingStability) (d : ℕ) (hd : 1 ≤ d)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (T : ℝ) (hT : 0 < T) (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (N : ℕ) (G : Fin N → ℝ → Sandpile.Continuum.Space d → ℝ)
    (hGc : ∀ i, Continuous fun p : ℝ × Sandpile.Continuum.Space d => G i p.1 p.2)
    (M : ℝ) (hGM : ∀ i s y, |G i s y| ≤ M)
    (ε ηF ηH : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x ∈ K,
      ∀ (F H : ℝ → Sandpile.Continuum.Space d → ℝ) (i : Fin N),
        ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => H p.1 p.2)
          (Set.Icc 0 T ×ˢ Set.univ) →
        (∀ s ∈ Set.Icc 0 T, ∀ y, |F s y - G i s y| ≤ ηF) →
        (∀ s ∈ Set.Icc 0 T, ∀ y, |H s y - G i s y| ≤ ηH) →
        |Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
              ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun k X => F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -H s y) T 1 x|
          ≤ ε + ηF + ηH := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := Sandpile.killed_stability_uniform_of_finite hStab d hd
    ΩB PB B hB T T hT le_rfl K hK N G hGc M hGM ε hε
  refine ⟨R₀, hR₀pos, ?_⟩
  intro R hR x hx F H i hHc hF hH
  have hRp : 0 < R := hR₀pos.trans_le hR
  let n : ℕ := ⌊R ^ 2 * T⌋₊
  let z : Sandpile.Site d := fun j => ⌊R * x j⌋
  let D := Sandpile.supBox z R
  let f : ℕ → Sandpile.Site d → ℝ := fun k y =>
    F (((n : ℕ) - (k : ℝ)) / R ^ 2) (Sandpile.External.Lclt.scaledSite R y)
  let g : ℕ → Sandpile.Site d → ℝ := fun k y =>
    G i (((n : ℕ) - (k : ℝ)) / R ^ 2) (Sandpile.External.Lclt.scaledSite R y)
  have hw : |Sandpile.killedStoppingSup D n z (fun k X => f k (X k)) -
      Sandpile.killedStoppingSup D n z (fun k X => g k (X k))| ≤ ηF :=
    Sandpile.abs_killedStoppingSup_sub_le_of_reward hd D n z _ _ ηF
      (Sandpile.bddAbove_killedSet_stopped_value hd D z n f)
      (Sandpile.bddAbove_killedSet_stopped_value hd D z n g)
      (fun τ ht hn => Sandpile.integrable_stopped_value hd z n f ht hn)
      (fun τ ht hn => Sandpile.integrable_stopped_value hd z n g ht hn)
      (Sandpile.reward_gap_of_uniform R T T hRp hT.le le_rfl F (G i) ηF hF)
  have hb : ∀ s ∈ Set.Icc 0 T, ∀ y, |H s y| ≤ M + ηH := by
    intro s hs y
    have ha := abs_sub_le (H s y) (G i s y) 0
    simp only [sub_zero] at ha
    linarith [hH s hs y, hGM i s y]
  have hm : |Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -H s y) T 1 x -
      Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -G i s y) T 1 x| ≤ ηH := by
    refine Sandpile.Continuum.abs_brownianDiscountCube_sub_le_of_continuousOn (hB x)
      (fun s y => -H s y) (fun s y => -G i s y) T 1 (M + ηH) M ηH hT.le zero_le_one
      hHc.neg (hGc i).continuousOn.neg ?_ ?_ ?_
    · intro s hs y _hy
      simpa only [abs_neg] using hb s hs y
    · intro s _hs y _hy
      simpa only [abs_neg] using hGM i s y
    · intro s hs y _hy
      simpa only [neg_sub_neg, abs_sub_comm] using hH s hs y
  have hmid := hR₀ R hR i T ⟨le_rfl, le_rfl⟩ x hx
  have ha := abs_sub_le (Sandpile.killedStoppingSup D n z (fun k X => f k (X k)))
    (Sandpile.killedStoppingSup D n z (fun k X => g k (X k)))
    (Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -H s y) T 1 x)
  have hb' := abs_sub_le (Sandpile.killedStoppingSup D n z (fun k X => g k (X k)))
    (Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -G i s y) T 1 x)
    (Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -H s y) T 1 x)
  rw [abs_sub_comm] at hm
  change |Sandpile.killedStoppingSup D n z (fun k X => f k (X k)) -
    Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -H s y) T 1 x| ≤ ε + ηF + ηH
  change |Sandpile.killedStoppingSup D n z (fun k X => g k (X k)) -
    Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -G i s y) T 1 x| ≤ ε at hmid
  linarith
