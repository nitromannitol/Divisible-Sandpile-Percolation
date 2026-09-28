import Sandpile.Support.ExplValueGap
import Sandpile.Support.Localization
import Sandpile.External.ContStoppingStability

/-!
# The stability gap, without the paper's subsequence argument

The stability input of the four-term bound of Theorem 1.3(i)(b), and the bridge that removes the
paper's subsequence argument.

The four-term assembly `Sandpile.abs_rescaled_odometer_sub_brownianValue_le` bounds the gap
between the rescaled odometer and the Brownian value by `E₀+E₁+E₂+E₃`, and `E₂` is the stability
gap: the distance between the walk value of the cut-off rescaled field and the Brownian discount
of the cut-off limit field. The cited input `Sandpile.External.ContinuumStoppingStability`
delivers exactly that gap, but only for a fixed family of rewards converging uniformly; the paper
reaches such a family by saying that every subsequence has a further subsequence along which the
field converges locally uniformly almost surely (`sandpile.tex:1878-1880`), which is a Skorokhod
representation.

This module replaces that step. The observation is that the threshold the cited input produces
depends on the reward family, on the accuracy, on the uniform bound and on the compact set, and on
nothing else. So:

* applied to the constant family at each member of a finite collection of rewards, it produces one
  threshold that serves the whole collection (`stability_uniform_of_finite`);

* both values are 1-Lipschitz in the reward for the supremum norm
  (`abs_stoppingSup_sub_le_of_reward` and
  `Sandpile.Continuum.abs_brownianDiscount_sub_le_of_reward`), so a reward within `η` of a member
  of the collection inherits the bound with `2η` added (`stability_gap_of_near_finite` and
  `stability_gap_of_close`).

The realization space of the motion is bound at `Type u` and the cited input is taken at the same
universe, because the cited theorem holds on an arbitrary probability space and the statements of
the paper that consume these lemmas carry a realization space of their own.

The reward may then be random, because the threshold does not see it. That is what the
subsequence argument was for, and it is why the weakest of the three Skorokhod strengths the
shared library offers is enough for this node: the library's
`tendsto_integral_of_fdd_of_equicontinuous` is needed only for the limit of the Brownian values, a
bounded functional of the path that is uniformly continuous for the supremum norm on a compact
set, and never for a fixed realization of the field.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

namespace Sandpile

variable {d : ℕ}

/-- **The walk value is 1-Lipschitz in the reward.**  Two optimal-stopping values whose
rewards are uniformly within `E` differ by at most `E`. -/
theorem abs_stoppingSup_sub_le_of_reward (hd : 1 ≤ d) (n : ℕ) (x : Site d)
    (F G : ℕ → (ℕ → Site d) → ℝ) (E : ℝ)
    (hbddF : BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, F (τ X) X ∂(walkLaw d x)})
    (hbddG : BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, G (τ X) X ∂(walkLaw d x)})
    (hF : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => F (τ X) X) (walkLaw d x))
    (hG : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => G (τ X) X) (walkLaw d x))
    (hFG : ∀ k : ℕ, k ≤ n → ∀ X : ℕ → Site d, |F k X - G k X| ≤ E) :
    |stoppingSup n x F - stoppingSup n x G| ≤ E := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  refine abs_stoppingSup_sub_le n x F G E hbddF hbddG ?_
  intro τ hτ hτn
  rw [← integral_sub (hF τ hτ hτn) (hG τ hτ hτn)]
  refine le_trans (abs_integral_le_integral_abs) ?_
  calc ∫ X, |F (τ X) X - G (τ X) X| ∂(walkLaw d x)
      ≤ ∫ _X : ℕ → Site d, E ∂(walkLaw d x) := by
        refine integral_mono (((hF τ hτ hτn).sub (hG τ hτ hτn)).abs)
          (integrable_const E) ?_
        intro X
        exact hFG (τ X) (hτn X) X
    _ = E := by simp

namespace Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB]

/-- **The Brownian discount is 1-Lipschitz in the reward.**  Two Brownian discounts whose
rewards are uniformly within `E` on `[0,T]` differ by at most `E`. -/
theorem abs_brownianDiscount_sub_le_of_reward (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h h' : ℝ → Space d → ℝ) (T E : ℝ) (hT : 0 ≤ T)
    (hbdd : BddAbove (stoppingPayoffs B P h T))
    (hbdd' : BddAbove (stoppingPayoffs B P h' T))
    (hint : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P)
    (hint' : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h' (T - τ ω) (B (τ ω) ω)) P)
    (hgap : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Space d, |h s y - h' s y| ≤ E) :
    |brownianDiscount B P h T - brownianDiscount B P h' T| ≤ E := by
  refine abs_brownianDiscount_sub_le B P h h' T E hT hbdd hbdd' ?_
  intro τ hτ hτT
  rw [← integral_sub (hint τ hτ hτT) (hint' τ hτ hτT)]
  refine le_trans (abs_integral_le_integral_abs) ?_
  calc ∫ ω, |-h (T - (τ ω : ℝ)) (B (τ ω) ω) - -h' (T - (τ ω : ℝ)) (B (τ ω) ω)| ∂P
      ≤ ∫ _ω : ΩB, E ∂P := by
        refine integral_mono (((hint τ hτ hτT).sub (hint' τ hτ hτT)).abs)
          (integrable_const E) ?_
        intro ω
        have hmem : T - (τ ω : ℝ) ∈ Set.Icc (0 : ℝ) T :=
          ⟨by linarith [hτT ω], sub_le_self T (τ ω).coe_nonneg⟩
        have hrw : -h (T - (τ ω : ℝ)) (B (τ ω) ω) - -h' (T - (τ ω : ℝ)) (B (τ ω) ω)
            = -(h (T - (τ ω : ℝ)) (B (τ ω) ω) - h' (T - (τ ω : ℝ)) (B (τ ω) ω)) := by ring
        show |-h (T - (τ ω : ℝ)) (B (τ ω) ω) - -h' (T - (τ ω : ℝ)) (B (τ ω) ω)| ≤ E
        rw [hrw, abs_neg]
        exact hgap _ hmem _
    _ = E := by simp

end Continuum

/-- **One threshold serves a finite family of rewards.**  The cited stability input, applied
to the constant family at each member, gives a threshold for each; the maximum of finitely
many thresholds is a threshold for all of them at once. -/
theorem stability_uniform_of_finite (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d)
    (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (T₀ T₁ : ℝ) (hT₀ : 0 < T₀) (hT : T₀ ≤ T₁)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (N : ℕ) (G : Fin N → ℝ → Sandpile.Continuum.Space d → ℝ)
    (hGc : ∀ i, Continuous (fun p : ℝ × Sandpile.Continuum.Space d => G i p.1 p.2))
    (M : ℝ) (hGM : ∀ (i : Fin N) (s : ℝ) (y : Sandpile.Continuum.Space d), |G i s y| ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ i : Fin N,
      ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
        |Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T| ≤ ε := by
  have key : ∀ i : Fin N, ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
        |Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T| ≤ ε := by
    intro i
    exact hStab d hd ΩB PB B hB T₀ T₁ hT₀ hT K hK (G i) (hGc i) (fun _ => G i) M
      (fun s y => hGM i s y) (fun _ s y => hGM i s y)
      (fun δ hδ => ⟨1, one_pos, fun _ _ _ _ _ => by
        simp only [sub_self, abs_zero]
        exact hδ.le⟩) ε hε
  choose R₀f hR₀pos hR₀ using key
  have hsum : (0 : ℝ) ≤ ∑ j : Fin N, |R₀f j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨1 + ∑ j : Fin N, |R₀f j|, by linarith, ?_⟩
  intro R hR i T hT' x hx
  refine hR₀ i R ?_ T hT' x hx
  have h1 : R₀f i ≤ |R₀f i| := le_abs_self _
  have h2 : |R₀f i| ≤ ∑ j : Fin N, |R₀f j| :=
    Finset.single_le_sum (f := fun j => |R₀f j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  linarith

/-- A uniform bound on `[0,T₁]` transfers to the rescaled walk reward: at a step `k` of a walk
run for `⌊R²T⌋` steps, the remaining time `(⌊R²T⌋-k)/R²` lies in `[0,T₁]`. -/
theorem reward_gap_of_uniform (R T T₁ : ℝ) (hR : 0 < R) (hT : 0 ≤ T) (hTT₁ : T ≤ T₁)
    (F G : ℝ → Sandpile.Continuum.Space d → ℝ) (η : ℝ)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ y : Sandpile.Continuum.Space d, |F s y - G s y| ≤ η) :
    ∀ k : ℕ, k ≤ ⌊R ^ 2 * T⌋₊ → ∀ X : ℕ → Sandpile.Site d,
      |F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2) (Sandpile.External.Lclt.scaledSite R (X k))
        - G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X k))| ≤ η := by
  intro k hk X
  refine h _ ?_ _
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hnk : (k : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast hk
  have hfl : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le (by positivity)
  constructor
  · apply div_nonneg _ hR2.le
    linarith
  · rw [div_le_iff₀ hR2]
    nlinarith [hnk, hfl, Nat.cast_nonneg (α := ℝ) k]

/-- **The stability gap at a reward near a finite family.**  The threshold of
`stability_uniform_of_finite` does not see the reward, so a reward within `η` of a member of
the family, and in particular a RANDOM one, inherits the bound with `2η` added.  This is what
the paper's subsequence argument at `sandpile.tex:1878-1880` was for. -/
theorem stability_gap_of_near_finite (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d)
    (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (T₀ T₁ : ℝ) (hT₀ : 0 < T₀) (hT : T₀ ≤ T₁)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (N : ℕ) (G : Fin N → ℝ → Sandpile.Continuum.Space d → ℝ)
    (hGc : ∀ i, Continuous (fun p : ℝ × Sandpile.Continuum.Space d => G i p.1 p.2))
    (M : ℝ) (hGM : ∀ (i : Fin N) (s : ℝ) (y : Sandpile.Continuum.Space d), |G i s y| ≤ M)
    (ε η : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
      ∀ (F : ℝ → Sandpile.Continuum.Space d → ℝ) (i : Fin N),
        |Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k)))| ≤ η →
        |Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -F s y) T -
            Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T| ≤ η →
        |Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -F s y) T|
          ≤ ε + 2 * η := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ :=
    stability_uniform_of_finite hStab d hd ΩB PB B hB T₀ T₁ hT₀ hT K hK N G hGc M hGM ε hε
  refine ⟨R₀, hR₀pos, ?_⟩
  intro R hR T hTmem x hx F i hwalk hbm
  have hmid := hR₀ R hR i T hTmem x hx
  have h1 := abs_sub_le
    (Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
      (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
        F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R (X k))))
    (Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
      (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
        G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R (X k))))
    (Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -F s y) T)
  have h2 := abs_sub_le
    (Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
      (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
        G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R (X k))))
    (Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T)
    (Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -F s y) T)
  have h3 : |Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T -
      Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -F s y) T| ≤ η := by
    rw [abs_sub_comm]
    exact hbm
  linarith

/-- **The stability gap `E₂` of the four-term bound, supplied without a Skorokhod
representation.** -/
theorem stability_gap_of_close (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d)
    (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (T₀ T₁ : ℝ) (hT₀ : 0 < T₀) (hT : T₀ ≤ T₁)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (N : ℕ) (G : Fin N → ℝ → Sandpile.Continuum.Space d → ℝ)
    (hGc : ∀ i, Continuous fun p : ℝ × Sandpile.Continuum.Space d => G i p.1 p.2)
    (M : ℝ) (hGM : ∀ (i : Fin N) (s : ℝ) (y : Sandpile.Continuum.Space d), |G i s y| ≤ M)
    (ε η : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → 0 < R → ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
      ∀ (F : ℝ → Sandpile.Continuum.Space d → ℝ) (i : Fin N),
        (∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ y : Sandpile.Continuum.Space d, |F s y - G i s y| ≤ η) →
        BddAbove {a : ℝ | ∃ τ : (ℕ → Sandpile.Site d) → ℕ, IsWalkStopping τ ∧
          (∀ X, τ X ≤ ⌊R ^ 2 * T⌋₊) ∧ a = ∫ X, F (((⌊R ^ 2 * T⌋₊ : ℕ) - ((τ X : ℕ) : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X (τ X)))
            ∂(walkLaw d (fun j => ⌊R * x j⌋))} →
        BddAbove {a : ℝ | ∃ τ : (ℕ → Sandpile.Site d) → ℕ, IsWalkStopping τ ∧
          (∀ X, τ X ≤ ⌊R ^ 2 * T⌋₊) ∧ a = ∫ X, G i (((⌊R ^ 2 * T⌋₊ : ℕ) - ((τ X : ℕ) : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X (τ X)))
            ∂(walkLaw d (fun j => ⌊R * x j⌋))} →
        (∀ τ : (ℕ → Sandpile.Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ ⌊R ^ 2 * T⌋₊) →
          Integrable (fun X => F (((⌊R ^ 2 * T⌋₊ : ℕ) - ((τ X : ℕ) : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X (τ X))))
            (walkLaw d (fun j => ⌊R * x j⌋))) →
        (∀ τ : (ℕ → Sandpile.Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ ⌊R ^ 2 * T⌋₊) →
          Integrable (fun X => G i (((⌊R ^ 2 * T⌋₊ : ℕ) - ((τ X : ℕ) : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X (τ X))))
            (walkLaw d (fun j => ⌊R * x j⌋))) →
        BddAbove (Sandpile.Continuum.stoppingPayoffs (B x) PB (fun s y => -F s y) T) →
        BddAbove (Sandpile.Continuum.stoppingPayoffs (B x) PB (fun s y => -G i s y) T) →
        (∀ τ : ΩB → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) τ →
          (∀ ω, (τ ω : ℝ) ≤ T) →
          Integrable (fun ω => -(fun s y => -F s y) (T - τ ω) (B x (τ ω) ω)) PB) →
        (∀ τ : ΩB → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) τ →
          (∀ ω, (τ ω : ℝ) ≤ T) →
          Integrable (fun ω => -(fun s y => -G i s y) (T - τ ω) (B x (τ ω) ω)) PB) →
        |Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -F s y) T|
          ≤ ε + 2 * η := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := stability_gap_of_near_finite hStab d hd ΩB PB B hB T₀ T₁ hT₀ hT
    K hK N G (fun i => hGc i) M hGM ε η hε
  refine ⟨R₀, hR₀pos, ?_⟩
  intro R hR hRpos T hTmem x hx F i hclose hbddF hbddG hintF hintG hbdd hbdd' hint hint'
  have hT0 : (0 : ℝ) ≤ T := le_trans hT₀.le hTmem.1
  have hTT₁ : T ≤ T₁ := hTmem.2
  have hwalk : |Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
        (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
          F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X k))) -
      Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
        (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
          G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X k)))| ≤ η :=
    abs_stoppingSup_sub_le_of_reward hd _ _ _ _ η hbddF hbddG hintF hintG
      (reward_gap_of_uniform R T T₁ hRpos hT0 hTT₁ F (G i) η hclose)
  have hbm : |Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -F s y) T -
      Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T| ≤ η := by
    refine Sandpile.Continuum.abs_brownianDiscount_sub_le_of_reward (B x) PB _ _ T η hT0
      hbdd hbdd' hint hint' ?_
    intro s hs y
    have hmem : s ∈ Set.Icc (0 : ℝ) T₁ := ⟨hs.1, le_trans hs.2 hTT₁⟩
    have := hclose s hmem y
    show |(-F s y) - (-G i s y)| ≤ η
    have hrw : (-F s y) - (-G i s y) = -(F s y - G i s y) := by ring
    rw [hrw, abs_neg]
    exact this
  exact hR₀ R hR T hTmem x hx F i hwalk hbm


/-- A bounded walk reward has a bounded set of attainable payoffs. -/
theorem bddAbove_walkPayoffs_of_bound (hd : 1 ≤ d) (x : Site d) (n : ℕ)
    (F : ℕ → (ℕ → Site d) → ℝ) (M : ℝ)
    (hb : ∀ (k : ℕ) (X : ℕ → Site d), F k X ≤ M)
    (hint : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => F (τ X) X) (walkLaw d x)) :
    BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, F (τ X) X ∂(walkLaw d x)} := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  refine ⟨M, ?_⟩
  rintro a ⟨τ, hτ, hτn, rfl⟩
  calc ∫ X, F (τ X) X ∂(walkLaw d x) ≤ ∫ _X : ℕ → Site d, M ∂(walkLaw d x) := by
        refine integral_mono (hint τ hτ hτn) (integrable_const M) ?_
        intro X
        exact hb (τ X) X
    _ = M := by simp


end Sandpile
