import Sandpile.Support.KillCutoff
import Sandpile.External.CubeStoppingStability

/-!
# The stability gap for the killed cube problem

The stability gap of `rem:dlt4-killed-scaling`, in the shape the assembly consumes.

This is the killed twin of `Sandpile/Support/ExplStability.lean`, and the argument
is that file's, word for word, with both values killed.  The cited input
`Sandpile.External.CubeStoppingStability` delivers the gap between the killed walk
value and the cube-killed Brownian discount, but only for a FIXED family of rewards
converging uniformly; the paper reaches such a family by a subsequence argument
(`sandpile.tex:1878-1880`, carried over to the remark without change).  The
threshold the cited input produces does not see the reward, so:

* applied to the CONSTANT family at each member of a FINITE collection of rewards,
  it produces ONE threshold that serves the whole collection
  (`killed_stability_uniform_of_finite`);

* both killed values are 1-Lipschitz in the reward
  (`Sandpile.abs_killedStoppingSup_sub_le_of_reward` and
  `Sandpile.Continuum.abs_brownianDiscountCube_sub_le_of_reward`), so a reward within
  `η` of a member of the collection inherits the bound with `2η` added
  (`killed_stability_gap_of_near_finite` and `killed_stability_gap_of_close`).

The reward may then be RANDOM, because the threshold does not see it.  The Brownian
half of the Lipschitz step is where the killed problem differs from the unkilled one:
the comparison of the two rewards is needed only on the closed cube, because a killed
motion never leaves it, and the motion's almost sure path continuity comes from
`IsBrownian` itself.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- **One threshold serves a finite family of rewards**, in the killed problem: the cited
input, applied to the constant family at each member, gives a threshold for each, and the
maximum of finitely many thresholds is a threshold for all of them at once. -/
theorem killed_stability_uniform_of_finite (hStab : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 1 ≤ d)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
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
        |Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
              ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -G i s y) T 1 x| ≤ ε := by
  have key : ∀ i : Fin N, ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
        |Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
              ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -G i s y) T 1 x|
          ≤ ε := by
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

/-- **The killed stability gap at a reward near a finite family.** -/
theorem killed_stability_gap_of_near_finite
    (hStab : Sandpile.External.CubeStoppingStability) (d : ℕ) (hd : 1 ≤ d)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
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
        |Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
              ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
              ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k)))| ≤ η →
        |Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -F s y) T 1 x -
            Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -G i s y) T 1 x| ≤ η →
        |Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
              ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -F s y) T 1 x|
          ≤ ε + 2 * η := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ :=
    killed_stability_uniform_of_finite hStab d hd ΩB PB B hB T₀ T₁ hT₀ hT K hK N G hGc M hGM ε hε
  refine ⟨R₀, hR₀pos, ?_⟩
  intro R hR T hTmem x hx F i hwalk hbm
  have hmid := hR₀ R hR i T hTmem x hx
  have h1 := abs_sub_le
    (Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
      ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
      (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
        F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R (X k))))
    (Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
      ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
      (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
        G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R (X k))))
    (Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -F s y) T 1 x)
  have h2 := abs_sub_le
    (Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
      ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
      (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
        G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R (X k))))
    (Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -G i s y) T 1 x)
    (Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -F s y) T 1 x)
  have h3 : |Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -G i s y) T 1 x -
      Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -F s y) T 1 x| ≤ η := by
    rw [abs_sub_comm]
    exact hbm
  linarith

/-- **The killed stability gap, at a reward uniformly close to a member of the family.**
This is `E₂` of the killed assembly. -/
theorem killed_stability_gap_of_close (hStab : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 1 ≤ d)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
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
        BddAbove (Sandpile.killedSet (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
          ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
          (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
            F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
              (Sandpile.External.Lclt.scaledSite R (X k)))) →
        BddAbove (Sandpile.killedSet (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
          ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
          (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
            G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
              (Sandpile.External.Lclt.scaledSite R (X k)))) →
        (∀ τ : (ℕ → Sandpile.Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ ⌊R ^ 2 * T⌋₊) →
          Integrable (fun X => F (((⌊R ^ 2 * T⌋₊ : ℕ) - ((τ X : ℕ) : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X (τ X))))
            (walkLaw d (fun j => ⌊R * x j⌋))) →
        (∀ τ : (ℕ → Sandpile.Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ ⌊R ^ 2 * T⌋₊) →
          Integrable (fun X => G i (((⌊R ^ 2 * T⌋₊ : ℕ) - ((τ X : ℕ) : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X (τ X))))
            (walkLaw d (fun j => ⌊R * x j⌋))) →
        BddAbove (Sandpile.Continuum.cubeStoppingPayoffs (B x) PB
          (fun s y => -F s y) T 1 x) →
        BddAbove (Sandpile.Continuum.cubeStoppingPayoffs (B x) PB
          (fun s y => -G i s y) T 1 x) →
        (∀ τ : ΩB → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) τ →
          (∀ ω, (τ ω : ℝ) ≤ T) →
          Integrable (fun ω => -(fun s y => -F s y) (T - τ ω) (B x (τ ω) ω)) PB) →
        (∀ τ : ΩB → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) τ →
          (∀ ω, (τ ω : ℝ) ≤ T) →
          Integrable (fun ω => -(fun s y => -G i s y) (T - τ ω) (B x (τ ω) ω)) PB) →
        |Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
              ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -F s y) T 1 x|
          ≤ ε + 2 * η := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := killed_stability_gap_of_near_finite hStab d hd ΩB PB B hB
    T₀ T₁ hT₀ hT K hK N G (fun i => hGc i) M hGM ε η hε
  refine ⟨R₀, hR₀pos, ?_⟩
  intro R hR hRpos T hTmem x hx F i hclose hbddF hbddG hintF hintG hbdd hbdd' hint hint'
  have hT0 : (0 : ℝ) ≤ T := le_trans hT₀.le hTmem.1
  have hTT₁ : T ≤ T₁ := hTmem.2
  have hwalk : |Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
        ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
        (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
          F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X k))) -
      Sandpile.killedStoppingSup (Sandpile.supBox (fun j => ⌊R * x j⌋) R)
        ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
        (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
          G i (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X k)))| ≤ η :=
    abs_killedStoppingSup_sub_le_of_reward hd _ _ _ _ _ η hbddF hbddG hintF hintG
      (reward_gap_of_uniform R T T₁ hRpos hT0 hTT₁ F (G i) η hclose)
  have hbm : |Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -F s y) T 1 x -
      Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -G i s y) T 1 x| ≤ η := by
    refine Sandpile.Continuum.abs_brownianDiscountCube_sub_le_of_reward (B x) PB _ _ T 1 η
      hT0 zero_le_one x (Sandpile.Continuum.ae_continuous_of_isBrownian hd (hB x))
      (hB x).start hbdd hbdd' hint hint' ?_
    intro s hs y _
    have hmem : s ∈ Set.Icc (0 : ℝ) T₁ := ⟨hs.1, le_trans hs.2 hTT₁⟩
    have hcl := hclose s hmem y
    show |(-F s y) - (-G i s y)| ≤ η
    have hrw : (-F s y) - (-G i s y) = -(F s y - G i s y) := by ring
    rw [hrw, abs_neg]
    exact hcl
  exact hR₀ R hR T hTmem x hx F i hwalk hbm

end Sandpile
