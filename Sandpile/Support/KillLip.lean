/-
The two values of `rem:dlt4-killed-scaling` are 1-Lipschitz in the reward.

The proof of Theorem 1.3(i)(b) compares an optimal-stopping value of the rescaled
field with the Brownian value of the limiting field by inserting a third reward
between them, and every such insertion costs the supremum distance between the two
rewards, because a supremum of integrals of rewards within `E` of each other moves by
at most `E`.  That is `Sandpile.abs_stoppingSup_sub_le_of_reward` and
`Sandpile.Continuum.abs_brownianDiscount_sub_le_of_reward` in the unkilled problem;
the killed forms are proved here, for the value killed on leaving a set of sites and
for the value killed on leaving a cube.

The killed Brownian value evaluates its reward at the stopping position, which the
killing condition constrains only STRICTLY BEFORE the stopping time.  A motion with
continuous paths that starts at `u` is nevertheless in the CLOSED cube when it stops
(`ae_cube_at_stop`), so a reward comparison valid on the closed cube is enough; and a
Brownian motion has almost surely continuous paths, because each of its coordinates,
centred and scaled, is a real Brownian motion (`ae_continuous_of_isBrownian`).  That
is what lets the comparison of the two rewards be made only where the killed motion
can go.
-/
import Sandpile.Support.KillRep
import Sandpile.Support.ExplStability
import Sandpile.Support.ExplKilledValue

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The killed payoff set is bounded above as soon as the unkilled one is. -/
theorem bddAbove_killedSet (D : Set (Site d)) (n : ℕ) (x : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ)
    (hbdd : BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, F (τ X) X ∂(walkLaw d x)}) :
    BddAbove (killedSet D n x F) :=
  hbdd.mono (killedSet_subset D n x F)

/-- Two killed values built from rewards whose payoffs differ by at most `E` differ by at
most `E`. -/
theorem abs_killedStoppingSup_sub_le (D : Set (Site d)) (n : ℕ) (x : Site d)
    (F G : ℕ → (ℕ → Site d) → ℝ) (E : ℝ)
    (hbddF : BddAbove (killedSet D n x F)) (hbddG : BddAbove (killedSet D n x G))
    (hFG : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      (∀ X, ∀ j < τ X, X j ∈ D) →
      |(∫ X, F (τ X) X ∂(walkLaw d x)) - ∫ X, G (τ X) X ∂(walkLaw d x)| ≤ E) :
    |killedStoppingSup D n x F - killedStoppingSup D n x G| ≤ E := by
  rw [abs_sub_le_iff]
  constructor
  · refine sub_le_iff_le_add.2 (csSup_le (killedSet_nonempty D n x F) ?_)
    rintro a ⟨τ, hτ, hτn, hkill, rfl⟩
    have h1 := hFG τ hτ hτn hkill
    rw [abs_sub_le_iff] at h1
    have h2 : (∫ X, G (τ X) X ∂(walkLaw d x)) ≤ killedStoppingSup D n x G :=
      le_csSup hbddG ⟨τ, hτ, hτn, hkill, rfl⟩
    linarith [h1.1]
  · refine sub_le_iff_le_add.2 (csSup_le (killedSet_nonempty D n x G) ?_)
    rintro a ⟨τ, hτ, hτn, hkill, rfl⟩
    have h1 := hFG τ hτ hτn hkill
    rw [abs_sub_le_iff] at h1
    have h2 : (∫ X, F (τ X) X ∂(walkLaw d x)) ≤ killedStoppingSup D n x F :=
      le_csSup hbddF ⟨τ, hτ, hτn, hkill, rfl⟩
    linarith [h1.2]

/-- **The killed walk value is 1-Lipschitz in the reward.** -/
theorem abs_killedStoppingSup_sub_le_of_reward (hd : 1 ≤ d) (D : Set (Site d)) (n : ℕ)
    (x : Site d) (F G : ℕ → (ℕ → Site d) → ℝ) (E : ℝ)
    (hbddF : BddAbove (killedSet D n x F)) (hbddG : BddAbove (killedSet D n x G))
    (hF : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => F (τ X) X) (walkLaw d x))
    (hG : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => G (τ X) X) (walkLaw d x))
    (hFG : ∀ k : ℕ, k ≤ n → ∀ X : ℕ → Site d, |F k X - G k X| ≤ E) :
    |killedStoppingSup D n x F - killedStoppingSup D n x G| ≤ E := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  refine abs_killedStoppingSup_sub_le D n x F G E hbddF hbddG ?_
  intro τ hτ hτn _
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

/-- A Brownian motion on `ℝ^d` has almost surely continuous paths, because each of its
coordinates, centred and scaled by `√d`, is a real Brownian motion. -/
theorem ae_continuous_of_isBrownian (hd : 1 ≤ d) {x : Space d} {B : ℝ≥0 → ΩB → Space d}
    {P : Measure ΩB} (hB : IsBrownian d x B P) :
    ∀ᵐ ω ∂P, Continuous fun s : ℝ≥0 => B s ω := by
  have hsq : Real.sqrt (d : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hd
    positivity
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin d,
      Continuous fun t : ℝ≥0 => Real.sqrt (d : ℝ) * (B t ω i - x i) := by
    rw [ae_all_iff]
    exact fun i => (hB.coord i).cont
  filter_upwards [hall] with ω hω
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  have h1 : Continuous fun t : ℝ≥0 =>
      (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ) * (B t ω i - x i)) + x i :=
    ((hω i).const_mul _).add_const _
  have h2 : (fun t : ℝ≥0 =>
      (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ) * (B t ω i - x i)) + x i)
      = fun t : ℝ≥0 => B t ω i := by
    funext t
    rw [← mul_assoc, inv_mul_cancel₀ hsq, one_mul]
    ring
  rw [h2] at h1
  exact h1

/-- **A killed motion is in the closed cube when it stops.**  The killing condition
constrains the path only strictly before the stopping time; continuity of the paths and the
starting point carry it to the stopping time itself. -/
theorem ae_cube_at_stop (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (u : Space d) (L : ℝ)
    (hL : 0 ≤ L) (hcont : ∀ᵐ ω ∂P, Continuous fun s : ℝ≥0 => B s ω)
    (hstart : ∀ᵐ ω ∂P, B 0 ω = u) (τ : ΩB → ℝ≥0)
    (hcube : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ∀ i, |B s ω i - u i| ≤ L) :
    ∀ᵐ ω ∂P, ∀ i, |B (τ ω) ω i - u i| ≤ L := by
  filter_upwards [hcont, hstart, hcube] with ω hc hs hcubeω
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ τ ω by simp) with h0 | h0
  · intro i
    rw [← h0, hs]
    simpa using hL
  · have hS : IsClosed {s : ℝ≥0 | ∀ i, |B s ω i - u i| ≤ L} := by
      have hEq : {s : ℝ≥0 | ∀ i, |B s ω i - u i| ≤ L}
          = ⋂ i : Fin d, {s : ℝ≥0 | |B s ω i - u i| ≤ L} := by
        ext s
        simp [Set.mem_iInter]
      rw [hEq]
      refine isClosed_iInter fun i => ?_
      exact isClosed_le ((((by fun_prop : Continuous fun y : Space d => y.ofLp i)).comp hc).sub
        continuous_const).abs continuous_const
    have hsub : Set.Iio (τ ω) ⊆ {s : ℝ≥0 | ∀ i, |B s ω i - u i| ≤ L} :=
      fun s hs' => hcubeω s hs'
    have hmem : τ ω ∈ closure (Set.Iio (τ ω)) := by
      rw [closure_Iio' (a := τ ω) ⟨0, h0⟩]
      exact Set.mem_Iic.mpr le_rfl
    exact hS.closure_subset_iff.mpr hsub hmem

/-- Two cube-killed discounts built from rewards whose payoffs differ by at most `E` differ
by at most `E`. -/
theorem abs_brownianDiscountCube_sub_le (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h h' : ℝ → Space d → ℝ) (T L E : ℝ) (hT : 0 ≤ T) (u : Space d)
    (hbdd : BddAbove (cubeStoppingPayoffs B P h T L u))
    (hbdd' : BddAbove (cubeStoppingPayoffs B P h' T L u))
    (hgap : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      (∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ∀ i, |B s ω i - u i| ≤ L) →
      |(∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P) - ∫ ω, -h' (T - τ ω) (B (τ ω) ω) ∂P| ≤ E) :
    |brownianDiscountCube B P h T L u - brownianDiscountCube B P h' T L u| ≤ E := by
  rw [abs_sub_le_iff]
  constructor
  · refine sub_le_iff_le_add.2
      (csSup_le (cubeStoppingPayoffs_nonempty B P h T L hT u) ?_)
    rintro a ⟨τ, hτ, hτT, hkill, rfl⟩
    have h1 := hgap τ hτ hτT hkill
    rw [abs_sub_le_iff] at h1
    have h2 : (∫ ω, -h' (T - τ ω) (B (τ ω) ω) ∂P) ≤ brownianDiscountCube B P h' T L u :=
      le_csSup hbdd' ⟨τ, hτ, hτT, hkill, rfl⟩
    linarith [h1.1]
  · refine sub_le_iff_le_add.2
      (csSup_le (cubeStoppingPayoffs_nonempty B P h' T L hT u) ?_)
    rintro a ⟨τ, hτ, hτT, hkill, rfl⟩
    have h1 := hgap τ hτ hτT hkill
    rw [abs_sub_le_iff] at h1
    have h2 : (∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P) ≤ brownianDiscountCube B P h T L u :=
      le_csSup hbdd ⟨τ, hτ, hτT, hkill, rfl⟩
    linarith [h1.2]

/-- **The cube-killed Brownian discount is 1-Lipschitz in the reward, and only on the
cube**: two rewards that agree to within `E` on `[0,T]` times the closed cube of half-width
`L` about `u` give cube-killed discounts within `E`, because a killed motion never leaves
that cube. -/
theorem abs_brownianDiscountCube_sub_le_of_reward (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h h' : ℝ → Space d → ℝ) (T L E : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (u : Space d)
    (hcont : ∀ᵐ ω ∂P, Continuous fun s : ℝ≥0 => B s ω) (hstart : ∀ᵐ ω ∂P, B 0 ω = u)
    (hbdd : BddAbove (cubeStoppingPayoffs B P h T L u))
    (hbdd' : BddAbove (cubeStoppingPayoffs B P h' T L u))
    (hint : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P)
    (hint' : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h' (T - τ ω) (B (τ ω) ω)) P)
    (hgap : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Space d, (∀ i, |y i - u i| ≤ L) →
      |h s y - h' s y| ≤ E) :
    |brownianDiscountCube B P h T L u - brownianDiscountCube B P h' T L u| ≤ E := by
  refine abs_brownianDiscountCube_sub_le B P h h' T L E hT u hbdd hbdd' ?_
  intro τ hτ hτT hkill
  rw [← integral_sub (hint τ hτ hτT) (hint' τ hτ hτT)]
  refine le_trans (abs_integral_le_integral_abs) ?_
  have hbound : (∫ ω, |-h (T - (τ ω : ℝ)) (B (τ ω) ω) - -h' (T - (τ ω : ℝ)) (B (τ ω) ω)| ∂P)
      ≤ ∫ _ω : ΩB, E ∂P := by
    refine integral_mono_ae (((hint τ hτ hτT).sub (hint' τ hτ hτT)).abs)
      (integrable_const E) ?_
    filter_upwards [ae_cube_at_stop B P u L hL hcont hstart τ hkill] with ω hω
    have hmem : T - (τ ω : ℝ) ∈ Set.Icc (0 : ℝ) T :=
      ⟨by linarith [hτT ω], sub_le_self T (τ ω).coe_nonneg⟩
    have hrw : -h (T - (τ ω : ℝ)) (B (τ ω) ω) - -h' (T - (τ ω : ℝ)) (B (τ ω) ω)
        = -(h (T - (τ ω : ℝ)) (B (τ ω) ω) - h' (T - (τ ω : ℝ)) (B (τ ω) ω)) := by ring
    show |-h (T - (τ ω : ℝ)) (B (τ ω) ω) - -h' (T - (τ ω : ℝ)) (B (τ ω) ω)| ≤ E
    rw [hrw, abs_neg]
    exact hgap _ hmem _ hω
  simpa using hbound

end Continuum

end Sandpile
