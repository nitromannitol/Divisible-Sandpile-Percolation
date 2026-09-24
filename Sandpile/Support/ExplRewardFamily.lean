/-
The finite family of continuous cut-off rewards.

`Sandpile.exists_finite_family_of_compact` builds, on a compact set, a finite
family of globally continuous functions within `2η` of every function obeying a
uniform bound and one oscillation bound.  The rewards of the proof of Theorem
1.3(i)(b) are the cut-off fields `χ_A(y) Z_R^{lin}(s,y)`, which live on
`[0,T₁] × \overline{B(0,2A)}` and vanish outside it, so this module transports
the family through the cutoff: multiplying each member by `χ_A` keeps it
continuous and bounded, makes the approximation valid at EVERY point of
`[0,T₁] × ℝ^d` rather than only on the box, and costs nothing, because outside
the box both the cut-off field and the cut-off family member are zero.

The two hypotheses on the field are exactly the complements of the two events of
the tightness clause of `prop:dlt4-heat-potential-invariance`, written as the
proposition writes them.
-/
import Sandpile.Support.ExplNetFamily
import Sandpile.Support.ExplCutoff

open Metric

namespace Sandpile.Continuum

variable {d : ℕ}

/-- The compact set the cut-off reward lives on. -/
def rewardBox (d : ℕ) (T₁ A : ℝ) : Set (ℝ × Space d) :=
  Set.Icc (0 : ℝ) T₁ ×ˢ Metric.closedBall (0 : Space d) (2 * A)

theorem isCompact_rewardBox (d : ℕ) (T₁ A : ℝ) : IsCompact (rewardBox d T₁ A) :=
  isCompact_Icc.prod (isCompact_closedBall _ _)

/-- **A finite family of continuous cut-off rewards.** -/
theorem exists_cutoff_reward_family (d : ℕ) (A T₁ : ℝ) (hA : 0 < A)
    (M η δ : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ (N : ℕ) (G : Fin N → ℝ → Space d → ℝ),
      (∀ i, Continuous fun p : ℝ × Space d => G i p.1 p.2) ∧
      (∀ (i : Fin N) (s : ℝ) (y : Space d), |G i s y| ≤ M + η) ∧
      ∀ v : ℝ → Space d → ℝ,
        (¬ ∃ p ∈ rewardBox d T₁ A, M < |v p.1 p.2|) →
        (¬ ∃ p ∈ rewardBox d T₁ A, ∃ q ∈ rewardBox d T₁ A,
            dist p q < δ ∧ η < |v p.1 p.2 - v q.1 q.2|) →
        ∃ i, ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ y : Space d,
          |cutoff A y * v s y - G i s y| ≤ 2 * η := by
  obtain ⟨N, g, hgc, hgb, happ⟩ :=
    Sandpile.exists_finite_family_of_compact (isCompact_rewardBox d T₁ A) M η δ hη hδ hM
  refine ⟨N, fun i s y => cutoff A y * g i (s, y), ?_, ?_, ?_⟩
  · intro i
    exact ((continuous_cutoff A).comp continuous_snd).mul (hgc i)
  · intro i s y
    have h0 : 0 ≤ cutoff A y := cutoff_nonneg A y
    have h1 : cutoff A y ≤ 1 := cutoff_le_one A y
    have hb := hgb i (s, y)
    rw [abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg (g i (s, y))]
  · intro v h1 h2
    push Not at h1 h2
    obtain ⟨i, hi⟩ := happ (fun p => v p.1 p.2) (fun p hp => h1 p hp)
      (fun p hp q hq hd => h2 p hp q hq hd)
    refine ⟨i, ?_⟩
    intro s hs y
    rcases le_or_gt (2 * A) ‖y‖ with hy | hy
    · show |cutoff A y * v s y - cutoff A y * g i (s, y)| ≤ 2 * η
      rw [cutoff_eq_zero_of_norm_ge A hA y hy]
      have hz : (0 : ℝ) * v s y - 0 * g i (s, y) = 0 := by ring
      rw [hz, abs_zero]
      positivity
    · have hmem : ((s, y) : ℝ × Space d) ∈ rewardBox d T₁ A := by
        refine ⟨hs, ?_⟩
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact hy.le
      have hgap := hi (s, y) hmem
      have h0 : 0 ≤ cutoff A y := cutoff_nonneg A y
      have hle1 : cutoff A y ≤ 1 := cutoff_le_one A y
      have hrw : cutoff A y * v s y - cutoff A y * g i (s, y)
          = cutoff A y * (v s y - g i (s, y)) := by ring
      show |cutoff A y * v s y - cutoff A y * g i (s, y)| ≤ 2 * η
      rw [hrw, abs_mul, abs_of_nonneg h0]
      nlinarith [abs_nonneg (v s y - g i (s, y))]

end Sandpile.Continuum
