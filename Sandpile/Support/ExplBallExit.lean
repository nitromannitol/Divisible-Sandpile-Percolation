/-
The exit time of a Euclidean ball for the Brownian motion of
`ssec:localization` (`sandpile.tex:1636-1646`), and its tail.

`lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) replaces each
stopping time `τ` by `τ ∧ τ_{u,A}`, where `τ_{u,A}` is the exit time of the
Euclidean ball of radius `A` about `u`, and pays the probability that the ball
is left before time `T`.  This module supplies the two halves of that sentence
which need nothing about the field:

- the tail `P(τ_{u,A} < T) ≤ C e^{-cA²/T}`, the continuum analogue of
  `eq:rw-max-displacement`.  It is the library's Brownian exit estimate read in
  the vocabulary of this repository: the three clauses of
  `Sandpile.Continuum.IsBrownian` are verbatim those of
  `LatticeProb.IsBrownianSpace`, so no continuity and no measurability of the
  motion is needed for it.  Both the open form (`A < ‖B s ω - u‖`) and the
  closed form (`A ≤ ‖B s ω - u‖`, the event the exit time itself defines) are
  proved, with the SAME constants and both depending only on the dimension: the
  closed event at level `A` is contained in the open event at every level
  `A' < A`, and the bound is continuous in the level, so no rate is halved and
  no horizon enters the constants.

- the fact that `τ ∧ τ_{u,A}` is again an admissible stopping time of the value
  and has not left the ball strictly before it stops, so that its payoff belongs
  to the attainable set of the localized value `𝒰_{Z,A}`. Natural-filtration
  stopping times are stable under minima, and the exit time of a closed ball is
  a stopping time for a motion with continuous paths.
-/
import Sandpile.Continuum.Stopping
import LatticeProb

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {Ω : Type*} {d : ℕ}

/-- The Brownian motion of this repository is the Brownian motion of the library: the three
clauses of the two predicates are the same. -/
theorem isBrownianSpace_of_isBrownian [MeasurableSpace Ω] {x : Space d}
    {B : ℝ≥0 → Ω → Space d} {P : Measure Ω} (hB : IsBrownian d x B P) :
    LatticeProb.IsBrownianSpace d x B P :=
  ⟨hB.start, hB.coord, hB.indep⟩

/-- **The Brownian exit-time tail.**  The probability that the motion started at `u` reaches
distance more than `A` from `u` before time `T` is at most `C e^{-cA²/T}`, with `C` and `c`
depending only on the dimension. -/
theorem exists_ball_exit_tail (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (u : Space d) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → Space d, IsBrownian d u B P →
          ∀ A : ℝ, 1 ≤ A → ∀ T : ℝ, 0 < T →
            P.real {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A < ‖B s ω - u‖}
              ≤ C * Real.exp (-(c * A ^ 2 / T)) := by
  obtain ⟨C, c, hC, hc, h⟩ := LatticeProb.brownian_exit_tail d
  refine ⟨C, c, hC, hc, ?_⟩
  intro u Ω mΩ P hP B hB A hA T hT
  have hle := h u Ω P hP B (isBrownianSpace_of_isBrownian hB) A hA T hT
  have hpos : (0 : ℝ) ≤ C * Real.exp (-(c * A ^ 2 / T)) := by positivity
  calc P.real {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A < ‖B s ω - u‖}
      = (P {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A < ‖B s ω - u‖}).toReal := rfl
    _ ≤ (ENNReal.ofReal (C * Real.exp (-(c * A ^ 2 / T)))).toReal :=
        ENNReal.toReal_mono (by simp) hle
    _ = C * Real.exp (-(c * A ^ 2 / T)) := ENNReal.toReal_ofReal hpos

/-- **The exit-time tail for the closed ball**, the event `{τ_{u,A} < T}` of
`ssec:localization`: the motion reaches distance at least `A` from `u` before time `T`.
The constants depend only on the dimension: they are bound before the level `A` and
before the horizon `T`. -/
theorem exists_ball_exit_tail_closed_uniform (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (u : Space d) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → Space d, IsBrownian d u B P →
          ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T →
            P.real {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A ≤ ‖B s ω - u‖}
              ≤ C * Real.exp (-(c * A ^ 2 / T)) := by
  obtain ⟨C, c, hC, hc, h⟩ := LatticeProb.brownian_exit_tail_closed d
  refine ⟨C, c, hC, hc, ?_⟩
  intro u Ω mΩ P hP B hB A hA T hT
  have hle := h u Ω P hP B (isBrownianSpace_of_isBrownian hB) A hA T hT
  have hpos : (0 : ℝ) ≤ C * Real.exp (-(c * A ^ 2 / T)) := by positivity
  calc P.real {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A ≤ ‖B s ω - u‖}
      = (P {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A ≤ ‖B s ω - u‖}).toReal := rfl
    _ ≤ (ENNReal.ofReal (C * Real.exp (-(c * A ^ 2 / T)))).toReal :=
        ENNReal.toReal_mono (by simp) hle
    _ = C * Real.exp (-(c * A ^ 2 / T)) := ENNReal.toReal_ofReal hpos

/-- **The exit-time tail for the closed ball** at a fixed horizon, the form the localization
lemma consumes. -/
theorem exists_ball_exit_tail_closed (d : ℕ) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (u : Space d) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → Space d, IsBrownian d u B P →
          ∀ A : ℝ, 1 ≤ A →
            P.real {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A ≤ ‖B s ω - u‖}
              ≤ C * Real.exp (-(c * A ^ 2 / T)) := by
  obtain ⟨C, c, hC, hc, h⟩ := exists_ball_exit_tail_closed_uniform d
  exact ⟨C, c, hC, hc, fun u Ω mΩ P hP B hB A hA =>
    h u Ω mΩ P hP B hB A (by linarith) T hT⟩

/-- Natural-filtration stopping times are stable under minima. -/
theorem isBrownianStopping_min {B : ℝ≥0 → Ω → Space d} {τ σ : Ω → ℝ≥0}
    (hτ : IsBrownianStopping B τ) (hσ : IsBrownianStopping B σ) :
    IsBrownianStopping B fun ω => min (τ ω) (σ ω) := by
  intro t
  convert! (hτ t).union (hσ t) using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_union]
  change ((min (τ ω) (σ ω) : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞) ↔
    (τ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞) ∨ (σ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)
  rw [ENNReal.coe_min]
  exact min_le_iff

/-- The exit time of a closed ball, stopped at a horizon, is a natural-filtration stopping
time for a motion with continuous paths. -/
theorem isBrownianStopping_exitTimeTrunc {B : ℝ≥0 → Ω → Space d}
    (hcont : ∀ ω, Continuous fun s => B s ω) (u : Space d) (A : ℝ) (Tn : ℝ≥0) :
    IsBrownianStopping B (LatticeProb.exitTimeTrunc B u A Tn) := by
  letI : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => fun t => B t ω) inferInstance
  have hp : Measurable (fun ω => fun t => B t ω) := measurable_iff_comap_le.mpr le_rfl
  have hm : ∀ t, StronglyMeasurable (B t) := fun t => ((measurable_pi_apply t).comp hp).stronglyMeasurable
  exact (Sandpile.Continuum.isBrownianStopping_iff_natFiltration B hm _).2
    (LatticeProb.isStoppingTime_exitTimeTrunc hm hcont u A Tn)


/-- A time bounded by the exit time of the ball has not left the ball strictly before it
stops, which is the clause defining the attainable set of `𝒰_{Z,A}`. -/
theorem ball_condition_of_le_exitTime {B : ℝ≥0 → Ω → Space d}
    (hcont : ∀ ω, Continuous fun s => B s ω) (u : Space d) (A : ℝ) (τ : Ω → ℝ≥0)
    (hle : ∀ ω, ((τ ω : ℝ≥0) : ℝ≥0∞) ≤ LatticeProb.exitTime B u A ω) :
    ∀ ω, ∀ s : ℝ≥0, s < τ ω → ‖B s ω - u‖ ≤ A := by
  intro ω s hs
  have hlt : ((s : ℝ≥0) : ℝ≥0∞) < LatticeProb.exitTime B u A ω :=
    lt_of_lt_of_le (by exact_mod_cast hs) (hle ω)
  have hnot : ¬ (LatticeProb.exitTime B u A ω ≤ ((s : ℝ≥0) : ℝ≥0∞)) := not_le.2 hlt
  rw [LatticeProb.exitTime_le_iff hcont u A ω s] at hnot
  push Not at hnot
  exact le_of_lt (hnot s le_rfl)

end Sandpile.Continuum
