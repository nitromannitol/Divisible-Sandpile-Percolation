import Sandpile.External.ContinuumRSW.MeshCrossings
import Sandpile.External.ContinuumRSW
import Sandpile.Support.CrossZeroLimit

/-!
# Continuum RSW from planar RSW

Discretization of continuous fields transfers the planar lattice comparison to
compact connected continuum crossings at arbitrary real aspect ratios.
-/

open Filter MeasureTheory Set Topology

namespace Sandpile.External.ContinuumRSW

open Sandpile Sandpile.Continuum Sandpile.Support Sandpile.Frozen.FixedScaleCrossings

/-- Sampled crossing events are measurable. -/
theorem measurableSet_sampledCrossingEvent {Ω : Type} [MeasurableSpace Ω]
    {X : Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    (t level : ℝ) (w h : ℕ) : MeasurableSet (sampledCrossingEvent X t level w h) := by
  exact (measurableSet_planarCrossingEvent w h (1 / 2)).preimage
    (measurable_binaryToReal.comp (measurable_sampledThreshold hX (gridPt t) level))

/-- Crossing probabilities converge as the level increases to a limit. -/
theorem tendsto_measureReal_crosses_levels {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Space 2 → Ω → ℝ)
    (hX : ∀ u, Measurable (X u)) (hc : ∀ᵐ ω ∂P, Continuous fun x => X x ω)
    (a b : Fin 2 → ℝ) (hab : ∀ i, a i < b i) (level : ℝ) :
    Tendsto (fun n : ℕ => P.real {ω | Crosses a b 0
      {x | level - 1 / ((n : ℝ) + 1) ≤ X x ω}}) atTop
      (𝓝 (P.real {ω | Crosses a b 0 {x | level ≤ X x ω}})) := by
  let E : ℕ → Set Ω := fun n => {ω | Crosses a b 0
    {x | level - 1 / ((n : ℝ) + 1) ≤ X x ω}}
  have hmono : Antitone E := by
    intro n m hnm ω hω
    apply crosses_level_mono ?_ hω
    exact sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 1)) _
  have hnull : ∀ n, NullMeasurableSet (E n) P := fun n =>
    nullMeasurableSet_crossing P X a b 0 hab _ hX hc
  have hrepr : (⋂ n, E n) =ᵐ[P] {ω | Crosses a b 0 {x | level ≤ X x ω}} := by
    filter_upwards [hc] with ω hω
    apply propext
    constructor
    · intro h
      apply crosses_of_monotone_levels hω
        (l := fun n : ℕ => level - 1 / ((n : ℝ) + 1))
      · intro n m hnm
        exact sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hnm 1)) _
      · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub level
      · exact fun n => mem_iInter.mp h n
    · intro h
      apply mem_iInter.mpr
      intro n
      apply crosses_level_mono ?_ h
      have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hlim : Tendsto (fun n => P (E n)) atTop (𝓝 (P (⋂ n, E n))) :=
    tendsto_measure_iInter_atTop hnull hmono ⟨0, measure_ne_top P _⟩
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp hlim
  simpa only [Measure.real, Function.comp_def, E, measure_congr hrepr] using hreal

/-- The continuum comparison follows from the planar lattice comparison. -/
theorem continuumRSW_of_planarRSW (hRSW : Sandpile.External.PlanarRSW) :
    Sandpile.External.ContinuumRSW := by
  intro ρ hρ
  let M : ℕ := ⌈ρ⌉₊ + 1
  have hρM : ρ ≤ M := by
    have := Nat.le_ceil ρ
    dsimp [M]
    push_cast
    linarith
  have hM : 1 ≤ M := by dsimp [M]; omega
  obtain ⟨ψ, hψ⟩ := sampled_grid_crossing_comparison hRSW M hM
  refine ⟨ψ, ?_⟩
  intro Ω _ P _ X hX hc hsym hassoc R hR level
  have hRpos : 0 < R := by linarith
  let A : Set Ω := {ω | Crosses ![0, 0] ![2 * R, 2 * ρ * R] 0
    {x | level ≤ X x ω}}
  let B : ℕ → Set Ω := fun k => {ω | Crosses ![0, 0] ![2 * ρ * R, 2 * R] 0
    {x | level - 1 / ((k : ℝ) + 1) ≤ X x ω}}
  have hbound : ∀ k, (ψ (probabilityInUnitInterval P A) : ℝ) ≤ P.real (B k) := by
    intro k
    let ε : ℝ := 1 / (2 * ((k : ℝ) + 1))
    have hε : 0 < ε := by dsimp [ε]; positivity
    let E : ℕ → Set Ω := fun n => sampledCrossingEvent X (crossingMesh R n) (level - ε)
      (2 * (n + 1)) (2 * M * (n + 1))
    let F : ℕ → Set Ω := fun n => sampledCrossingEvent X (crossingMesh R n) (level - ε)
      (2 * M * (n + 1)) (2 * (n + 1))
    have hEm : ∀ n, MeasurableSet (E n) := fun n =>
      measurableSet_sampledCrossingEvent hX _ _ _ _
    have hFm : ∀ n, MeasurableSet (F n) := fun n =>
      measurableSet_sampledCrossingEvent hX _ _ _ _
    have hcomp : ∀ n, (ψ (probabilityInUnitInterval P (E n)) : ℝ) ≤ P.real (F n) := by
      intro n
      exact hψ Ω P X hX hsym hassoc (crossingMesh R n) (level - ε) (n + 1) (by omega)
    have happ : ∀ᵐ ω ∂P, (ω ∈ A → ∃ N, ∀ n ≥ N, ω ∈ E n) ∧
        ((∀ N, ∃ n ≥ N, ω ∈ F n) → ω ∈ B k) := by
      filter_upwards [hc] with ω hω
      constructor
      · intro hcross
        exact eventually_sampled_tall_of_crosses hω hRpos hρ hρM hε hcross
      · intro hfreq
        obtain ⟨N, hN⟩ := eventually_crosses_of_sampled_wide (X := X) (ω := ω)
          hω hRpos hρ hρM hε (level := level)
        obtain ⟨n, hn, hfn⟩ := hfreq N
        have hcross := hN n hn hfn
        have heq : level - 2 * ε = level - 1 / ((k : ℝ) + 1) := by
          dsimp [ε]
          field_simp
        change Crosses ![0, 0] ![2 * ρ * R, 2 * R] 0
          {x | level - 1 / ((k : ℝ) + 1) ≤ X x ω}
        simpa only [heq] using hcross
    exact comparison_of_eventual_event_bounds P ψ A (B k) E F hEm hFm hcomp happ
  have hab : ∀ i : Fin 2, (![0, 0] : Fin 2 → ℝ) i < ![2 * ρ * R, 2 * R] i := by
    intro i
    fin_cases i <;> simp <;> positivity
  have hlim : Tendsto (fun k => P.real (B k)) atTop
      (𝓝 (P.real {ω | Crosses ![0, 0] ![2 * ρ * R, 2 * R] 0
        {x | level ≤ X x ω}})) :=
    tendsto_measureReal_crosses_levels P X hX hc ![0, 0] ![2 * ρ * R, 2 * R] hab level
  change (ψ (probabilityInUnitInterval P A) : ℝ) ≤ _
  exact ge_of_tendsto hlim (Eventually.of_forall hbound)

end Sandpile.External.ContinuumRSW
