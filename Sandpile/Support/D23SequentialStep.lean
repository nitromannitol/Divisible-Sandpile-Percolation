import Sandpile.Support.D23Compactness
import Sandpile.Support.D23Transfer
import Sandpile.Support.D23HeatCoupling
import Sandpile.Support.D23UniformTightness
import Sandpile.Support.D23Mesh
import Sandpile.Frozen.LimitingOdometerCrossing
import Sandpile.Support.D23NormalizedTransfer
import Sandpile.Support.ContFDSeq
import Sandpile.Support.D23CubeValueRegularity
import Sandpile.Support.LimWhiteNoiseInstance
import Sandpile.Support.MeanAKolmogorov
import Sandpile.Support.ContContinuumMCT

/-!
# The sequential step of the dimension two and three percolation theorem

The sequential step of the dimension two and three percolation theorem.

The reduction is already in place: `d23BlockCrossing_of_convergent_variance`
(`D23Compactness.lean`) reduces the uniform block-crossing estimate to a statement
along a sequence of scales with convergent variance, and
`d23_critical_level_percolation_of_block_crossing` (`D23Assembly.lean`) turns that
estimate into the theorem. What is missing is the sequential step itself.

It needs `CubeStoppingStability` as well: nothing else ties the discrete odometer
to the Brownian value, and every lemma bridging `d23Field` to a continuum object
carries it.  It is a cited input, frozen and assumed, exactly as elsewhere.

It is where the continuum crossing enters. `Sandpile.Frozen.limiting_odometer_crossing`
is SEALED and gives, for a family of rectangles and directions, a horizon and a
height at which the continuum Gaussian potential crosses with positive
probability. The couplings carry that to the discrete field along the sequence:
`heat_field_coupling_seq_of_fdd` (`D23HeatCoupling.lean`) supplies the coupling
from finite-dimensional convergence, `heat_potential_tightness_uniform_of_exp_bound`
(`D23UniformTightness.lean`) the tightness that makes it uniform in the law, and
`eventually_measure_bad_block_lt_of_couplings` (`D23Transfer.lean`) converts a
coupling into a bound on the bad-block probability. The assumed bad-block
probability staying above the threshold along the whole sequence then contradicts
that bound.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile

section Helpers

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-! ### Comparison of the ball value and the cube value -/

/-- A positive multiple of the ball value is at most the cube value of the multiple of the
reward, as soon as the cube payoffs of the multiple are bounded above.  This is
`brownianValueBall_le_brownianValueCube` together with the homogeneity of the value, with the
boundedness asked only of the cube payoffs, which continuity of the reward supplies. -/
theorem mul_brownianValueBall_le_brownianValueCube {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}
    (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h : ℝ → Space d → ℝ) (a T : ℝ)
    (ha : 0 < a) (hT : 0 ≤ T) (u : Space d)
    (hbdd : BddAbove (cubeStoppingPayoffs B P (fun t y => a * h t y) T 1 u)) :
    a * brownianValueBall B P h T 1 u ≤ brownianValueCube B P (fun t y => a * h t y) T 1 u := by
  have hdisc : brownianDiscountBall B P h T 1 u ≤
      brownianDiscountCube B P (fun t y => a * h t y) T 1 u / a := by
    apply csSup_le (ballStoppingPayoffs_nonempty B P h T 1 hT u)
    intro x hx
    rw [le_div_iff₀ ha]
    obtain ⟨τ, hτ, hb, hball, rfl⟩ := hx
    have hmem : a * ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P ∈
        ballStoppingPayoffs B P (fun t y => a * h t y) T 1 u := by
      refine ⟨τ, hτ, hb, hball, ?_⟩
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      ring
    rw [mul_comm]
    exact le_csSup hbdd (ballStoppingPayoffs_subset_cube B P _ T 1 1 le_rfl u hmem)
  unfold brownianValueBall brownianValueCube
  rw [le_div_iff₀ ha] at hdisc
  nlinarith

/-- The ball value reads the reward only at non-negative times. -/
theorem brownianValueBall_congr_of_nonneg {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}
    (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h h' : ℝ → Space d → ℝ) (T A : ℝ)
    (hT : 0 ≤ T) (hh : ∀ t, 0 ≤ t → ∀ z, h t z = h' t z) (u : Space d) :
    brownianValueBall B P h T A u = brownianValueBall B P h' T A u := by
  have hset : ballStoppingPayoffs B P h T A u = ballStoppingPayoffs B P h' T A u := by
    have key : ∀ (g g' : ℝ → Space d → ℝ), (∀ t, 0 ≤ t → ∀ z, g t z = g' t z) →
        ballStoppingPayoffs B P g T A u ⊆ ballStoppingPayoffs B P g' T A u := by
      rintro g g' hg a ⟨τ, hτ, hb, hball, rfl⟩
      refine ⟨τ, hτ, hb, hball, ?_⟩
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      rw [hg _ (sub_nonneg.mpr (hb ω))]
    exact Set.Subset.antisymm (key h h' hh) (key h' h fun t ht z => (hh t ht z).symm)
  unfold brownianValueBall
  rw [hh T hT u]
  exact congrArg _ (congrArg sSup hset)

/-! ### A globally continuous version of the heat potential -/

/-- A field that is continuous on every strip `[0, N + 1] × ℝ^d` is continuous on all of
`ℝ × ℝ^d` once it is read at the non-negative part of the time. -/
theorem continuous_clampTime_of_continuousOn {d : ℕ} (G : ℝ → Space d → ℝ)
    (hG : ∀ N : ℕ, ContinuousOn (fun p : ℝ × Space d => G p.1 p.2)
      (Set.Icc (0 : ℝ) ((N : ℝ) + 1) ×ˢ (Set.univ : Set (Space d)))) :
    Continuous fun q : ℝ × Space d => G (max q.1 0) q.2 := by
  rw [continuous_iff_continuousAt]
  intro q0
  set n : ℝ := ((⌈|q0.1|⌉₊ : ℕ) : ℝ) + 1 with hn
  have hn0 : 0 ≤ n := by positivity
  have hopen : IsOpen {q : ℝ × Space d | q.1 < n} := isOpen_lt continuous_fst continuous_const
  have hmaps : Set.MapsTo (fun q : ℝ × Space d => (max q.1 0, q.2)) {q | q.1 < n}
      (Set.Icc (0 : ℝ) n ×ˢ (Set.univ : Set (Space d))) := fun q hq =>
    ⟨⟨le_max_right _ _, max_le (le_of_lt hq) hn0⟩, Set.mem_univ _⟩
  have hφ : Continuous fun q : ℝ × Space d => (max q.1 0, q.2) :=
    (continuous_fst.max continuous_const).prodMk continuous_snd
  have hon : ContinuousOn (fun q : ℝ × Space d => G (max q.1 0) q.2) {q | q.1 < n} :=
    (hG ⌈|q0.1|⌉₊).comp hφ.continuousOn hmaps
  refine hon.continuousAt (hopen.mem_nhds ?_)
  show q0.1 < n
  have h1 : |q0.1| ≤ (⌈|q0.1|⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : q0.1 ≤ |q0.1| := le_abs_self _
  linarith

/-- **A version of the heat potential that is measurable at every point and continuous at
every sample point.**  The frozen version is continuous only on strips and only almost
surely, and is not measurable; this one is read at the non-negative part of the time, which
is all the stopping values read, and is the modification of
`exists_measurable_continuous_version`. -/
theorem exists_globalHeatField {d : ℕ} (hd1 : 1 ≤ d) (hd3 : d ≤ 3)
    {ΩW : Type} [MeasurableSpace ΩW] (PW : Measure ΩW)
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (Z1 : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ (t : ℝ) (x : Space d),
      Z1 t x =ᵐ[PW] fun ω => gaussianPotential d 1 W t x ω)
    (hcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z1 p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)))) :
    ∃ Zg : ΩW → ℝ → Space d → ℝ,
      (∀ t x, Measurable fun ω => Zg ω t x) ∧
      (∀ ω, Continuous fun q : ℝ × Space d => Zg ω q.1 q.2) ∧
      (∀ᵐ ω ∂PW, ∀ t : ℝ, 0 ≤ t → ∀ x, Zg ω t x = Z1 t x ω) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x,
        (fun ω => Zg ω t x) =ᵐ[PW] fun ω => gaussianPotential d 1 W t x ω) := by
  have hXm : ∀ q : ℝ × Space d, Measurable fun ω => gaussianPotential d 1 W (max q.1 0) q.2 ω :=
    fun q => (hW.meas _ (memLp_greenTimeBM hd1 hd3 (le_max_right _ _) q.2)).const_mul _
  have hae : ∀ q : ℝ × Space d, (fun ω => Z1 (max q.1 0) q.2 ω) =ᵐ[PW]
      fun ω => gaussianPotential d 1 W (max q.1 0) q.2 ω := fun q => hmod _ _
  have hc : ∀ᵐ ω ∂PW, Continuous fun q : ℝ × Space d => Z1 (max q.1 0) q.2 ω := by
    have h := ae_all_iff.mpr fun N : ℕ => hcont ((N : ℝ) + 1) (by positivity)
    filter_upwards [h] with ω hω
    exact continuous_clampTime_of_continuousOn (fun t x => Z1 t x ω) hω
  obtain ⟨Y, hYm, hYc, hYae⟩ := exists_measurable_continuous_version
    (fun (q : ℝ × Space d) ω => Z1 (max q.1 0) q.2 ω) _ hXm hae hc
  have hYae' : ∀ᵐ ω ∂PW, ∀ t : ℝ, 0 ≤ t → ∀ x, Y (t, x) ω = Z1 t x ω := by
    filter_upwards [hYae] with ω hω t ht x
    rw [hω (t, x)]
    simp [max_eq_left ht]
  refine ⟨fun ω t x => Y (t, x) ω, fun t x => hYm (t, x), fun ω => hYc ω, hYae', ?_⟩
  intro t ht x
  filter_upwards [hYae', hmod t x] with ω h1 h2
  rw [h1 t ht x, h2]

/-! ### A measurable event inside the crossing event -/

/-- The complement of a measurable set of probability at least `1 - ε` has probability at most
`ε`. -/
theorem measure_compl_le_of_ofReal_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {S : Set Ω} (hS : MeasurableSet S) {ε : ℝ}
    (h : ENNReal.ofReal (1 - ε) ≤ P S) : P Sᶜ ≤ ENNReal.ofReal ε := by
  rw [prob_compl_eq_one_sub hS, tsub_le_iff_right]
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ε + ENNReal.ofReal (1 - ε) := by
    have := ENNReal.ofReal_add_le (p := ε) (q := 1 - ε)
    rwa [add_sub_cancel, ENNReal.ofReal_one] at this
  exact h1.trans (add_le_add le_rfl h)

/-- **A measurable event of large probability inside the crossing event.**  The crossing event
of a field that is continuous in the parameter need not be measurable, and the crossing theorem
bounds only its outer measure from below; that does not bound the outer measure of the
complement.  But the crossing event agrees almost surely with the measurable representative
`closedCrossEvent` of the field, and a set of outer measure at least `1 - ε` that is almost
surely inside a measurable set forces that measurable set to have probability at least
`1 - ε`. -/
theorem exists_crossing_good_set {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (a b : Fin N → Fin 2 → ℝ)
    (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i) (dir : Fin N → Fin 2)
    (X : Ω → Space 2 → ℝ) (hXm : ∀ u, Measurable fun ω => X ω u) (hXc : ∀ ω, Continuous (X ω))
    (ℓ ε : ℝ) (A : Set Ω) (hA : ENNReal.ofReal (1 - ε) ≤ P A)
    (hAX : ∀ᵐ ω ∂P, ω ∈ A → ∀ j, Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u}) :
    ∃ E : Set Ω, (∀ ω ∈ E, ∀ j, Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u}) ∧
      P Eᶜ ≤ ENNReal.ofReal ε := by
  classical
  set M : Fin N → Set Ω := fun j =>
    Sandpile.Support.closedCrossEvent (fun u ω => X ω u) (a j) (b j) (dir j) ℓ with hMdef
  have hMm : ∀ j, MeasurableSet (M j) := fun j =>
    measurableSet_closedCrossEvent_local _ _ _ _ _ fun x _ => hXm x
  have hMae : ∀ᵐ ω ∂P, ∀ j, (ω ∈ M j ↔ Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u}) := by
    rw [ae_all_iff]
    intro j
    have h := closedCrossEvent_ae_eq P (fun u ω => X ω u) (a j) (b j) (dir j) (hab j) ℓ
      (Filter.Eventually.of_forall hXc)
    filter_upwards [h] with ω hω
    exact iff_of_eq hω
  set S : Set Ω := ⋂ j, M j with hSdef
  have hSm : MeasurableSet S := MeasurableSet.iInter hMm
  have hN : P {ω | ¬ ((∀ j, (ω ∈ M j ↔ Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u})) ∧
      (ω ∈ A → ∀ j, Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u}))} = 0 :=
    ae_iff.mp (hMae.and hAX)
  have hAS : P A ≤ P S := by
    have hsub : A ⊆ S ∪ {ω | ¬ ((∀ j, (ω ∈ M j ↔ Crosses (a j) (b j) (dir j)
        {u | ℓ ≤ X ω u})) ∧ (ω ∈ A → ∀ j, Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u}))} := by
      intro ω hω
      by_cases hg : (∀ j, (ω ∈ M j ↔ Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u})) ∧
          (ω ∈ A → ∀ j, Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u})
      · exact Or.inl (Set.mem_iInter.2 fun j => (hg.1 j).2 (hg.2 hω j))
      · exact Or.inr hg
    calc P A ≤ P (S ∪ _) := measure_mono hsub
      _ ≤ P S + P {ω | ¬ ((∀ j, (ω ∈ M j ↔ Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u})) ∧
          (ω ∈ A → ∀ j, Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u}))} := measure_union_le _ _
      _ = P S := by rw [hN, add_zero]
  have hSc : P Sᶜ ≤ ENNReal.ofReal ε := measure_compl_le_of_ofReal_le P hSm (hA.trans hAS)
  have hN2 : P {ω | ¬ ∀ j, (ω ∈ M j ↔ Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u})} = 0 :=
    ae_iff.mp hMae
  refine ⟨S ∩ {ω | ∀ j, Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u}}, fun ω hω => hω.2, ?_⟩
  have hsub : (S ∩ {ω | ∀ j, Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u}})ᶜ ⊆
      Sᶜ ∪ {ω | ¬ ∀ j, (ω ∈ M j ↔ Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u})} := by
    intro ω hω
    by_cases hS' : ω ∈ S
    · by_cases hg : ∀ j, (ω ∈ M j ↔ Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u})
      · exact absurd ⟨hS', fun j => (hg j).1 (Set.mem_iInter.1 hS' j)⟩ hω
      · exact Or.inr hg
    · exact Or.inl hS'
  calc P _ ≤ P (Sᶜ ∪ _) := measure_mono hsub
    _ ≤ P Sᶜ + P {ω | ¬ ∀ j, (ω ∈ M j ↔ Crosses (a j) (b j) (dir j) {u | ℓ ≤ X ω u})} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ε := by rw [hN2, add_zero]; exact hSc

/-- The cube payoffs of a continuous reward are bounded above: the reward is bounded on the
compact time strip over the cube. -/
theorem bddAbove_cubeStoppingPayoffs_of_continuous {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (B : ℝ≥0 → ΩB → Space d) (u : Space d)
    (hB : IsBrownian d u B PB) (h : ℝ → Space d → ℝ)
    (hh : Continuous fun q : ℝ × Space d => h q.1 q.2) (T L : ℝ) (hL : 0 ≤ L) :
    BddAbove (cubeStoppingPayoffs B PB h T L u) := by
  obtain ⟨M, hM⟩ := (isCompact_strip_cube d u T L).exists_bound_of_continuousOn hh.continuousOn
  refine bddAbove_cubeStoppingPayoffs_of_continuousOn hB h T L M hL hh.continuousOn ?_
  intro s hs y hy
  simpa using hM (s, y) ⟨hs, hy⟩

end Helpers

/-- **The sequential step.**  Exactly the hypothesis
`d23BlockCrossing_of_convergent_variance` consumes, obtained from the sealed
continuum crossing through the couplings. -/
theorem d23_sequential_of_crossing (d : ℕ) (hd : d = 2 ∨ d = 3)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hCube : Sandpile.External.CubeStoppingStability)
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
 ∀ δ : ℝ, 0 < δ → ∃ c T : ℝ, 0 < c ∧ 0 < T ∧
      ∀ (Rs : ℕ → ℕ) (laws : ℕ → Measure ℝ) (v : ℝ),
        (∀ n, n + 1 ≤ Rs n) →
        (∀ n, IsProbabilityMeasure (laws n)) →
        (∀ n, ∫ z, z ∂(laws n) = 0) →
        (∀ n, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (laws n)) →
        (∀ n, Integrable (fun z => Real.exp (θ₀ * |z|)) (laws n)) →
        (∀ n, ∫ z, Real.exp (θ₀ * |z|) ∂(laws n) ≤ K₀) →
        ν₀ ^ 2 ≤ v → 0 < v → v ≤ (4 / θ₀ ^ 2) * K₀ →
        Tendsto (fun n => variance id (laws n)) atTop (𝓝 v) →
        ¬ (∀ n, ENNReal.ofReal δ < LatticeProb.iidLaw d (laws n)
          {ζ : Site d → ℝ | ¬ BlockGood (Rs n)
            (d23Field d (Rs n) ⌊(Rs n : ℝ) ^ 2 * T⌋₊ ζ)
            (c * (Rs n : ℝ) ^ (2 - (d : ℝ) / 2)) 0}) := by
  open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings in
  classical
  intro δ hδ
  have hd1 : 1 ≤ d := by omega
  have hd3 : d ≤ 3 := by omega
  -- the four rectangles of the coupling lemma, and the continuum crossing on them
  let a : Fin 4 → Fin 2 → ℝ := fun _ => ![0, 0]
  let b : Fin 4 → Fin 2 → ℝ := ![![2, 2], ![2, 2], ![4, 2], ![2, 4]]
  let dir : Fin 4 → Fin 2 := ![0, 1, 0, 1]
  have hab : ∀ (j : Fin 4) (i : Fin 2), a j i < b j i := by
    intro j i
    fin_cases j <;> fin_cases i <;> simp [a, b]
  obtain ⟨T, H, hT, hH, hcross⟩ := Sandpile.Frozen.limiting_odometer_crossing hRSWc hPitt hOcc
    d hd 4 a b hab dir (δ / 4) (by positivity)
  refine ⟨ν₀ * H / 2, T, by positivity, hT, ?_⟩
  intro Rs laws v hRs hprob hmean hevar hexp hK hv1 hv0 hv2 hvar hbad
  haveI : ∀ n, IsProbabilityMeasure (laws n) := hprob
  have hRs' : Tendsto Rs atTop atTop :=
    tendsto_atTop_mono (fun n => (Nat.le_succ n).trans (hRs n)) tendsto_id
  have hRsR : Tendsto (fun n => (Rs n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hRs'
  -- a white noise with continuous ball fields, and a heat potential version of it
  obtain ⟨ΩW, mΩ, PW, hPW, W, hW, hWc⟩ := exists_whiteNoise_continuous_ballField d hd
  obtain ⟨Z1, hZ1mod, hZ1cont⟩ := exists_continuous_version hd1 hd3 (zero_le_one' ℝ) PW W hW
  obtain ⟨Zg, hZgm, hZgc, hZgae, hZgmod⟩ := exists_globalHeatField hd1 hd3 PW W hW Z1 hZ1mod hZ1cont
  -- one motion, shifted to every starting point
  obtain ⟨ΩB, mB, PB, hPB, B0all, hB0all, hB0cont, hB0sm⟩ := motion_exists d
  let B : Space d → ℝ≥0 → ΩB → Space d := fun y t ω => y + B0all 0 t ω
  have hB : ∀ y, IsBrownian d y (B y) PB :=
    fun y => isBrownian_add_const d PB (B0all 0) (hB0all 0) y
  have hBcont : ∀ (y : Space d) (ω : ΩB), Continuous fun t => B y t ω :=
    fun y ω => continuous_const.add (hB0cont 0 ω)
  have hBsm : ∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t) :=
    fun y t => stronglyMeasurable_const.add (hB0sm 0 t)
  have hshift : ∀ (y : Space d) (t : ℝ≥0) (ω : ΩB), B y t ω = y + B 0 t ω := by
    intro y t ω
    simp [B]
  -- `hWc` gives continuity at every positive scale; the crossing theorem asks for it
  -- only on the scales the paper defines, `0 < s ≤ 1`.
  have hcr := hcross ΩW PW W hW (fun s hs _ => hWc s hs) Z1 hZ1mod hZ1cont ΩB PB B hB hBcont hBsm
  -- the field of the coupling: the frozen field scaled by the standard deviation
  let Zv : ΩW → ℝ → Space d → ℝ := fun ω t x => Real.sqrt v * Zg ω t x
  have hZvm : ∀ t x, Measurable fun ω => Zv ω t x := fun t x => (hZgm t x).const_mul _
  have hZvc : ∀ ω, Continuous fun q : ℝ × Space d => Zv ω q.1 q.2 :=
    fun ω => continuous_const.mul (hZgc ω)
  let X : ΩW → Space 2 → ℝ := fun ω u =>
    brownianValueCube (B (planePoint u)) PB (Zv ω) T 1 (planePoint u)
  have hXm : ∀ u, Measurable fun ω => X ω u := fun u =>
    measurable_brownianValueCube_sample_of_isBrownian d PB (B (planePoint u)) Zv hZvm hZvc T 1 hT
      (planePoint u) (hB _)
  have hXc : ∀ ω, Continuous (X ω) := fun ω =>
    (continuous_brownianValueCube_family d PB B (hB 0) hshift (Zv ω) (hZvc ω) T 1 hT).comp
      (continuous_planePoint d)
  -- the crossing for the ball value transfers to the cube value of the scaled field
  have hsqrt : ν₀ ≤ Real.sqrt v := by
    have := Real.sqrt_le_sqrt hv1
    rwa [Real.sqrt_sq hν₀.le] at this
  have hsqrt0 : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hAX : ∀ᵐ ω ∂PW, ω ∈ {ω | ∀ j : Fin 4,
        Sandpile.Frozen.LimitingOdometerCrossing.Crosses (a j) (b j) (dir j)
          {u : Space 2 | H < brownianValueBall
            (B (Sandpile.Frozen.LimitingOdometerCrossing.planePoint u)) PB
            (fun t z => Z1 t z ω) T 1
            (Sandpile.Frozen.LimitingOdometerCrossing.planePoint u)}} →
      ∀ j, Crosses (a j) (b j) (dir j) {u | 2 * (ν₀ * H / 2) ≤ X ω u} := by
    filter_upwards [hZgae] with ω hω hωA j
    refine crosses_mono (fun u hu => ?_) (hωA j)
    have hu' : H < brownianValueBall (B (planePoint u)) PB (fun t z => Z1 t z ω) T 1
        (planePoint u) := hu
    rw [brownianValueBall_congr_of_nonneg (B (planePoint u)) PB _ (fun t z => Zg ω t z) T 1
      hT.le (fun t ht z => (hω t ht z).symm)] at hu'
    have hbdd := bddAbove_cubeStoppingPayoffs_of_continuous PB (B (planePoint u)) (planePoint u)
      (hB _) (Zv ω) (hZvc ω) T 1 zero_le_one
    have hcmp := mul_brownianValueBall_le_brownianValueCube (B (planePoint u)) PB
      (fun t z => Zg ω t z) (Real.sqrt v) T hsqrt0 hT.le (planePoint u) hbdd
    show 2 * (ν₀ * H / 2) ≤ brownianValueCube (B (planePoint u)) PB (Zv ω) T 1 (planePoint u)
    refine le_trans ?_ hcmp
    nlinarith
  obtain ⟨E, hE0, hEprob⟩ := exists_crossing_good_set PW a b hab dir X hXm hXc
    (2 * (ν₀ * H / 2)) (δ / 4) _ hcr hAX
  have hprobE : PW Eᶜ < ENNReal.ofReal (δ / 2) :=
    hEprob.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
  -- the finite-dimensional convergence of the scenery field to the scaled continuum field
  have hfdd : ∀ (m : ℕ) (r : Fin m → ℝ) (w : Fin m → Space d),
      (∀ i, r i ∈ Set.Icc (0 : ℝ) T) →
      TendstoInDistribution
        (fun n (σ : Site d → ℝ) (i : Fin m) =>
          Frozen.HeatPotentialInvariance.linInterp d (Rs n) (scenery d σ) (r i) (w i))
        atTop (fun ω i => Zv ω (r i) (w i))
        (fun n => centeredMassLaw d (laws n)) PW := by
    intro m r w hr
    have h := heat_potential_fd_seq hLocalCLT hd1 hd3 (continuum_double_time_limit hd1 hd3)
      θ₀ K₀ v hθ₀ hv0 laws hmean hexp hK hvar (fun n => (Rs n : ℝ)) hRsR PW W hW r
      (fun i => (hr i).1) w (∑ i, ‖w i‖)
      (fun i => Finset.single_le_sum (f := fun j => ‖w j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i))
    refine h.congr (fun n => Filter.EventuallyEq.rfl) ?_
    have hi : ∀ i, ∀ᵐ ω ∂PW, gaussianPotential d v W (r i) (w i) ω = Zv ω (r i) (w i) := by
      intro i
      filter_upwards [hZgmod (r i) (hr i).1 (w i)] with ω hω
      show _ = Real.sqrt v * Zg ω (r i) (w i)
      rw [hω]
      simp [gaussianPotential]
    filter_upwards [ae_all_iff.2 hi] with ω hω
    funext i
    exact hω i
  have hev := eventually_measure_bad_d23_block_lt_of_fdd hCube hd1 hd3 θ₀ K₀ hθ₀ laws hmean hexp
    hK Rs hRs' PW Zv (Filter.Eventually.of_forall hZvc) ΩB PB B hB T (ν₀ * H / 2) δ hT
    (by positivity) hδ hfdd X (fun _ _ => rfl) hXm E
    (fun ω hω => ⟨hXc ω, hE0 ω hω 0, hE0 ω hω 1, hE0 ω hω 2, hE0 ω hω 3⟩) hprobE
  obtain ⟨n, hn⟩ := (hev.and (Filter.Eventually.of_forall hbad)).exists
  exact absurd hn.1 (not_lt.2 hn.2.le)

end Sandpile.Support
