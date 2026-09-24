/-
**The first conclusion of `lem:dgt4-linearization-from-survival`**
(`eq:dgt4-linearization-from-paths`, `sandpile.tex:5651-5657`) for an arbitrary
test function.

`Support/LinJacobianTestedL2.lean` proves it for a NONNEGATIVE test function,
which is what makes the tested field convex in each coordinate of the scenery.
The pairing is linear in the test function, so a signed one enters as the
difference of its positive and negative parts, and the mean square of a
difference is at most twice the sum of the two mean squares.  Neither part is
smooth, which is why the cell estimate was restated in
`Support/LinJacobianCellGeneral.lean` for a bounded, integrable and square
integrable test function.
The limits may be taken along any real-scale filter below `atTop`;
the default scale-filter bound retains the unrestricted real-scale form.
-/
import Sandpile.Support.LinJacobianTestedL2
import Sandpile.Support.LinL2Two
import Sandpile.Support.ContDGT4Membrane
import Sandpile.Support.ContDominated

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- The lattice pairing is additive in the test function. -/
theorem latticePairing_sub_testFn (R : ℝ) (f : Site d → ℝ) (φ ψ : Space d → ℝ)
    (hφ : Integrable φ) (hψ : Integrable ψ) {L : ℝ}
    (hsφ : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L)
    (hsψ : ∀ z : Space d, ψ z ≠ 0 → ‖z‖ ≤ L) :
    Sandpile.Continuum.latticePairing R f (fun z => φ z - ψ z)
      = Sandpile.Continuum.latticePairing R f φ
        - Sandpile.Continuum.latticePairing R f ψ := by
  have hsφ' : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ Sandpile.Support.supportBox d R L :=
    fun z hz => Sandpile.Support.floor_mem_boxFinset R z (hsφ z hz)
  have hsψ' : ∀ z : Space d, ψ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ Sandpile.Support.supportBox d R L :=
    fun z hz => Sandpile.Support.floor_mem_boxFinset R z (hsψ z hz)
  have hf : Integrable (fun z : Space d => Sandpile.Continuum.embed R f z * φ z) :=
    Sandpile.Support.integrable_embed_mul R f φ hφ (Sandpile.Support.supportBox d R L) hsφ'
  have hg : Integrable (fun z : Space d => Sandpile.Continuum.embed R f z * ψ z) :=
    Sandpile.Support.integrable_embed_mul R f ψ hψ (Sandpile.Support.supportBox d R L) hsψ'
  show ∫ z : Space d, Sandpile.Continuum.embed R f z * (φ z - ψ z)
    = (∫ z : Space d, Sandpile.Continuum.embed R f z * φ z)
      - ∫ z : Space d, Sandpile.Continuum.embed R f z * ψ z
  rw [← MeasureTheory.integral_sub hf hg]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)

/-- A functional of the scenery is integrable under the law of the mass
configuration exactly when it is under the i.i.d. law of the field. -/
theorem integrable_comp_scenery (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (G : (Site d → ℝ) → ℝ) (hG : AEStronglyMeasurable G (LatticeProb.iidLaw d ν))
    (hGint : Integrable G (LatticeProb.iidLaw d ν)) :
    Integrable (fun σ => G (Sandpile.scenery d σ)) (Sandpile.centeredMassLaw d ν) := by
  have hmap := map_scenery_centeredMassLaw d ν hd
  have hG' : AEStronglyMeasurable G ((Sandpile.centeredMassLaw d ν).map (Sandpile.scenery d)) := by
    rw [hmap]; exact hG
  have h : Integrable G ((Sandpile.centeredMassLaw d ν).map (Sandpile.scenery d)) := by
    rw [hmap]; exact hGint
  exact (integrable_map_measure hG' (measurable_scenery d).aemeasurable).mp h

/-- The frozen integrand of `eq:dgt4-linearization-from-paths` is square
integrable. -/
theorem integrable_sq_frozen_pairing (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (hsqν : Integrable (fun z => z ^ 2) ν) (hpos : Integrable (fun z => max z 0) ν)
    (R : ℝ) (N : ℕ) (q : ℕ → ℝ) (φ : Space d → ℝ) (hφ : Integrable φ) {Lb : ℝ}
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ Lb)
    (s : Finset (Site d)) (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    Integrable (fun σ => (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ N x -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) N -
          ∑ j ∈ Finset.range N, q j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2)
      (Sandpile.centeredMassLaw d ν) := by
  classical
  set a : Site d → ℝ :=
    fun x => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x with ha
  set c : Site d → ℝ := fun z => ∑ x ∈ s, a x *
    ∑ j ∈ Finset.range N, q j * heatKernel d j x z with hc
  set G : (Site d → ℝ) → ℝ := fun ζ =>
    (testedField s a N ζ - (∫ η, testedField s a N η ∂(LatticeProb.iidLaw d ν))
      - ∑ z ∈ testedSites s N, c z * ζ z) ^ 2 with hG
  have hGm : Measurable G := by
    refine (((measurable_testedField s a N).sub measurable_const).sub ?_).pow_const 2
    exact Finset.measurable_sum _ fun z _ => measurable_const.mul (measurable_pi_apply z)
  have hGint : Integrable G (LatticeProb.iidLaw d ν) :=
    integrable_sq_testedField_sub_linear ν hsqν s a N (testedSites s N) c
      (∫ η, testedField s a N η ∂(LatticeProb.iidLaw d ν))
  have hpt : ∀ σ : Site d → ℝ,
      (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ N x -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) N -
          ∑ j ∈ Finset.range N, q j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
        = G (Sandpile.scenery d σ) := by
    intro σ
    rw [hG]
    exact congrArg (fun t => t ^ 2)
      (frozen_integrand_eq_testedField ν hd hpos R N q σ φ hφ hsupp s hs)
  refine Integrable.congr
    (integrable_comp_scenery ν hd G hGm.aestronglyMeasurable hGint) ?_
  exact Filter.Eventually.of_forall fun σ => (hpt σ).symm

/-- The properties the positive part of a test function inherits. -/
theorem posPart_facts (φ : Space d → ℝ) (Cφ L : ℝ) (hb : ∀ z, |φ z| ≤ Cφ)
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L) (hint : Integrable φ)
    (hsq : Integrable (fun z => φ z ^ 2)) :
    (∀ z, 0 ≤ max (φ z) 0) ∧ (∀ z, |max (φ z) 0| ≤ Cφ) ∧
      (∀ z : Space d, max (φ z) 0 ≠ 0 → ‖z‖ ≤ L) ∧
      Integrable (fun z => max (φ z) 0) ∧
      Integrable (fun z => (max (φ z) 0) ^ 2) := by
  have hle : ∀ z : Space d, |max (φ z) 0| ≤ |φ z| := by
    intro z
    rcases le_total 0 (φ z) with hz | hz
    · rw [max_eq_left hz]
    · rw [max_eq_right hz, abs_zero]
      exact abs_nonneg _
  refine ⟨fun z => le_max_right _ _, fun z => (hle z).trans (hb z), ?_, ?_, ?_⟩
  · intro z hz
    refine hsupp z fun h0 => hz ?_
    rw [h0, max_self]
  · have hm : AEStronglyMeasurable (fun z : Space d => max (φ z) 0) volume :=
      (hint.aemeasurable.max aemeasurable_const).aestronglyMeasurable
    refine Integrable.mono' hint.abs hm ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hle z
  · have hm : AEStronglyMeasurable (fun z : Space d => max (φ z) 0 ^ 2) volume :=
      ((hint.aemeasurable.max aemeasurable_const).pow_const 2).aestronglyMeasurable
    refine Integrable.mono' hsq hm ?_
    refine Filter.Eventually.of_forall fun z => ?_
    have hsqle : |max (φ z) 0| ^ 2 ≤ |φ z| ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hle z) 2
    rw [sq_abs, sq_abs] at hsqle
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    exact hsqle

/-- **`eq:dgt4-linearization-from-paths`, the first conclusion of
`lem:dgt4-linearization-from-survival`**, for an arbitrary test function. -/
theorem tendsto_l2_frozen_pairing {l : Filter ℝ} [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmean : ∫ z, z ∂ν = 0) (hsqν : Integrable (fun z => z ^ 2) ν)
    (φ : Space d → ℝ) (hφtest : Sandpile.Continuum.IsTestFn Set.univ φ)
    (T : ℝ) (hT : 0 < T) (q : ℝ → ℕ → ℝ) (C : ℝ)
    (hsurv : Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, survivalInd σ ⌊R ^ 2 * T⌋₊ j X ∂(Sandpile.centeredMassLaw d ν)) - q R j|
            ∂(walkLaw d 0)) l (𝓝 0))
    (hcov : ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun l (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
          (j : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Site d,
            Frozen.DGT4PathSurvival.IsNNPath i X →
            Frozen.DGT4PathSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ i X *
                  Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ i X
                  ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν))| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R)
    (hl : l ≤ atTop := by exact le_rfl) :
    Tendsto (fun R : ℝ =>
        ∫ σ, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
          (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
            Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
            ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
          ∂(Sandpile.centeredMassLaw d ν)) l (𝓝 0) := by
  classical
  obtain ⟨Cφ, L, hCφ, hL, hb, hsupp, hint⟩ := Sandpile.Support.exists_bound_of_isTestFn hφtest
  have hsq2 : Integrable (fun z => φ z ^ 2) := integrable_sq_of_isTestFn hφtest
  have hpos : Integrable (fun z => max z 0) ν := integrable_posPart_of_sq ν hsqν
  obtain ⟨hp0, hpb, hps, hpint, hpsq⟩ := posPart_facts φ Cφ L hb hsupp hint hsq2
  have hbn : ∀ z : Space d, |(-φ) z| ≤ Cφ := fun z => by
    show |(-(φ z))| ≤ Cφ
    rw [abs_neg]; exact hb z
  have hsn : ∀ z : Space d, (-φ) z ≠ 0 → ‖z‖ ≤ L := fun z hz =>
    hsupp z fun h0 => hz (by show -(φ z) = 0; rw [h0, neg_zero])
  have hsqn : Integrable (fun z => (-φ) z ^ 2) :=
    hsq2.congr (Filter.Eventually.of_forall fun z => by show φ z ^ 2 = (-(φ z)) ^ 2; ring)
  obtain ⟨hm0, hmb, hms, hmint, hmsq⟩ := posPart_facts (-φ) Cφ L hbn hsn hint.neg hsqn
  set pf : Space d → ℝ := fun z => max (φ z) 0 with hpf
  set mf : Space d → ℝ := fun z => max (-(φ z)) 0 with hmf
  have hsplit : φ = fun z => pf z - mf z := by
    funext z
    simp only [hpf, hmf]
    rcases le_total 0 (φ z) with hz | hz
    · rw [max_eq_left hz, max_eq_right (by linarith : -(φ z) ≤ 0), sub_zero]
    · rw [max_eq_right hz, max_eq_left (by linarith : (0 : ℝ) ≤ -(φ z)), zero_sub, neg_neg]
  set A : ℝ → (Site d → ℝ) → ℝ := fun R σ =>
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
      (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) pf with hA
  set Bf : ℝ → (Site d → ℝ) → ℝ := fun R σ =>
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
      (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) mf with hBf
  have hlin : ∀ (R : ℝ) (σ : Site d → ℝ),
      R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
          ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ
        = A R σ - Bf R σ := by
    intro R σ
    simp only [hA, hBf]
    rw [hsplit, latticePairing_sub_testFn R _ pf mf hpint hmint hps hms]
    ring
  have hint1 : ∀ R : ℝ, Integrable (fun σ => (A R σ) ^ 2) (Sandpile.centeredMassLaw d ν) :=
    fun R => integrable_sq_frozen_pairing ν (by omega) hsqν hpos R ⌊R ^ 2 * T⌋₊ (q R) pf
      hpint hps (Sandpile.Support.supportBox d R L)
      (fun z hz => Sandpile.Support.floor_mem_boxFinset R z (hps z hz))
  have hint2 : ∀ R : ℝ, Integrable (fun σ => (Bf R σ) ^ 2) (Sandpile.centeredMassLaw d ν) :=
    fun R => integrable_sq_frozen_pairing ν (by omega) hsqν hpos R ⌊R ^ 2 * T⌋₊ (q R) mf
      hmint hms (Sandpile.Support.supportBox d R L)
      (fun z hz => Sandpile.Support.floor_mem_boxFinset R z (hms z hz))
  have hint3 : ∀ R : ℝ, Integrable (fun σ => (A R σ - Bf R σ) ^ 2) (Sandpile.centeredMassLaw d ν) := by
    intro R
    refine Integrable.congr (integrable_sq_frozen_pairing ν (by omega) hsqν hpos R
      ⌊R ^ 2 * T⌋₊ (q R) φ hint hsupp (Sandpile.Support.supportBox d R L)
      (fun z hz => Sandpile.Support.floor_mem_boxFinset R z (hsupp z hz))) ?_
    exact Filter.Eventually.of_forall fun σ => by simp only [hlin R σ]
  have hup := tendsto_l2_frozen_of_nonneg (hl := hl) hd hGreen hInter ν hmean hsqν pf hpsq hp0
    Cφ L hCφ hL hpb hpint hps T hT q C hsurv hcov
  have hvm := tendsto_l2_frozen_of_nonneg (hl := hl) hd hGreen hInter ν hmean hsqν mf hmsq hm0
    Cφ L hCφ hL hmb hmint hms T hT q C hsurv hcov
  have hmain := tendsto_l2_of_two_remainders (Sandpile.centeredMassLaw d ν) A (fun _ _ => (0 : ℝ)) Bf (fun _ _ => (0 : ℝ))
    (fun R => by simpa using hint1 R) (fun R => by simpa using hint2 R)
    (fun R => by simpa using hint3 R)
    (by simpa using hup) (by simpa using hvm)
  refine hmain.congr fun R => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  simp only [hlin R σ, sub_zero]

end Sandpile
