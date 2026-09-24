/-
The Step-3 subsequential convergence of `thm:dgt4-many-limits`
(`sandpile.tex:5900-5928`, proof at `sandpile.tex:6275-6305`).

`dgt4_subseq_pairing` is the per-test-function step: the linearization
(`prop:dgt4-linearization` read along the subsequence) and the weighted
membrane limit (`prop:weighted-membrane-limit` at `q(r) = (1-r/T)^κ`) give the
same limit in distribution, because the two differ by a term of vanishing
second moment.  `dgt4_odometer_tight_subseq` reindexes the odometer's own
`H^{-s}_loc` tightness along the subsequence.
-/
import Sandpile.Support.ManyLReindex
import Sandpile.Support.ManyLMeasureBridge
import Sandpile.Support.ContDGT4Membrane
import Sandpile.Support.TightWeightedMembrane
import Sandpile.Frozen.WeightedMembraneLimit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum


open Sandpile Sandpile.Continuum

/-- **The per-test-function convergence of the Step-3 subsequential limit.**  The
linearization `hlin` says the rescaled centred odometer and the time-weighted
field differ by a term whose second moment tends to zero; `hW` identifies the
limit of the second; convergence in `L²` is convergence in measure, so the two
have the same limit in distribution. -/
theorem dgt4_subseq_pairing
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν)
    (κ : ℝ) (T : ℝ)
    (g : ℝ → ℝ) (q : ℝ → ℝ)
    (hlin : ∀ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
      Tendsto (fun L : ℝ =>
        ∫ σ, (g L ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing (g L)
            (fun x => Sandpile.odometer σ ⌊g L ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊g L ^ 2 * T⌋₊ -
              ∑ j ∈ Finset.range ⌊g L ^ 2 * T⌋₊,
                q ((j : ℝ) / g L ^ 2) *
                  (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
          ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0))
    (hW : ∀ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
      TendstoInDistribution
        (fun L : ℝ => fun σ : Sandpile.Site d → ℝ =>
          g L ^ (((d : ℝ) - 4) / 2) *
            Sandpile.Continuum.latticePairing (g L)
              (fun x => ∑ j ∈ Finset.range ⌊g L ^ 2 * T⌋₊,
                q ((j : ℝ) / g L ^ 2) *
                  (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
        atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
        (gaussianReal 0 (Real.toNNReal
          (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ))))
    (φ : Space d → ℝ) (hφtest : Sandpile.Continuum.IsTestFn Set.univ φ) :
    TendstoInDistribution
      (fun L : ℝ => fun σ : Sandpile.Site d → ℝ =>
        g L ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing (g L)
            (fun x => Sandpile.odometer σ ⌊g L ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊g L ^ 2 * T⌋₊) φ)
      atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
      (gaussianReal 0 (Real.toNNReal
        (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ))) := by
  classical
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hsq' : MemLp (id : ℝ → ℝ) 2 ν :=
    (MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq
  set P : Measure (Sandpile.Site d → ℝ) := Sandpile.centeredMassLaw d ν with hP
  set O : ℝ → (Sandpile.Site d → ℝ) → ℝ := fun R σ =>
    R ^ (((d : ℝ) - 4) / 2) *
      Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
          Sandpile.meanOdometer P ⌊R ^ 2 * T⌋₊) φ with hO
  set W : ℝ → (Sandpile.Site d → ℝ) → ℝ := fun R σ =>
    R ^ (((d : ℝ) - 4) / 2) *
      Sandpile.Continuum.latticePairing R
        (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ with hWdef
  obtain ⟨C, Lb, hC0, hL0, hC, hsupp, hint⟩ := exists_bound_of_isTestFn hφtest
  have hOmem : ∀ R : ℝ, MemLp (O R) 2 P := by
    intro R
    refine (memLp_two_latticePairing P R
      (fun σ x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x - Sandpile.meanOdometer P ⌊R ^ 2 * T⌋₊)
      (fun x => (memLp_two_odometer ν hsq hd1 _ x).sub (memLp_const _)) φ hint hsupp).const_mul _
  have hWmem : ∀ R : ℝ, MemLp (W R) 2 P := by
    intro R
    refine (memLp_two_latticePairing P R
      (fun σ x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
        q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x)
      (fun x => memLp_two_weightedField_mass ν hsq' hd1 _ _ x) φ hint hsupp).const_mul _
  have hdiff : ∀ (R : ℝ) (σ : Sandpile.Site d → ℝ),
      O R σ - W R σ = R ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing R
          (fun x => (Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
            Sandpile.meanOdometer P ⌊R ^ 2 * T⌋₊) -
            ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ := by
    intro R σ
    rw [latticePairing_sub R _ _ φ hint hsupp, hO, hWdef]
    ring
  have hZlim : Tendsto (fun L : ℝ => ∫ σ, (O (g L) σ - W (g L) σ) ^ 2 ∂P) atTop (𝓝 0) := by
    refine (hlin φ hφtest).congr fun L => ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    show (g L ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing (g L)
          (fun x => Sandpile.odometer σ ⌊g L ^ 2 * T⌋₊ x -
            Sandpile.meanOdometer P ⌊g L ^ 2 * T⌋₊ -
            ∑ j ∈ Finset.range ⌊g L ^ 2 * T⌋₊,
              q ((j : ℝ) / g L ^ 2) *
                (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
      = (O (g L) σ - W (g L) σ) ^ 2
    rw [hdiff (g L) σ]
  have hOW : ∀ L : ℝ, MemLp (fun σ => O (g L) σ - W (g L) σ) 2 P :=
    fun L => (hOmem (g L)).sub (hWmem (g L))
  have hZint : ∀ L : ℝ, Integrable (fun σ => (O (g L) σ - W (g L) σ) ^ 2) P := fun L =>
    (MeasureTheory.memLp_two_iff_integrable_sq (hOW L).aestronglyMeasurable).mp (hOW L)
  have hmeasure : TendstoInMeasure P (fun L : ℝ => O (g L) - W (g L)) atTop 0 :=
    tendstoInMeasure_sub_of_integral_sq P (fun L => O (g L)) (fun L => W (g L)) hOW hZint hZlim
  have hWlim : TendstoInDistribution (fun L : ℝ => W (g L)) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 (Real.toNNReal
        (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ))) := by
    simpa only [hP, hWdef] using hW φ hφtest
  exact tendstoInDistribution_of_sub_tendstoInMeasure P (fun L => O (g L)) (fun L => W (g L)) _
    hWlim hmeasure (fun L => (hOmem (g L)).aestronglyMeasurable.aemeasurable)




open Sandpile Sandpile.Continuum

/-- **Tightness of the rescaled centred odometer along a subsequence.**  The
odometer's own tightness (`dgt4_odometer_tight`) reindexed along a map tending
to infinity and staying at least one. -/
theorem dgt4_odometer_tight_subseq
    (d : ℕ) (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (hpos : Integrable (fun z => max z 0) ν)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : ((d : ℝ) - 4) / 2 < s)
    (g : ℝ → ℝ) (hg1 : ∀ L : ℝ, 1 ≤ L → 1 ≤ g L) :
    Sandpile.Continuum.TightInNegSobolev d s (Sandpile.centeredMassLaw d ν)
      (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Space d → ℝ) =>
        g L ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing (g L)
            (fun x => Sandpile.odometer σ ⌊g L ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊g L ^ 2 * T⌋₊) φ) := by
  have h := dgt4_odometer_tight hGreenHigh hBesov hd ν hsq hpos T hT s hs
  exact Sandpile.Support.TightInNegSobolev.comp_atTop h hg1


/-- **The Step-3 subsequential convergence of `thm:dgt4-many-limits`.**  Along a
subsequence `g = Rseq ∘ kl` tending to infinity, the linearization of the
rescaled centred odometer (the hypothesis `hlin`, `prop:dgt4-linearization` read
along the subsequence) and the weighted membrane limit at `q(r) = (1-r/T)^κ`
(the hypothesis `hW`, `prop:weighted-membrane-limit` read along the subsequence)
give the convergence in `H^{-s}_loc(ℝ^d)` to `ℋ_{κ,T}`.  Tightness is the
odometer's own, reindexed. -/
theorem dgt4_subsequential_convergence
    (d : ℕ) (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (hpos : Integrable (fun z => max z 0) ν)
    (κ : ℝ) (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : ((d : ℝ) - 4) / 2 < s)
    (g : ℝ → ℝ) (q : ℝ → ℝ) (hg1 : ∀ L : ℝ, 1 ≤ L → 1 ≤ g L)
    (hlin : ∀ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
      Tendsto (fun L : ℝ =>
        ∫ σ, (g L ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing (g L)
            (fun x => Sandpile.odometer σ ⌊g L ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊g L ^ 2 * T⌋₊ -
              ∑ j ∈ Finset.range ⌊g L ^ 2 * T⌋₊,
                q ((j : ℝ) / g L ^ 2) *
                  (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
          ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0))
    (hW : ∀ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
      TendstoInDistribution
        (fun L : ℝ => fun σ : Sandpile.Site d → ℝ =>
          g L ^ (((d : ℝ) - 4) / 2) *
            Sandpile.Continuum.latticePairing (g L)
              (fun x => ∑ j ∈ Finset.range ⌊g L ^ 2 * T⌋₊,
                q ((j : ℝ) / g L ^ 2) *
                  (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
        atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
        (gaussianReal 0 (Real.toNNReal
          (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ)))) :
    Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
      (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Space d → ℝ) =>
        g L ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing (g L)
            (fun x => Sandpile.odometer σ ⌊g L ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊g L ^ 2 * T⌋₊) φ)
      (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T) := by
  refine ⟨fun φ hφ => dgt4_subseq_pairing d hd ν hsq κ T g q hlin hW φ hφ, ?_⟩
  exact dgt4_odometer_tight_subseq d hGreenHigh hBesov hd ν hsq hpos T hT s hs g hg1


end Sandpile.Support
