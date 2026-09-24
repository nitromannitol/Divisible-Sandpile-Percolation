/-
**The polynomial growth of the continuous version of the Gaussian heat
potential, proved rather than assumed.**

Until this module, `sandpile.tex:1019-1021`'s sentence "this field has a
locally continuous modification, and throughout `Z` denotes that version" was
split in two: the modification and its continuity were constructed
(`Sandpile.Support.exists_continuous_version`), and its polynomial growth on
each strip was the external input `Sandpile.External.ContinuousVersionGrowth`
(Adler and Taylor, *Random Fields and Geometry*, Theorem 2.1.1).  That growth
is now proved, so the External is discharged: its file and manifest entry are
removed, and every consumer is re-registered without the hypothesis.

`exists_ae_linear_envelope` (`GrowLatticeEnvelope.lean`) gives the growth bound
for ONE continuous version `Y`, built by
`exists_version_continuous_on_strip_meas`.  The statement below is for an
ARBITRARY field `Z` that is a modification of the potential and almost surely
continuous on the strip, exactly the form `ssec:scaling-dlt4` needs; two such
fields are indistinguishable there
(`ae_forall_eq_of_continuous_modifications`, `ExplFieldEvent.lean`), so the
bound transfers from `Y` to `Z` without assuming anything about which version
`Z` is.
-/
import Sandpile.Support.GrowLatticeEnvelope
import Sandpile.Support.GrowVersionMeasurable
import Sandpile.Support.ExplFieldEvent

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- **The polynomial growth of every almost-surely-continuous modification of
the Gaussian heat potential, on every strip.**  This is the statement of the
discharged external `Sandpile.External.ContinuousVersionGrowth`, proved rather
than assumed. -/
theorem continuousVersionGrowth :
    ∀ d : ℕ, 1 ≤ d → d ≤ 3 →
      ∀ ν2 : ℝ, 0 ≤ ν2 →
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Space d → ℝ) → ΩW → ℝ),
        IsWhiteNoise d W PW →
      ∀ Z : ℝ → Space d → ΩW → ℝ,
        (∀ (t : ℝ) (x : Space d),
          Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
            (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)))) →
        ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∃ C k : ℝ,
          ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)),
            |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k := by
  intro d hd hd3 ν2 hν2 ΩW _ PW _ W hW Z hZmod hZcont T hT
  obtain ⟨Y, hYmeas, hYmod, hYcont⟩ :=
    exists_version_continuous_on_strip_meas hd hd3 hν2 hT PW W hW
  have henv := exists_ae_linear_envelope hd hd3 hν2 hT PW W hW Y hYmeas hYmod hYcont
  set strip : Set (ℝ × Space d) :=
    Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)) with hstripdef
  haveI hne : Nonempty ↥strip := ⟨⟨(0, 0), ⟨⟨le_rfl, hT.le⟩, Set.mem_univ _⟩⟩⟩
  set F : ↥strip → ΩW → ℝ := fun e ω => Z e.1.1 e.1.2 ω with hFdef
  set G : ↥strip → ΩW → ℝ := fun e ω => Y (e.1.1, fun i => e.1.2 i) ω with hGdef
  have hF : ∀ᵐ ω ∂PW, Continuous fun e : ↥strip => F e ω := by
    filter_upwards [hZcont T hT] with ω hω
    exact hω.restrict
  have hG : ∀ᵐ ω ∂PW, Continuous fun e : ↥strip => G e ω := by
    refine Filter.Eventually.of_forall fun ω => ?_
    refine (hYcont ω).comp (continuous_subtype_val.fst.prodMk ?_)
    exact (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin d => ℝ)).continuous.comp continuous_subtype_val.snd
  have hmod : ∀ e : ↥strip, F e =ᵐ[PW] G e := by
    intro e
    have h1 := hZmod e.1.1 e.1.2
    have h2 := hYmod (e.1.1, fun i => e.1.2 i) e.2.1
    filter_upwards [h1, h2] with ω hω1 hω2
    show Z e.1.1 e.1.2 ω = Y (e.1.1, fun i => e.1.2 i) ω
    rw [hω1, hω2]
  have hall := ae_forall_eq_of_continuous_modifications PW F G hF hG hmod
  filter_upwards [hall, henv] with ω hωall hωenv
  obtain ⟨C, hC⟩ := hωenv
  refine ⟨C, 1, fun p hp => ?_⟩
  set e : ↥strip := ⟨p, hp⟩ with hedef
  have hFG : F e ω = G e ω := hωall e
  have hFp : F e ω = Z p.1 p.2 ω := rfl
  have hGp : G e ω = Y (p.1, fun i => p.2 i) ω := rfl
  have hp' : p.1 ∈ Set.Icc (0 : ℝ) T := hp.1
  have hzp : Y (p.1, fun i => p.2 i) ω = zField Y p.1 p.2 ω := rfl
  rw [← hFp, hFG, hGp, hzp]
  rw [Real.rpow_one]
  exact hC p.1 hp' p.2

end Sandpile.Support
