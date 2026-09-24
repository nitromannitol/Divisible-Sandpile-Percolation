/-
White noise is preserved by separately almost-sure changes at each index.
This does not give simultaneous equality at an uncountable set of indices.
The null-fiber construction records both the measurability and the white-noise
properties of such modifications.
-/
import Sandpile.Continuum.WhiteNoise
open MeasureTheory ProbabilityTheory Set Filter
open Sandpile.Continuum

theorem Sandpile.Support.isWhiteNoise_congr {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} {W W' : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (heq : ∀ f, W f =ᵐ[P] W' f)
    (hm : ∀ f, MemLp f 2 (volume : Measure (Space d)) → Measurable (W' f)) :
    IsWhiteNoise d W' P := by
  refine ⟨hW.gaussian.congr heq, hm, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    exact (integral_congr_ae (heq f).symm).trans (hW.mean f hf)
  · intro f g hf hg
    have hprod : (fun ω => W' f ω * W' g ω) =ᵐ[P] (fun ω => W f ω * W g ω) := by
      filter_upwards [heq f, heq g] with ω hf' hg'
      rw [hf', hg']
    exact (integral_congr_ae hprod).trans (hW.cov f g hf hg)
  · intro f g hf hg
    filter_upwards [hW.add f g hf hg, heq (f + g), heq f, heq g] with ω ha hfg hf' hg'
    change W (f + g) ω = W f ω + W g ω at ha
    rw [hfg, hf', hg'] at ha
    exact ha
  · intro a f hf
    filter_upwards [hW.smul a f hf, heq (a • f), heq f] with ω ha haf hf'
    change W (a • f) ω = a * W f ω at ha
    rw [haf, hf'] at ha
    exact ha
  · intro U mU μ hμ f hf hs
    obtain ⟨g, hg, hgeq⟩ := LatticeProb.exists_joint_version_of_covariance volume P W
      (fun q => (hW.gaussian.hasGaussianLaw_eval q).memLp_two) hW.cov f hf hs
    exact ⟨g, hg, fun u => (hgeq u).trans (heq (f u))⟩

theorem Sandpile.Support.ae_eq_null_fiber_update {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W A : I → Ω → ℝ) (V : Ω → ℝ) (c : I → ℝ)
    (hnull : ∀ i, P {ω | V ω = c i} = 0) (i : I) :
    W i =ᵐ[P] (fun ω => if V ω = c i then A i ω else W i ω) := by
  have hne : ∀ᵐ ω ∂P, ¬ V ω = c i := ae_iff.mpr (by simpa only [not_not] using hnull i)
  filter_upwards [hne] with ω hω
  simp only [if_neg hω]

theorem Sandpile.Support.measurable_null_fiber_update {Ω I : Type*} [MeasurableSpace Ω]
    (W A : I → Ω → ℝ) (V : Ω → ℝ) (c : I → ℝ)
    (hW : ∀ i, Measurable (W i)) (hA : ∀ i, Measurable (A i)) (hV : Measurable V)
    (i : I) : Measurable (fun ω => if V ω = c i then A i ω else W i ω) := by
  exact (hA i).ite (measurableSet_eq_fun hV measurable_const) (hW i)

theorem Sandpile.Support.isWhiteNoise_null_fiber_update {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (P : Measure Ω) (W A : (Space d → ℝ) → Ω → ℝ)
    (V : Ω → ℝ) (c : (Space d → ℝ) → ℝ) (hW : IsWhiteNoise d W P)
    (hA : ∀ f, Measurable (A f)) (hV : Measurable V)
    (hnull : ∀ f, P {ω | V ω = c f} = 0) :
    IsWhiteNoise d (fun f ω => if V ω = c f then A f ω else W f ω) P := by
  refine Sandpile.Support.isWhiteNoise_congr hW
    (Sandpile.Support.ae_eq_null_fiber_update P W A V c hnull) ?_
  intro f hf
  exact (hA f).ite (measurableSet_eq_fun hV measurable_const) (hW.meas f hf)

