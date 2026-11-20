import Sandpile.External.Stopping.CenteredWalkLaw
import LatticeProb.Topology.PolishContinuousMap
import LatticeProb.Prob.SkorokhodRepresentation

/-!
# Coupling centered lattice walks with Brownian motion

Weak convergence of centered interpolated walks admits an almost surely
convergent coupling. Measurable decoding lifts the coupled paths back to
lattice walks with their original laws.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Decoding the centered path law recovers the law of the lattice walk. -/
theorem map_decode_centeredWalkPath {d : ℕ} {R : ℝ} (hR : 0 < R) (q : Site d)
    (μ : Measure (ℕ → Site d)) :
    (μ.map (centeredWalkPath R q)).map (decodeCenteredWalk R q) = μ := by
  rw [Measure.map_map (measurable_decodeCenteredWalk R q) (measurable_centeredWalkPath R q)]
  have heq : decodeCenteredWalk R q ∘ centeredWalkPath R q = id := by
    funext X
    exact decodeCenteredWalk_centeredWalkPath hR q X
  rw [heq, Measure.map_id]

/-- A path with the centered walk law is almost surely recovered by decoding
and reinterpolating it. -/
theorem ae_centeredWalkPath_decode {d : ℕ} {R : ℝ} (hR : 0 < R) (q : Site d)
    (μ : Measure (ℕ → Site d)) :
    ∀ᵐ f ∂μ.map (centeredWalkPath R q),
      centeredWalkPath R q (decodeCenteredWalk R q f) = f := by
  have hm : MeasurableSet {f : C(ℝ≥0, Continuum.Space d) |
      centeredWalkPath R q (decodeCenteredWalk R q f) = f} :=
    measurableSet_eq_fun ((measurable_centeredWalkPath R q).comp (measurable_decodeCenteredWalk R q)) measurable_id
  rw [ae_map_iff (measurable_centeredWalkPath R q).aemeasurable hm]
  filter_upwards with X
  rw [decodeCenteredWalk_centeredWalkPath hR q X]

/-- Centered lattice walks with any starting points and diverging positive
scales can be coupled so that their paths converge almost surely to a
continuous version of Brownian motion started at the origin. -/
theorem exists_centered_walk_brownian_coupling
    (d : ℕ) [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    {ΩB : Type*} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Continuum.Space d) (hB : LatticeProb.IsBrownianSpace d 0 B PB) :
    ∃ (F : ΩB → C(ℝ≥0, Continuum.Space d)) (_hFm : Measurable F),
      (∀ᵐ ω ∂PB, ∀ t, F ω t = B t ω) ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X : ℕ → Ω → (ℕ → Site d)) (Y : Ω → C(ℝ≥0, Continuum.Space d)),
        (∀ n, Measurable (X n)) ∧ Measurable Y ∧
        (∀ n, P.map (X n) = walkLaw d (q n)) ∧ P.map Y = PB.map F ∧
        ∀ᵐ ω ∂P, Tendsto (fun n => centeredWalkPath (R n) (q n) (X n ω)) atTop (𝓝 (Y ω)) := by
  obtain ⟨F, hFm, hF, hweak⟩ := exists_centered_brownian_path_limit d R q hR PB B hB
  let : PolishSpace C(ℝ≥0, Continuum.Space d) := LatticeProb.polishSpace_continuousMap _ _
  let := TopologicalSpace.upgradeIsCompletelyMetrizable C(ℝ≥0, Continuum.Space d)
  obtain ⟨Ω, mΩ, P, hP, Z, Y, hZm, hYm, hZmap, hYmap, hconv⟩ :=
    LatticeProb.Skorokhod.exists_skorokhod_representation hweak
  let X : ℕ → Ω → (ℕ → Site d) := fun n => decodeCenteredWalk (R n) (q n) ∘ Z n
  have hXm (n : ℕ) : Measurable (X n) :=
    (measurable_decodeCenteredWalk (R n) (q n)).comp (hZm n)
  have hXmap (n : ℕ) : P.map (X n) = walkLaw d (q n) := by
    rw [show X n = decodeCenteredWalk (R n) (q n) ∘ Z n from rfl,
      ← Measure.map_map (measurable_decodeCenteredWalk (R n) (q n)) (hZm n), hZmap n]
    exact map_decode_centeredWalkPath (hRpos n) (q n) (walkLaw d (q n))
  have hrecon : ∀ᵐ ω ∂P, ∀ n, centeredWalkPath (R n) (q n) (X n ω) = Z n ω := by
    apply ae_all_iff.2
    intro n
    have hh : ∀ᵐ f ∂P.map (Z n), centeredWalkPath (R n) (q n)
        (decodeCenteredWalk (R n) (q n) f) = f := by
      rw [hZmap n]
      exact ae_centeredWalkPath_decode (hRpos n) (q n) (walkLaw d (q n))
    exact ae_of_ae_map (hZm n).aemeasurable hh
  refine ⟨F, hFm, hF, Ω, mΩ, P, hP, X, Y, hXm, hYm, hXmap, hYmap, ?_⟩
  filter_upwards [hconv, hrecon] with ω hconvω hreconω
  simpa only [hreconω] using hconvω

end Sandpile.External.Stopping
