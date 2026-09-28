import Sandpile.Support.Dgt4CaseBProb
import Sandpile.Support.Localization
import LatticeProb.Prob.IidSplit

/-!
# Fubini for the i.i.d. field split at one site

"Since $Pw_n(0)$ is independent of the atomless $\zeta(0)$" (`sandpile.tex:5405`), the
sentence with which Step 2 of case (b) of `prop:dgt4-contact-asymptotics` turns the two
identities of `lem:dgt4-origin-frozen` into the two displayed estimates.

`Pw_n(0)` is the average over the neighbours of the origin of the odometer with the walk
KILLED at the origin, so it is a function of the scenery that never reads the coordinate at
the origin. The step is therefore Fubini for the i.i.d. field split at one site, and the
form proved here is the one the two call sites use: resampling a single coordinate of the
i.i.d. field with an independent draw leaves its law unchanged, so an integral of
`f(\zeta(i), W(\zeta))` with `W` blind to the coordinate `i` integrates `f` in its first
argument against `\nu` alone.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- An integral against the i.i.d. field is unchanged by resampling the coordinate `i`. -/
theorem integral_iidLaw_update (ν : Measure ℝ) [IsProbabilityMeasure ν] (i : Sandpile.Site d)
    {g : (Sandpile.Site d → ℝ) → ℝ} (hg : AEStronglyMeasurable g (LatticeProb.iidLaw d ν)) :
    ∫ ζ, g ζ ∂(LatticeProb.iidLaw d ν)
      = ∫ q : ℝ × (Sandpile.Site d → ℝ), g (Function.update q.2 i q.1)
          ∂(ν.prod (LatticeProb.iidLaw d ν)) := by
  have hmp := measurePreserving_updateSite (d := d) ν i
  have h := integral_map (μ := ν.prod (LatticeProb.iidLaw d ν))
    (φ := fun q : ℝ × (Sandpile.Site d → ℝ) => Function.update q.2 i q.1) (f := g)
    hmp.measurable.aemeasurable (by rwa [hmp.map_eq])
  rw [hmp.map_eq] at h
  exact h

/-- Fubini for the i.i.d. field split at one site: if `W` never reads the coordinate `i`,
the integral of `f(ζ(i), W(ζ))` integrates `f` in its first argument against `ν` alone.
This is `sandpile.tex:5400`, "Since $Pw_n(0)$ is independent of the atomless $\zeta(0)$". -/
theorem integral_iidLaw_split (ν : Measure ℝ) [IsProbabilityMeasure ν] (i : Sandpile.Site d)
    {f : ℝ → ℝ → ℝ} (hf : Measurable fun q : ℝ × ℝ => f q.1 q.2)
    {W : (Sandpile.Site d → ℝ) → ℝ} (hW : Measurable W)
    (hWloc : ∀ (ζ : Sandpile.Site d → ℝ) (z : ℝ), W (Function.update ζ i z) = W ζ)
    (hint : Integrable (fun q : ℝ × (Sandpile.Site d → ℝ) => f q.1 (W q.2))
      (ν.prod (LatticeProb.iidLaw d ν))) :
    ∫ ζ, f (ζ i) (W ζ) ∂(LatticeProb.iidLaw d ν)
      = ∫ ζ, (∫ z, f z (W ζ) ∂ν) ∂(LatticeProb.iidLaw d ν) := by
  have hgm : AEStronglyMeasurable (fun ζ : Sandpile.Site d → ℝ => f (ζ i) (W ζ))
      (LatticeProb.iidLaw d ν) :=
    (hf.comp ((measurable_pi_apply i).prodMk hW)).aestronglyMeasurable
  rw [integral_iidLaw_update ν i hgm]
  have hcongr : ∀ q : ℝ × (Sandpile.Site d → ℝ),
      f ((Function.update q.2 i q.1) i) (W (Function.update q.2 i q.1)) = f q.1 (W q.2) := by
    intro q
    rw [Function.update_self, hWloc]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)]
  exact integral_prod_symm _ hint

/-- `Pw_n(0)`, the average over the neighbours of the origin of the odometer killed there,
does not read the scenery at the origin.  This is the locality that makes the sentence
"Since $Pw_n(0)$ is independent of the atomless $\zeta(0)$" (`sandpile.tex:5400`) true. -/
theorem avg_originOdometer_update (hd : 1 ≤ d) (ζ : Sandpile.Site d → ℝ) (z : ℝ) (n : ℕ) :
    Sandpile.avg (Sandpile.originOdometer (Function.update ζ 0 z) n) 0
      = Sandpile.avg (Sandpile.originOdometer ζ n) 0 := by
  rw [Sandpile.originOdometer_update hd ζ z n]

/-- The split of `sandpile.tex:5400` at the origin, with `W = Pw_n(0)`: the scenery at the
origin integrates out against `ν` alone. -/
theorem integral_iidLaw_split_origin (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : Measurable fun q : ℝ × ℝ => f q.1 q.2)
    (hint : Integrable (fun q : ℝ × (Sandpile.Site d → ℝ) =>
        f q.1 (Sandpile.avg (Sandpile.originOdometer q.2 n) 0))
      (ν.prod (LatticeProb.iidLaw d ν))) :
    ∫ ζ, f (ζ 0) (Sandpile.avg (Sandpile.originOdometer ζ n) 0) ∂(LatticeProb.iidLaw d ν)
      = ∫ ζ, (∫ z, f z (Sandpile.avg (Sandpile.originOdometer ζ n) 0) ∂ν)
          ∂(LatticeProb.iidLaw d ν) :=
  integral_iidLaw_split ν 0 hf (Sandpile.measurable_avg_originOdometer hd n)
    (fun ζ z => avg_originOdometer_update hd ζ z n) hint

end Sandpile
