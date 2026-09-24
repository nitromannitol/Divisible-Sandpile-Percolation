/-
The dependence range of the unit-scale field (`sandpile.tex:2110`), and the
independence it gives across separated regions of the plane.

  "The unit-scale field `𝒳_1` is stationary, sign-symmetric, invariant under
   rotations by `π/2` and coordinate reflections, and has dependence range 2."

Step 1 of `prop:fixed-scale-crossings` uses this: "choosing a logarithmic number
of such annuli separated by distance greater than the dependence range of `𝒳_1`
makes these circuit events independent" (`sandpile.tex:2229-2231`).

The dependence range is the diameter of the support of the kernel: `𝒳_s(u)` is
the white noise tested against `ballKernel d s u`, which vanishes outside the
ball of radius `s` about the lift of `u`, so two field values at plane points at
distance at least `2s` are tested against functions with disjoint supports.  For
a white noise those two variables are jointly Gaussian with covariance the `L²`
inner product of the kernels, which is then zero, and uncorrelated jointly
Gaussian families are independent.  That last step is Mathlib's
`ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_eq_zero`; nothing is
assumed here beyond `Sandpile.Continuum.IsWhiteNoise`.

The conclusion is stated twice: as the independence of the families of field
values over the regions, and as the independence of events each of which is
measurable with respect to one such family, which is the form the circuit events
of separated annuli are used in.
-/
import Sandpile.Support.CrossBallMemLp

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- The lift of the plane into `ℝ^d` is additive on differences. -/
theorem planePoint_sub {d : ℕ} (u v : Sandpile.Continuum.Space 2) :
    (planePoint (d := d) (u - v)) = planePoint (d := d) u - planePoint (d := d) v := by
  ext i
  simp only [planePoint, PiLp.sub_apply]
  by_cases h : (i : ℕ) < 2
  · simp [h]
  · simp [h]

/-- The lift of the plane into `ℝ^d` is an isometry: it pads with zeros, and the
Euclidean norm does not see the padded coordinates. -/
theorem norm_planePoint {d : ℕ} (hd : 2 ≤ d) (w : Sandpile.Continuum.Space 2) :
    ‖(planePoint (d := d) w)‖ = ‖w‖ := by
  classical
  set F : ℕ → ℝ := fun k => if h : k < 2 then ‖w ⟨k, h⟩‖ ^ 2 else 0 with hF
  have h1 : ∀ i : Fin d, ‖(planePoint (d := d) w) i‖ ^ 2 = F (i : ℕ) := by
    intro i
    simp [planePoint, hF]
  have h2 : ∀ i : Fin 2, ‖w i‖ ^ 2 = F (i : ℕ) := by
    intro i
    simp only [hF]
    rw [dif_pos i.isLt]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  calc ∑ i : Fin d, ‖(planePoint (d := d) w) i‖ ^ 2
      = ∑ i : Fin d, F (i : ℕ) := Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ k ∈ Finset.range d, F k := Fin.sum_univ_eq_sum_range F d
    _ = ∑ k ∈ Finset.range 2, F k := by
        have hsub : Finset.range 2 ⊆ Finset.range d := by
          intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
        refine (Finset.sum_subset hsub ?_).symm
        intro k _ hk
        have hk2 : ¬ k < 2 := by simpa using hk
        simp only [hF]
        rw [dif_neg hk2]
    _ = ∑ i : Fin 2, F (i : ℕ) := (Fin.sum_univ_eq_sum_range F 2).symm
    _ = ∑ i : Fin 2, ‖w i‖ ^ 2 := Finset.sum_congr rfl fun i _ => (h2 i).symm

/-- Distances in the plane are the distances of the lifted points. -/
theorem norm_planePoint_sub {d : ℕ} (hd : 2 ≤ d) (u v : Sandpile.Continuum.Space 2) :
    ‖(planePoint (d := d) u) - planePoint (d := d) v‖ = ‖u - v‖ := by
  rw [← planePoint_sub, norm_planePoint hd]

/-- The dependence range: the kernels of two field values at plane points at
distance at least `2s` have disjoint supports, so their product vanishes. -/
theorem ballKernel_mul_eq_zero {d : ℕ} {s : ℝ} {u v : Sandpile.Continuum.Space 2}
    (huv : 2 * s ≤ ‖(planePoint (d := d) u) - planePoint (d := d) v‖)
    (z : Sandpile.Continuum.Space d) :
    ballKernel d s u z * ballKernel d s v z = 0 := by
  by_cases h1 : ‖(planePoint (d := d) u) - z‖ < s
  · by_cases h2 : ‖(planePoint (d := d) v) - z‖ < s
    · exfalso
      have hsplit : (planePoint (d := d) u) - planePoint (d := d) v
          = ((planePoint (d := d) u) - z) - ((planePoint (d := d) v) - z) := by abel
      have hlt : ‖(planePoint (d := d) u) - planePoint (d := d) v‖ < 2 * s := by
        calc ‖(planePoint (d := d) u) - planePoint (d := d) v‖
            = ‖((planePoint (d := d) u) - z) - ((planePoint (d := d) v) - z)‖ := by rw [hsplit]
          _ ≤ ‖(planePoint (d := d) u) - z‖ + ‖(planePoint (d := d) v) - z‖ := norm_sub_le _ _
          _ < 2 * s := by linarith
      linarith
    · simp [ballKernel, h2]
  · simp [ballKernel, h1]

/-- Two white-noise variables tested against functions with pointwise disjoint
supports are uncorrelated: the covariance of a white noise is the `L²` inner
product of the test functions. -/
theorem cov_whiteNoise_eq_zero {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (f g : Sandpile.Continuum.Space d → ℝ)
    (hf : MemLp f 2 (volume : Measure (Sandpile.Continuum.Space d)))
    (hg : MemLp g 2 (volume : Measure (Sandpile.Continuum.Space d)))
    (hfg : ∀ y, f y * g y = 0) :
    cov[W f, W g; P] = 0 := by
  have hWf : MemLp (W f) 2 P := (hW.gaussian.hasGaussianLaw_eval f).memLp_two
  have hWg : MemLp (W g) 2 P := (hW.gaussian.hasGaussianLaw_eval g).memLp_two
  rw [ProbabilityTheory.covariance_eq_sub hWf hWg, hW.mean f hf, hW.mean g hg]
  have hz : ∫ ω, W f ω * W g ω ∂P = 0 := by
    rw [hW.cov f g hf hg]
    simp [hfg]
  simpa [Pi.mul_apply] using hz

/-- Families of white-noise variables tested against functions with pairwise
disjoint supports are independent.  The families are jointly Gaussian because
the whole white noise is, and their cross-covariances vanish. -/
theorem iIndepFun_whiteNoise_of_disjoint {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    {T : Type} {S : T → Type} (f : (t : T) → S t → (Sandpile.Continuum.Space d → ℝ))
    (hmem : ∀ t s, MemLp (f t s) 2 (volume : Measure (Sandpile.Continuum.Space d)))
    (hdisj : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂), ∀ y, f t₁ s₁ y * f t₂ s₂ y = 0) :
    iIndepFun (fun t ω s => W (f t s) ω) P := by
  have hgauss : IsGaussianProcess
      (fun (p : (t : T) × S t) ω => W (f p.1 p.2) ω) P :=
    hW.gaussian.comp_right (fun p : (t : T) × S t => f p.1 p.2)
  refine ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_eq_zero hgauss ?_ ?_
  · intro t s
    exact (hW.meas _ (hmem t s)).aemeasurable
  · intro t₁ t₂ ht s₁ s₂
    exact cov_whiteNoise_eq_zero hW _ _ (hmem t₁ s₁) (hmem t₂ s₂) (hdisj t₁ t₂ ht s₁ s₂)

/-- Events read off independent families are independent. -/
theorem iIndepSet_of_comap {Ω ι : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {β : ι → Type} [∀ i, MeasurableSpace (β i)] {Y : (i : ι) → Ω → β i}
    (hY : ProbabilityTheory.iIndepFun Y P) (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet[MeasurableSpace.comap (Y i) inferInstance] (E i)) :
    ProbabilityTheory.iIndepSet E P := by
  rw [ProbabilityTheory.iIndepSet_iff_iIndep]
  refine ProbabilityTheory.iIndep_of_iIndep_of_le hY.iIndep fun i => ?_
  exact MeasurableSpace.generateFrom_le fun s hs => by
    rw [Set.mem_singleton_iff] at hs
    exact hs ▸ hE i

/-- **The dependence range of `𝒳_s` is `2s`.**  The families of field values
over regions of the plane whose points are at distance at least `2s` from each
other are independent. -/
theorem iIndepFun_ballField_of_separated {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℝ} (hs : 0 < s)
    {ι : Type} (Reg : ι → Set (Sandpile.Continuum.Space 2))
    (hsep : ∀ i j, i ≠ j → ∀ u ∈ Reg i, ∀ v ∈ Reg j, 2 * s ≤ ‖u - v‖) :
    iIndepFun (fun (i : ι) (ω : Ω) (u : Reg i) => ballField d W s (u : Sandpile.Continuum.Space 2) ω)
      P := by
  have hd2 : 2 ≤ d := by rcases hd with h | h <;> omega
  refine iIndepFun_whiteNoise_of_disjoint hW
    (fun (i : ι) (u : Reg i) => ballKernel d s (u : Sandpile.Continuum.Space 2))
    (fun i u => memLp_ballKernel hd hs _) ?_
  intro i j hij u v y
  refine ballKernel_mul_eq_zero ?_ y
  rw [norm_planePoint_sub hd2]
  exact hsep i j hij _ u.2 _ v.2

/-- The same in the form the circuit events of separated annuli are used in:
events each of which is read off the field over its own region, the regions
being at distance at least `2s` from each other, are independent. -/
theorem iIndepSet_ballField_of_separated {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℝ} (hs : 0 < s)
    {ι : Type} (Reg : ι → Set (Sandpile.Continuum.Space 2))
    (hsep : ∀ i j, i ≠ j → ∀ u ∈ Reg i, ∀ v ∈ Reg j, 2 * s ≤ ‖u - v‖)
    (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet[MeasurableSpace.comap
      (fun ω (u : Reg i) => ballField d W s (u : Sandpile.Continuum.Space 2) ω) inferInstance]
      (E i)) :
    ProbabilityTheory.iIndepSet E P :=
  iIndepSet_of_comap (iIndepFun_ballField_of_separated hd hW hs Reg hsep) E hE

end Sandpile.Support
