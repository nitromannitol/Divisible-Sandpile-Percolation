/-
The finite-dimensional clause of `prop:dlt4-heat-potential-invariance`
(`sandpile.tex:1841-1848`), reduced to two statements about the coefficients of
the rescaled linear field.

`Z_R^{\rm lin}(r,w)` is a finite linear functional of the scenery
(`linInterp_eq_sum`), and for finitely many points `(r_i,w_i)` one box carries
every site all of them read, so the whole vector is a vector of finite linear
functionals over ONE enumeration of sites.  The vector Lindeberg-Feller step then
gives the convergence to the vector of white-noise values, provided the combined
coefficients are uniformly small and their sums of squares converge to the `L²`
inner products of the Brownian Green kernels.  Those two statements, `hsmall` and
the pair `hQlim`, `hQvar`, are the only analytic input left in the clause; they
are the local central limit theorem and the Riemann-sum convergence of
`ssec:green-estimates`.
-/
import Sandpile.Support.ContVectorCLT
import Sandpile.Support.ContHeatPotential

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- Boxes about the origin grow with the radius. -/
theorem boxFinset_zero_mono {s u : ℕ} (h : s ≤ u) :
    Sandpile.boxFinset (0 : Site d) s ⊆ Sandpile.boxFinset (0 : Site d) u := by
  refine Sandpile.boxFinset_subset ?_
  rw [Sandpile.boxDist_self]
  simpa using h

/-- The largest time index among finitely many parabolic mesh times. -/
noncomputable def interpTime (R : ℝ) {m : ℕ} (r : Fin m → ℝ) : ℕ :=
  Finset.univ.sup fun i => ⌊R ^ 2 * r i⌋₊

/-- One box carrying every site the interpolations at `m` points can read. -/
noncomputable def interpBox (d : ℕ) (R L : ℝ) {m : ℕ} (r : Fin m → ℝ) : Finset (Site d) :=
  Sandpile.boxFinset (0 : Site d) (⌈|R| * L⌉₊ + 1 + 1 + (interpTime R r + 1))

/-- Every corner box of every one of the `m` interpolation cells lies in the
common box. -/
theorem interp_box_subset_max (R L : ℝ) {m : ℕ} (r : Fin m → ℝ) (w : Fin m → Space d)
    (hw : ∀ i, ‖w i‖ ≤ L) (i : Fin m) (ε : Fin d → Bool) :
    Sandpile.boxFinset (fun j => ⌊R * w i j⌋ + if ε j then 1 else 0) (⌊R ^ 2 * r i⌋₊ + 1)
      ⊆ interpBox d R L r := by
  refine subset_trans (Sandpile.Support.interp_box_subset R L (r i) (w i) (hw i) ε) ?_
  refine boxFinset_zero_mono ?_
  have hle : ⌊R ^ 2 * r i⌋₊ ≤ interpTime R r :=
    Finset.le_sup (f := fun j => ⌊R ^ 2 * r j⌋₊) (Finset.mem_univ i)
  omega

/-- Every one of the `m` interpolated fields is a finite linear functional of the
scenery over the common box. -/
theorem linInterp_eq_sum_interpBox (R L : ℝ) {m : ℕ} (r : Fin m → ℝ) (w : Fin m → Space d)
    (hw : ∀ i, ‖w i‖ ≤ L) (ζ : Site d → ℝ) (i : Fin m) :
    Sandpile.Frozen.HeatPotentialInvariance.linInterp d R ζ (r i) (w i)
      = ∑ k : Fin (interpBox d R L r).card,
          interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k) *
            ζ (siteEnum (interpBox d R L r) k) :=
  linInterp_eq_sum R (r i) ζ (w i) fun ε => interp_box_subset_max R L r w hw i ε

/-- **The finite-dimensional convergence of the rescaled linear field**, granted
the two coefficient statements.  This is the first clause of
`prop:dlt4-heat-potential-invariance`. -/
theorem heat_potential_fd_of (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    {m : ℕ} (r : Fin m → ℝ) (w : Fin m → Space d) (L : ℝ) (hw : ∀ i, ‖w i‖ ≤ L)
    (hmemg : ∀ i, MemLp (fun y => Sandpile.Continuum.greenTimeBM d (r i) (w i) y) 2
      (volume : Measure (Space d)))
    (Q : (Fin m → ℝ) → ℝ)
    (hsmall : ∀ (t : Fin m → ℝ) (δ : ℝ), 0 < δ → ∀ᶠ R : ℝ in atTop,
      ∀ k : Fin (interpBox d R L r).card,
        |∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)| ≤ δ)
    (hQlim : ∀ t : Fin m → ℝ, Tendsto (fun R : ℝ => ∑ k : Fin (interpBox d R L r).card,
      (∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)) ^ 2)
      atTop (𝓝 (Q t)))
    (hQvar : ∀ t : Fin m → ℝ, (∫ z, z ^ 2 ∂ν) * Q t
      = ∫ y : Space d,
          (∑ i, t i * (Real.sqrt (variance (id : ℝ → ℝ) ν) *
            Sandpile.Continuum.greenTimeBM d (r i) (w i) y)) *
          ∑ i, t i * (Real.sqrt (variance (id : ℝ → ℝ) ν) *
            Sandpile.Continuum.greenTimeBM d (r i) (w i) y)) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site d → ℝ) (i : Fin m) =>
        Sandpile.Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) (r i) (w i))
      atTop
      (fun (ω : ΩW) (i : Fin m) =>
        Sandpile.Continuum.gaussianPotential d (variance (id : ℝ → ℝ) ν) W (r i) (w i) ω)
      (fun _ => Sandpile.centeredMassLaw d ν) PW := by
  classical
  set c : ℝ := Real.sqrt (variance (id : ℝ → ℝ) ν) with hc
  set g : Fin m → Space d → ℝ :=
    fun i y => c * Sandpile.Continuum.greenTimeBM d (r i) (w i) y with hgdef
  have hgmem : ∀ i, MemLp (g i) 2 (volume : Measure (Space d)) := fun i =>
    (hmemg i).const_mul c
  have hvec := tendstoInDistribution_vector_pick_mass hd ν hsq hmean
    (fun (R : ℝ) (σ : Site d → ℝ) (i : Fin m) =>
      Sandpile.Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) (r i) (w i))
    (fun R => (interpBox d R L r).card)
    (fun R i k => interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k))
    (fun R => siteEnum (interpBox d R L r))
    (fun R => siteEnum_injective _)
    (fun R σ i => linInterp_eq_sum_interpBox R L r w hw (Sandpile.scenery d σ) i)
    PW W hW g hgmem Q hsmall hQlim hQvar
  refine hvec.congr (fun R => Filter.EventuallyEq.refl _ _) ?_
  have hsm : ∀ i, W (g i) =ᵐ[PW] fun ω =>
      Sandpile.Continuum.gaussianPotential d (variance (id : ℝ → ℝ) ν) W (r i) (w i) ω := by
    intro i
    have hfun : g i = c • fun y => Sandpile.Continuum.greenTimeBM d (r i) (w i) y := by
      funext y
      simp [hgdef]
    rw [hfun]
    exact hW.smul c (fun y => Sandpile.Continuum.greenTimeBM d (r i) (w i) y) (hmemg i)
  have := (MeasureTheory.ae_all_iff (ι := Fin m)
    (p := fun ω i => W (g i) ω =
      Sandpile.Continuum.gaussianPotential d (variance (id : ℝ → ℝ) ν) W (r i) (w i) ω)).mpr hsm
  filter_upwards [this] with ω hω
  funext i
  exact hω i

/-- The multilinear interpolation weights of one mesh cell sum to one.  This is what
turns a bound on the Green kernels at the corners of a cell into a bound on the
interpolation coefficient. -/
theorem sum_interp_weights (d : ℕ) (u : Fin d → ℝ) :
    ∑ ε : Fin d → Bool, ∏ i, (if ε i then u i else 1 - u i) = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset Bool))
    (fun (i : Fin d) (b : Bool) => if b then u i else 1 - u i)
  simp only [Fintype.piFinset_univ, Fintype.sum_bool] at h
  rw [← h]
  simp

end Sandpile.Support
