import Sandpile.Support.ContMomentModulus
import Sandpile.Support.ContKolmogorovMoments
import LatticeProb.Prob.KolmogorovBound

/-!
# The tightness clause via the multi-parameter Kolmogorov criterion

The quantitative multi-parameter Kolmogorov criterion is stated for a process indexed by a
compact box of `ℝ^k`, while the tightness clause of the heat-potential invariance principle is
about a process indexed by a compact subset of `ℝ × Space d`. This file assembles the
coordinates of `ℝ × Space d` into a point of `ℝ^{d+1}` (`toPi`, `ofPi`), builds the box that
contains the image of a compact set of times in `[0, T]` and space points of norm at most `L`
(`boxLo`, `boxHi`), compares the two distance functions, and transports the moment, measurability
and continuity hypotheses of the criterion to the interpolated field `piField`, uniformly in the
mesh scale `R`. `heat_potential_tightness_of_criterion` then applies the criterion in one step.
-/

open MeasureTheory ProbabilityTheory
open Sandpile.Frozen.HeatPotentialInvariance

namespace Sandpile.Support

variable {d : ℕ}

/-- The coordinates of a point of `ℝ × ℝ^d`, assembled into a point of
`ℝ^{d+1}`: the time first, then the space coordinates. -/
noncomputable def toPi (p : ℝ × Sandpile.Continuum.Space d) : Fin (d + 1) → ℝ :=
  Fin.cons p.1 (fun j => p.2 j)

/-- The zeroth coordinate of `toPi p` is the time coordinate `p.1`. -/
@[simp] theorem toPi_zero (p : ℝ × Sandpile.Continuum.Space d) : toPi p 0 = p.1 := rfl

/-- The `j.succ`-th coordinate of `toPi p` is the space coordinate `p.2 j`. -/
@[simp] theorem toPi_succ (p : ℝ × Sandpile.Continuum.Space d) (j : Fin d) :
    toPi p j.succ = p.2 j := rfl

/-- The point of `ℝ × ℝ^d` read off a point of `ℝ^{d+1}`. -/
noncomputable def ofPi (u : Fin (d + 1) → ℝ) : ℝ × Sandpile.Continuum.Space d :=
  (u 0, WithLp.toLp 2 (fun j : Fin d => u j.succ))

/-- Reading `ofPi` off `toPi p` recovers the original point of `ℝ × Space d`. -/
theorem ofPi_toPi (p : ℝ × Sandpile.Continuum.Space d) : ofPi (toPi p) = p := rfl

/-- The sup distance of the assembled coordinates is at most the distance of the
points. -/
theorem dist_toPi_le (p q : ℝ × Sandpile.Continuum.Space d) :
    dist (toPi p) (toPi q) ≤ dist p q := by
  refine (dist_pi_le_iff dist_nonneg).mpr ?_
  intro i
  refine Fin.cases ?_ ?_ i
  · show dist p.1 q.1 ≤ dist p q
    rw [Prod.dist_eq]
    exact le_max_left _ _
  · intro j
    show dist (p.2 j) (q.2 j) ≤ dist p q
    have h1 : dist (p.2 j) (q.2 j) ≤ ‖p.2 - q.2‖ := by
      rw [Real.dist_eq]
      have := abs_coord_le_norm (p.2 - q.2) j
      simpa using this
    rw [← dist_eq_norm] at h1
    refine le_trans h1 ?_
    rw [Prod.dist_eq]
    exact le_max_right _ _

/-- The `ℓ¹` displacement of the coordinates is at most `1 + d` times their sup
distance. -/
theorem sum_abs_sub_le_dist_pi (u v : Fin (d + 1) → ℝ) :
    |u 0 - v 0| + ∑ j : Fin d, |u j.succ - v j.succ| ≤ (1 + (d : ℝ)) * dist u v := by
  have hcoord : ∀ i : Fin (d + 1), |u i - v i| ≤ dist u v := by
    intro i
    rw [← Real.dist_eq]
    exact dist_le_pi_dist u v i
  have hsum : ∑ j : Fin d, |u j.succ - v j.succ| ≤ (d : ℝ) * dist u v := by
    calc ∑ j : Fin d, |u j.succ - v j.succ| ≤ ∑ _j : Fin d, dist u v :=
          Finset.sum_le_sum fun j _ => hcoord j.succ
      _ = (d : ℝ) * dist u v := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith [hcoord 0, hsum]

/-- The lower corner of the box of `ℝ^{d+1}` that carries the times `[0,T]` and
the space ball of radius `L`. -/
noncomputable def boxLo (d : ℕ) (L : ℝ) : Fin (d + 1) → ℝ := Fin.cons 0 (fun _ => -L)

/-- The upper corner of that box. -/
noncomputable def boxHi (d : ℕ) (T L : ℝ) : Fin (d + 1) → ℝ := Fin.cons T (fun _ => L)

/-- The lower corner `boxLo d L` is at most the upper corner `boxHi d T L` coordinatewise,
provided `T` and `L` are nonnegative. -/
theorem boxLo_le_boxHi (d : ℕ) (L T : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L) :
    boxLo d L ≤ boxHi d T L := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [boxLo, boxHi] using hT
  · intro j; simpa [boxLo, boxHi] using hL

/-- A point of `ℝ^{d+1}` lies in the box `Set.Icc (boxLo d L) (boxHi d T L)` exactly when its
zeroth coordinate lies in `[0, T]` and every other coordinate lies in `[-L, L]`. -/
theorem mem_box_iff (T L : ℝ) (u : Fin (d + 1) → ℝ) :
    u ∈ Set.Icc (boxLo d L) (boxHi d T L) ↔
      ((0 ≤ u 0 ∧ u 0 ≤ T) ∧ ∀ j : Fin d, -L ≤ u j.succ ∧ u j.succ ≤ L) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨⟨hlo 0, hhi 0⟩, fun j => ⟨hlo j.succ, hhi j.succ⟩⟩
  · rintro ⟨⟨h00, h0T⟩, hj⟩
    constructor
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact h00
      · intro j; exact (hj j).1
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact h0T
      · intro j; exact (hj j).2

/-- The assembled coordinates `toPi p` of a point `p` with time in `[0, T]` and space part of
norm at most `L` lie in the box `Set.Icc (boxLo d L) (boxHi d T L)`. -/
theorem toPi_mem_box {T L : ℝ} {p : ℝ × Sandpile.Continuum.Space d}
    (h0 : 0 ≤ p.1) (hT : p.1 ≤ T) (hL : ‖p.2‖ ≤ L) :
    toPi p ∈ Set.Icc (boxLo d L) (boxHi d T L) := by
  refine (mem_box_iff T L (toPi p)).mpr ⟨⟨h0, hT⟩, fun j => ?_⟩
  have h := le_trans (abs_coord_le_norm p.2 j) hL
  rw [abs_le] at h
  exact ⟨h.1, h.2⟩

/-- The interpolated rescaled field, read as a process indexed by `ℝ^{d+1}`. -/
noncomputable def piField (d : ℕ) (R : ℝ) (u : Fin (d + 1) → ℝ) (σ : Site d → ℝ) : ℝ :=
  linInterp d R (Sandpile.scenery d σ) (ofPi u).1 (ofPi u).2

/-- The interpolated field `piField` at the assembled coordinates `toPi p` agrees with
`linInterp` applied directly to the time and space components of `p`. -/
theorem piField_toPi (R : ℝ) (p : ℝ × Sandpile.Continuum.Space d) (σ : Site d → ℝ) :
    piField d R (toPi p) σ = linInterp d R (Sandpile.scenery d σ) p.1 p.2 := by
  rw [piField, ofPi_toPi]

/-- The space part of a point of the box has norm at most `√d L`. -/
theorem norm_ofPi_le {L : ℝ} (hL : 0 ≤ L) {u : Fin (d + 1) → ℝ}
    (h : ∀ j : Fin d, |u j.succ| ≤ L) : ‖(ofPi u).2‖ ≤ Real.sqrt (d : ℝ) * L := by
  have hsum : ∑ j : Fin d, ‖(ofPi u).2 j‖ ^ 2 ≤ (d : ℝ) * L ^ 2 := by
    calc ∑ j : Fin d, ‖(ofPi u).2 j‖ ^ 2 ≤ ∑ _j : Fin d, L ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hj : ‖(ofPi u).2 j‖ = |u j.succ| := rfl
          rw [hj]
          nlinarith [h j, abs_nonneg (u j.succ)]
      _ = (d : ℝ) * L ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ j : Fin d, ‖(ofPi u).2 j‖ ^ 2) ≤ Real.sqrt ((d : ℝ) * L ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * L := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hL]

/-- The `ℓ¹` displacement of the space coordinates of two points of the box. -/
theorem sum_abs_sub_box_le {T L : ℝ} {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ Set.Icc (boxLo d L) (boxHi d T L))
    (hv : v ∈ Set.Icc (boxLo d L) (boxHi d T L)) :
    ∑ j : Fin d, |(ofPi u).2 j - (ofPi v).2 j| ≤ 2 * (d : ℝ) * L := by
  obtain ⟨_, hju⟩ := (mem_box_iff T L u).mp hu
  obtain ⟨_, hjv⟩ := (mem_box_iff T L v).mp hv
  calc ∑ j : Fin d, |(ofPi u).2 j - (ofPi v).2 j| ≤ ∑ _j : Fin d, (2 * L) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : |u j.succ| ≤ L := abs_le.mpr ⟨(hju j).1, (hju j).2⟩
        have h2 : |v j.succ| ≤ L := abs_le.mpr ⟨(hjv j).1, (hjv j).2⟩
        have hshow : |(ofPi u).2 j - (ofPi v).2 j| = |u j.succ - v j.succ| := rfl
        rw [hshow]
        calc |u j.succ - v j.succ| ≤ |u j.succ| + |v j.succ| := abs_sub _ _
          _ ≤ 2 * L := by linarith
    _ = 2 * (d : ℝ) * L := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The moment hypothesis of the criterion for the interpolated field on the
box of `ℝ^{d+1}`, with a constant free of the scale.** -/
theorem measurable_piField (R : ℝ) (u : Fin (d + 1) → ℝ) :
    Measurable (fun σ : Site d → ℝ => piField d R u σ) := by
  classical
  set s : Finset (Site d) := Sandpile.boxFinset (0 : Site d)
    (⌈|R| * ‖(ofPi u).2‖⌉₊ + 1 + 1 + (⌊R ^ 2 * (ofPi u).1⌋₊ + 1)) with hsdef
  have hps : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * (ofPi u).2 i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * (ofPi u).1⌋₊ + 1) ⊆ s :=
    fun ε => interp_box_subset R ‖(ofPi u).2‖ (ofPi u).1 (ofPi u).2 le_rfl ε
  have hrep : ∀ σ : Site d → ℝ, piField d R u σ
      = ∑ i, interpCoeff d R (ofPi u).1 (ofPi u).2 (Sandpile.siteEnum s i)
          * Sandpile.scenery d σ (Sandpile.siteEnum s i) := by
    intro σ
    rw [piField, linInterp_eq_sum R (ofPi u).1 (Sandpile.scenery d σ) (ofPi u).2 hps]
  rw [show (fun σ : Site d → ℝ => piField d R u σ)
      = fun σ => ∑ i, interpCoeff d R (ofPi u).1 (ofPi u).2 (Sandpile.siteEnum s i)
          * Sandpile.scenery d σ (Sandpile.siteEnum s i) from funext hrep]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact measurable_const.mul ((measurable_pi_apply (Sandpile.siteEnum s i)).comp
    (Sandpile.measurable_scenery d))

/-- **The `p`-th power of an increment of the interpolated field is
integrable**, for `p ≥ 1`, as soon as the one-site law has a `p`-th moment.  The
increment is the pairing of the increment of the coefficient vector with the
scenery on the box the two cells reach. -/
theorem integrable_piField_sub_rpow (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 1 ≤ p) (hint : Integrable (fun z => |z| ^ p) ν)
    (R T L : ℝ) (u v : Fin (d + 1) → ℝ)
    (_hu : u ∈ Set.Icc (boxLo d L) (boxHi d T L))
    (_hv : v ∈ Set.Icc (boxLo d L) (boxHi d T L)) :
    Integrable (fun σ : Site d → ℝ => |piField d R u σ - piField d R v σ| ^ p)
      (Sandpile.centeredMassLaw d ν) := by
  classical
  set s : Finset (Site d) := Sandpile.boxFinset (0 : Site d)
    (max (⌈|R| * ‖(ofPi u).2‖⌉₊ + 1 + 1 + (⌊R ^ 2 * (ofPi u).1⌋₊ + 1))
      (⌈|R| * ‖(ofPi v).2‖⌉₊ + 1 + 1 + (⌊R ^ 2 * (ofPi v).1⌋₊ + 1))) with hsdef
  have hps : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * (ofPi u).2 i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * (ofPi u).1⌋₊ + 1) ⊆ s := fun ε =>
    subset_trans (interp_box_subset R ‖(ofPi u).2‖ (ofPi u).1 (ofPi u).2 le_rfl ε)
      (boxFinset_zero_mono (le_max_left _ _))
  have hqs : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * (ofPi v).2 i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * (ofPi v).1⌋₊ + 1) ⊆ s := fun ε =>
    subset_trans (interp_box_subset R ‖(ofPi v).2‖ (ofPi v).1 (ofPi v).2 le_rfl ε)
      (boxFinset_zero_mono (le_max_right _ _))
  have h := integrable_linInterp_sub_rpow hd ν hp hint R (ofPi u).1 (ofPi v).1
    (ofPi u).2 (ofPi v).2 s hps hqs
  simpa only [piField] using h

/-- The `p`-th power of the interpolated field itself is integrable, for `p ≥ 1`, as soon as
the one-site law has a `p`-th moment. -/
theorem integrable_piField_rpow (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 1 ≤ p) (hint : Integrable (fun z => |z| ^ p) ν)
    (R T L : ℝ) (u : Fin (d + 1) → ℝ)
    (_hu : u ∈ Set.Icc (boxLo d L) (boxHi d T L)) :
    Integrable (fun σ : Site d → ℝ => |piField d R u σ| ^ p)
      (Sandpile.centeredMassLaw d ν) := by
  classical
  set s : Finset (Site d) := Sandpile.boxFinset (0 : Site d)
    (⌈|R| * ‖(ofPi u).2‖⌉₊ + 1 + 1 + (⌊R ^ 2 * (ofPi u).1⌋₊ + 1)) with hsdef
  have hps : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * (ofPi u).2 i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * (ofPi u).1⌋₊ + 1) ⊆ s := fun ε =>
    interp_box_subset R ‖(ofPi u).2‖ (ofPi u).1 (ofPi u).2 le_rfl ε
  have h := integrable_linInterp_rpow hd ν hp hint R (ofPi u).1 (ofPi u).2 s hps
  simpa only [piField] using h

/-- **The moment-increment bound of the Kolmogorov criterion for the interpolated field
indexed by `ℝ^{d+1}`**, with Hölder exponent `p * min(1 - d/4, (1-θ)/4)` and a constant
depending only on `T`, `L`, `p` and `θ`, uniform in the mesh scale `R ≥ 1`. -/
theorem exists_pi_moment_modulus
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (p : ℝ) (hp : 2 ≤ p)
    (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L) :
    ∃ M : ℝ, 0 < M ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∫ z, z ∂ν = 0) →
      Integrable (fun z => |z| ^ p) ν → ∀ R : ℝ, 1 ≤ R →
        ∀ u ∈ Set.Icc (boxLo d L) (boxHi d T L), ∀ v ∈ Set.Icc (boxLo d L) (boxHi d T L),
          ∫ σ, |piField d R u σ - piField d R v σ| ^ p ∂(Sandpile.centeredMassLaw d ν)
            ≤ M * Sandpile.resampleMoment ν p
              * dist u v ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := by
  obtain ⟨M₀, hM₀, hmod⟩ := exists_moment_modulus_linInterp hHK hd hd3 hθ0 hθ1 p hp
    T (2 * (d : ℝ) * L) hT (by positivity)
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hp0 : (0:ℝ) < p := by linarith
  have hβ0 : (0:ℝ) < min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := lt_min (by linarith) (by linarith)
  have hpβ : (0:ℝ) ≤ p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := by positivity
  refine ⟨M₀ * (1 + (d : ℝ)) ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4)),
    by positivity, ?_⟩
  intro ν hν hmean hint R hR u hu v hv
  haveI := hν
  obtain ⟨⟨hu0, huT⟩, _⟩ := (mem_box_iff T L u).mp hu
  obtain ⟨⟨hv0, hvT⟩, _⟩ := (mem_box_iff T L v).mp hv
  have hmain := hmod ν hν hmean hint R hR (ofPi u).1 (ofPi v).1 (ofPi u).2 (ofPi v).2
    hu0 hv0 huT hvT (sum_abs_sub_box_le hu hv)
  refine le_trans hmain ?_
  have hδ0 : (0:ℝ) ≤ |(ofPi u).1 - (ofPi v).1| + ∑ j : Fin d, |(ofPi u).2 j - (ofPi v).2 j| := by
    have h1 : (0:ℝ) ≤ ∑ j : Fin d, |(ofPi u).2 j - (ofPi v).2 j| :=
      Finset.sum_nonneg fun j _ => abs_nonneg _
    have h2 := abs_nonneg ((ofPi u).1 - (ofPi v).1)
    linarith
  have hdle : |(ofPi u).1 - (ofPi v).1| + ∑ j : Fin d, |(ofPi u).2 j - (ofPi v).2 j|
      ≤ (1 + (d : ℝ)) * dist u v := sum_abs_sub_le_dist_pi u v
  have hpow : (|(ofPi u).1 - (ofPi v).1| + ∑ j : Fin d, |(ofPi u).2 j - (ofPi v).2 j|)
        ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
      ≤ (1 + (d : ℝ)) ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
        * dist u v ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := by
    rw [← Real.mul_rpow (by positivity) dist_nonneg]
    exact Real.rpow_le_rpow hδ0 hdle hpβ
  have hm0 : (0:ℝ) ≤ Sandpile.resampleMoment ν p := LatticeProb.pairMoment_nonneg ν p
  calc M₀ * Sandpile.resampleMoment ν p
        * (|(ofPi u).1 - (ofPi v).1| + ∑ j : Fin d, |(ofPi u).2 j - (ofPi v).2 j|)
          ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
      ≤ M₀ * Sandpile.resampleMoment ν p
        * ((1 + (d : ℝ)) ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
          * dist u v ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = M₀ * (1 + (d : ℝ)) ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
        * Sandpile.resampleMoment ν p
        * dist u v ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := by ring

/-- `ofPi` is continuous: its time component is a coordinate projection, and its space
component is the inverse of the `Space d` equivalence composed with coordinate projections. -/
theorem continuous_ofPi : Continuous (ofPi (d := d)) := by
  refine Continuous.prodMk (continuous_apply 0) ?_
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp
    (continuous_pi fun j => continuous_apply j.succ)

/-- **Every sample path of the interpolated field is continuous on the box.** -/
theorem continuousOn_piField
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (R : ℝ) (hR : 1 ≤ R) (σ : Site d → ℝ) (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L) :
    ContinuousOn (fun u => piField d R u σ) (Set.Icc (boxLo d L) (boxHi d T L)) := by
  have hbase := continuousOn_linInterp_box hHK hd hd3 hθ0 hθ1 R hR (Sandpile.scenery d σ)
    T (Real.sqrt (d : ℝ) * L) hT (by positivity)
  have hmaps : Set.MapsTo (ofPi (d := d)) (Set.Icc (boxLo d L) (boxHi d T L))
      (Set.Icc (0:ℝ) T ×ˢ Metric.closedBall
        (0 : Sandpile.Continuum.Space d) (Real.sqrt (d : ℝ) * L)) := by
    intro u hu
    obtain ⟨⟨h0, hTu⟩, hj⟩ := (mem_box_iff T L u).mp hu
    refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨h0, hTu⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_ofPi_le hL fun j => abs_le.mpr ⟨(hj j).1, (hj j).2⟩
  exact hbase.comp continuous_ofPi.continuousOn hmaps

/-- **The one-point moment bound at the lower corner of the box.** -/
theorem exists_pi_one_point_moment
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (p : ℝ) (hp : 2 ≤ p) (T L : ℝ) (hT : 0 ≤ T) :
    ∃ M : ℝ, 0 < M ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∫ z, z ∂ν = 0) →
      Integrable (fun z => |z| ^ p) ν → ∀ R : ℝ, 1 ≤ R →
        ∫ σ, |piField d R (boxLo d L) σ| ^ p ∂(Sandpile.centeredMassLaw d ν)
          ≤ M * Sandpile.resampleMoment ν p := by
  obtain ⟨M, hM, hone⟩ := exists_one_point_moment_linInterp hHK hd hd3 p hp T hT
  refine ⟨M, hM, ?_⟩
  intro ν hν hmean hint R hR
  haveI := hν
  have h0 : (ofPi (boxLo d L)).1 = (0:ℝ) := rfl
  have := hone ν hν hmean hint R hR (ofPi (boxLo d L)).1 (ofPi (boxLo d L)).2
    (by rw [h0]) (by rw [h0]; exact hT)
  exact this

/-- **The modulus clause of the quantitative multi-parameter Kolmogorov
criterion.**  The modulus `δ` is chosen before the process, so that one choice
serves every scale. -/
def KolmogorovModulusPi : Prop :=
  ∀ (k : ℕ) (a b : Fin k → ℝ) (p q M : ℝ), 0 < p → (k : ℝ) < q →
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ X : (Fin k → ℝ) → Ω → ℝ,
          (∀ u, Measurable (X u)) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            Integrable (fun ω => |X u ω - X v ω| ^ p) P) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q) →
          (∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b)) →
          P {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b, dist u v < δ ∧ η < |X u ω - X v ω|}
            ≤ ENNReal.ofReal ε

/-- **The uniform-norm clause of the quantitative multi-parameter Kolmogorov
criterion.**  The bound `B` is chosen before the process. -/
def KolmogorovBoundPi : Prop :=
  ∀ (k : ℕ) (a b : Fin k → ℝ) (p q M : ℝ), 0 < p → (k : ℝ) < q →
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ X : (Fin k → ℝ) → Ω → ℝ,
          (∀ u, Measurable (X u)) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            Integrable (fun ω => |X u ω - X v ω| ^ p) P) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q) →
          Integrable (fun ω => |X a ω| ^ p) P →
          (∫ ω, |X a ω| ^ p ∂P ≤ M) →
          (∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b)) →
          P {ω | ∃ u ∈ Set.Icc a b, B < |X u ω|} ≤ ENNReal.ofReal ε

/-- **The tightness clause of `prop:dlt4-heat-potential-invariance`, from the two
statements of the quantitative multi-parameter Kolmogorov criterion.**  The
moment exponent is chosen so that `p β` exceeds the number `d + 1` of parameters,
which is possible because `β = min(1 - d/4, (1-θ)/4)` is positive for `d ≤ 3` and
`θ < 1`; the two constants of the criterion are then free of the scale, because
the moment bound is. -/
theorem heat_potential_tightness_of_criterion
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hDelta : KolmogorovModulusPi) (hBound : KolmogorovBoundPi)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hmomν : ∀ p : ℝ, 2 ≤ p → Integrable (fun z => |z| ^ p) ν)
    (T : ℝ) (hT : 0 < T)
    (K : Set (ℝ × Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (hKT : K ⊆ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) :
    (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
        (Sandpile.centeredMassLaw d ν)
            {σ | ∃ x ∈ K, M < |linInterp d R (Sandpile.scenery d σ) x.1 x.2|}
          ≤ ENNReal.ofReal ε) ∧
      (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
        (Sandpile.centeredMassLaw d ν)
            {σ | ∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧
              η < |linInterp d R (Sandpile.scenery d σ) x.1 x.2
                - linInterp d R (Sandpile.scenery d σ) y.1 y.2|}
          ≤ ENNReal.ofReal ε) := by
  classical
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hβ0 : (0:ℝ) < min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := lt_min (by linarith) (by linarith)
  set β : ℝ := min (1 - (d : ℝ) / 4) ((1 - θ) / 4) with hβdef
  set p₀ : ℝ := 2 + ((d : ℝ) + 2) / β with hp₀def
  have hp₀ : (2:ℝ) ≤ p₀ := by
    have : (0:ℝ) ≤ ((d : ℝ) + 2) / β := by positivity
    rw [hp₀def]; linarith
  have hp₀0 : (0:ℝ) < p₀ := by linarith
  have hp₀1 : (1:ℝ) ≤ p₀ := by linarith
  have hpβ : p₀ * β = 2 * β + ((d : ℝ) + 2) := by
    rw [hp₀def, add_mul, div_mul_cancel₀ _ hβ0.ne']
  have hq : ((d + 1 : ℕ) : ℝ) < p₀ * β := by
    rw [hpβ]
    push_cast
    linarith
  -- the radius of the compact set
  obtain ⟨L₀, hL₀⟩ := (hK.image continuous_snd).isBounded.subset_closedBall
    (0 : Sandpile.Continuum.Space d)
  have hL : (0:ℝ) ≤ max L₀ 0 := le_max_right _ _
  set L : ℝ := max L₀ 0 with hLdef
  have hKL : ∀ x ∈ K, ‖x.2‖ ≤ L := by
    intro x hx
    have hmem : x.2 ∈ Metric.closedBall (0 : Sandpile.Continuum.Space d) L₀ :=
      hL₀ ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact le_trans hmem (le_max_left _ _)
  have hbox : ∀ x ∈ K, toPi x ∈ Set.Icc (boxLo d L) (boxHi d T L) := by
    intro x hx
    have h1 := hKT hx
    exact toPi_mem_box (Set.mem_Icc.mp (Set.mem_prod.mp h1).1).1
      (Set.mem_Icc.mp (Set.mem_prod.mp h1).1).2 (hKL x hx)
  have hint := hmomν p₀ hp₀
  obtain ⟨Mmod, hMmod, hmod⟩ :=
    exists_pi_moment_modulus hHK hd hd3 hθ0 hθ1 p₀ hp₀ T L hT.le hL
  obtain ⟨Mpt, hMpt, hpt⟩ := exists_pi_one_point_moment hHK hd hd3 p₀ hp₀ T L hT.le
  have hm0 : (0:ℝ) ≤ Sandpile.resampleMoment ν p₀ := LatticeProb.pairMoment_nonneg ν p₀
  set MM : ℝ := (Mmod + Mpt) * Sandpile.resampleMoment ν p₀ + 1 with hMMdef
  have hmomhyp : ∀ R : ℝ, 1 ≤ R →
      ∀ u ∈ Set.Icc (boxLo d L) (boxHi d T L), ∀ v ∈ Set.Icc (boxLo d L) (boxHi d T L),
        ∫ σ, |piField d R u σ - piField d R v σ| ^ p₀ ∂(Sandpile.centeredMassLaw d ν)
          ≤ MM * dist u v ^ (p₀ * β) := by
    intro R hR u hu v hv
    refine le_trans (hmod ν inferInstance hmean hint R hR u hu v hv) ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg dist_nonneg _)
    rw [hMMdef]
    nlinarith [hm0, hMpt.le, hMmod.le]
  have hpthyp : ∀ R : ℝ, 1 ≤ R →
      ∫ σ, |piField d R (boxLo d L) σ| ^ p₀ ∂(Sandpile.centeredMassLaw d ν) ≤ MM := by
    intro R hR
    refine le_trans (hpt ν inferInstance hmean hint R hR) ?_
    rw [hMMdef]
    nlinarith [hm0, hMpt.le, hMmod.le]
  have hconthyp : ∀ R : ℝ, 1 ≤ R → ∀ σ : Site d → ℝ,
      ContinuousOn (fun u => piField d R u σ) (Set.Icc (boxLo d L) (boxHi d T L)) :=
    fun R hR σ => continuousOn_piField hHK hd hd3 hθ0 hθ1 R hR σ T L hT.le hL
  constructor
  · intro ε hε
    obtain ⟨B, hB⟩ := hBound (d + 1) (boxLo d L) (boxHi d T L) p₀ (p₀ * β) MM hp₀0 hq ε hε
    refine ⟨B, fun R hR => ?_⟩
    refine le_trans (measure_mono ?_)
      (hB (Sandpile.centeredMassLaw d ν) inferInstance (piField d R)
        (fun u => measurable_piField R u)
        (fun u hu v hv => integrable_piField_sub_rpow hd ν hp₀1 hint R T L u v hu hv)
        (hmomhyp R hR)
        (integrable_piField_rpow hd ν hp₀1 hint R T L (boxLo d L)
          (Set.left_mem_Icc.mpr (boxLo_le_boxHi d L T hT.le hL)))
        (hpthyp R hR) (hconthyp R hR))
    intro σ hσ
    obtain ⟨x, hx, hlt⟩ := hσ
    refine ⟨toPi x, hbox x hx, ?_⟩
    rwa [piField_toPi]
  · intro ε η hε hη
    obtain ⟨δ, hδ0, hδ⟩ :=
      hDelta (d + 1) (boxLo d L) (boxHi d T L) p₀ (p₀ * β) MM hp₀0 hq ε η hε hη
    refine ⟨δ, hδ0, fun R hR => ?_⟩
    refine le_trans (measure_mono ?_)
      (hδ (Sandpile.centeredMassLaw d ν) inferInstance (piField d R)
        (fun u => measurable_piField R u)
        (fun u hu v hv => integrable_piField_sub_rpow hd ν hp₀1 hint R T L u v hu hv)
        (hmomhyp R hR) (hconthyp R hR))
    intro σ hσ
    obtain ⟨x, hx, y, hy, hdlt, hlt⟩ := hσ
    refine ⟨toPi x, hbox x hx, toPi y, hbox y hy,
      lt_of_le_of_lt (dist_toPi_le x y) hdlt, ?_⟩
    rwa [piField_toPi, piField_toPi]

/-- **The modulus clause of the criterion, from the library.**  The library's
`LatticeProb.kolmogorovModulusPi` is the same statement with `δ` chosen before
the process, so the two are definitionally equal. -/
theorem kolmogorovModulusPi_holds : KolmogorovModulusPi :=
  LatticeProb.kolmogorovModulusPi

/-- **The uniform-norm clause of the criterion, from the library.** -/
theorem kolmogorovBoundPi_holds : KolmogorovBoundPi :=
  LatticeProb.kolmogorovBoundPi

end Sandpile.Support
