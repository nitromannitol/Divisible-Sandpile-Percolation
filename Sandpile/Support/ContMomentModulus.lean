/-
The moment hypothesis of the multi-parameter Kolmogorov criterion for the
interpolated rescaled field, uniformly in the scale.

`ContLinMoment` prices the centred `p`-th moment of the increment of the field by
the `ℓ²` norm of the increment of its coefficient vector, and `ContCoeffCoarse`
prices that `ℓ²` norm by a power of the distance with a constant free of the
scale.  This module joins the two, and removes the centring: the scenery of a
centred mass field has mean zero, so the field itself has mean zero, and the
centred moment is the moment.  What comes out is exactly the hypothesis
`∫ |X u - X v|^p ≤ M dist(u,v)^q` of the criterion, with `q = p β` and `M` free
of the scale, together with the one-point moment bound the criterion's
uniform-norm clause asks for.
-/
import Sandpile.Support.ContCoeffCoarse
import Sandpile.Support.ContLinMoment
import LatticeProb.Support.ContSums

open LatticeProb

open MeasureTheory ProbabilityTheory
open Sandpile.Frozen.HeatPotentialInvariance

namespace Sandpile.Support

variable {d : ℕ}

/-- **The interpolated field has mean zero.**  It is a finite linear functional
of the scenery, and the scenery of a centred mass field is an i.i.d. field with
mean zero. -/
theorem integral_linInterp_sub_eq_zero (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hνint : Integrable (fun z : ℝ => z) ν)
    (R r r' : ℝ) (w w' : Sandpile.Continuum.Space d) :
    ∫ τ, (linInterp d R (Sandpile.scenery d τ) r w
        - linInterp d R (Sandpile.scenery d τ) r' w') ∂(Sandpile.centeredMassLaw d ν) = 0 := by
  classical
  set s : Finset (Site d) := Sandpile.boxFinset (0 : Site d)
    (max (⌈|R| * ‖w‖⌉₊ + 1 + 1 + (⌊R ^ 2 * r⌋₊ + 1))
      (⌈|R| * ‖w'‖⌉₊ + 1 + 1 + (⌊R ^ 2 * r'⌋₊ + 1))) with hsdef
  have hps : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * r⌋₊ + 1) ⊆ s := fun ε =>
    subset_trans (interp_box_subset R ‖w‖ r w le_rfl ε) (boxFinset_zero_mono (le_max_left _ _))
  have hqs : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w' i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * r'⌋₊ + 1) ⊆ s := fun ε =>
    subset_trans (interp_box_subset R ‖w'‖ r' w' le_rfl ε)
      (boxFinset_zero_mono (le_max_right _ _))
  have hrep : ∀ σ : Site d → ℝ,
      linInterp d R (Sandpile.scenery d σ) r w - linInterp d R (Sandpile.scenery d σ) r' w'
        = ∑ i : Fin s.card,
            (interpCoeff d R r w (Sandpile.siteEnum s i)
              - interpCoeff d R r' w' (Sandpile.siteEnum s i))
            * Sandpile.scenery d σ (Sandpile.siteEnum s i) := by
    intro σ
    rw [linInterp_eq_sum R r (Sandpile.scenery d σ) w hps,
      linInterp_eq_sum R r' (Sandpile.scenery d σ) w' hqs, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmeas : Measurable (fun ξ : Fin s.card → ℝ =>
      ∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
        - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * ξ i) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  simp only [hrep]
  rw [integral_scenery_pick ν hd (Sandpile.siteEnum s) (Sandpile.siteEnum_injective s) _
    hmeas.aestronglyMeasurable]
  exact integral_linear_pi_eq_zero ν hmean hνint _

/-- **The moment hypothesis of the multi-parameter Kolmogorov criterion for the
interpolated rescaled field, with a constant free of the scale.**  The `p`-th
moment of the increment is at most a constant times the `p`-th power of the
distance, with the exponent `p β` for `β = min(1 - d/4, (1-θ)/4)`; taking `p`
large makes `p β` exceed the number `1 + d` of parameters, which is what the
criterion asks. -/
theorem exists_moment_modulus_linInterp
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (p : ℝ) (hp : 2 ≤ p)
    (T S : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 < M ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∫ z, z ∂ν = 0) →
      Integrable (fun z => |z| ^ p) ν →
      ∀ R : ℝ, 1 ≤ R → ∀ (r r' : ℝ) (w w' : Sandpile.Continuum.Space d),
        0 ≤ r → 0 ≤ r' → r ≤ T → r' ≤ T → (∑ i : Fin d, |w i - w' i|) ≤ S →
        ∫ σ, |linInterp d R (Sandpile.scenery d σ) r w
              - linInterp d R (Sandpile.scenery d σ) r' w'| ^ p
            ∂(Sandpile.centeredMassLaw d ν)
          ≤ M * Sandpile.resampleMoment ν p
            * (|r - r'| + ∑ i : Fin d, |w i - w' i|)
              ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := by
  classical
  obtain ⟨C₉, hC₉, hmom⟩ := exists_moment_linInterp_sub_le hd p hp
  obtain ⟨C₁₀, hC₁₀, hmod⟩ :=
    exists_sqrt_tsum_interpCoeff_sub_modulus hHK hd hd3 hθ0 hθ1 T S hT hS
  have hp0 : (0:ℝ) < p := by linarith
  refine ⟨(C₉ * C₁₀) ^ p, Real.rpow_pos_of_pos (by positivity) p, ?_⟩
  intro ν hν hmean hint R hR r r' w w' hr hr' hrT hr'T hws
  haveI := hν
  have hνint : Integrable (fun z : ℝ => z) ν :=
    LatticeProb.integrable_abs_of_rpow ν (by linarith) (fun z => z)
      measurable_id.aestronglyMeasurable hint
  set s : Finset (Site d) := Sandpile.boxFinset (0 : Site d)
    (max (⌈|R| * ‖w‖⌉₊ + 1 + 1 + (⌊R ^ 2 * r⌋₊ + 1))
      (⌈|R| * ‖w'‖⌉₊ + 1 + 1 + (⌊R ^ 2 * r'⌋₊ + 1))) with hsdef
  have hps : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * r⌋₊ + 1) ⊆ s := fun ε =>
    subset_trans (interp_box_subset R ‖w‖ r w le_rfl ε) (boxFinset_zero_mono (le_max_left _ _))
  have hqs : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w' i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * r'⌋₊ + 1) ⊆ s := fun ε =>
    subset_trans (interp_box_subset R ‖w'‖ r' w' le_rfl ε)
      (boxFinset_zero_mono (le_max_right _ _))
  have hzero := integral_linInterp_sub_eq_zero hd ν hmean hνint R r r' w w'
  have h1 := hmom ν hν hint R r r' w w' s hps hqs
  rw [hzero] at h1
  simp only [sub_zero] at h1
  have h2 := hmod R hR r r' w w' hr hr' hrT hr'T hws
  have hm0 : (0:ℝ) ≤ Sandpile.resampleMoment ν p := LatticeProb.pairMoment_nonneg ν p
  have hmr : (0:ℝ) ≤ Sandpile.resampleMoment ν p ^ (1 / p) := Real.rpow_nonneg hm0 _
  have hδ0 : (0:ℝ) ≤ |r - r'| + ∑ i : Fin d, |w i - w' i| := by
    have : (0:ℝ) ≤ ∑ i : Fin d, |w i - w' i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have h := abs_nonneg (r - r')
    linarith
  have hδβ : (0:ℝ) ≤ (|r - r'| + ∑ i : Fin d, |w i - w' i|)
      ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := Real.rpow_nonneg hδ0 _
  have hInt0 : (0:ℝ) ≤ ∫ σ, |linInterp d R (Sandpile.scenery d σ) r w
        - linInterp d R (Sandpile.scenery d σ) r' w'| ^ p
      ∂(Sandpile.centeredMassLaw d ν) :=
    integral_nonneg fun σ => Real.rpow_nonneg (abs_nonneg _) _
  have hchain : (∫ σ, |linInterp d R (Sandpile.scenery d σ) r w
          - linInterp d R (Sandpile.scenery d σ) r' w'| ^ p
        ∂(Sandpile.centeredMassLaw d ν)) ^ (1 / p)
      ≤ C₉ * Sandpile.resampleMoment ν p ^ (1 / p)
        * (C₁₀ * (|r - r'| + ∑ i : Fin d, |w i - w' i|)
          ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := by
    refine le_trans h1 ?_
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hpow := rpow_le_of_rpow_inv_le hp0 hInt0 hchain
  refine le_trans hpow (le_of_eq ?_)
  have hgroup : C₉ * Sandpile.resampleMoment ν p ^ (1 / p)
        * (C₁₀ * (|r - r'| + ∑ i : Fin d, |w i - w' i|)
          ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
      = (C₉ * C₁₀) * (Sandpile.resampleMoment ν p ^ (1 / p)
          * (|r - r'| + ∑ i : Fin d, |w i - w' i|)
            ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := by ring
  have hmid : (Sandpile.resampleMoment ν p ^ (1 / p)) ^ p = Sandpile.resampleMoment ν p := by
    rw [← Real.rpow_mul hm0, one_div_mul_cancel hp0.ne', Real.rpow_one]
  have hdel : ((|r - r'| + ∑ i : Fin d, |w i - w' i|)
        ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) ^ p
      = (|r - r'| + ∑ i : Fin d, |w i - w' i|)
        ^ (p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := by
    rw [← Real.rpow_mul hδ0]
    congr 1
    ring
  rw [hgroup, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hmr hδβ, hmid, hdel, mul_assoc]

/-- **Cauchy-Schwarz for the interpolated field.**  The increment of the field is
the pairing of the increment of its coefficient vector with the scenery on the
finite set the two cells reach. -/
theorem abs_linInterp_sub_le_cauchy (R r r' : ℝ) (ζ : Site d → ℝ)
    (w w' : Sandpile.Continuum.Space d) {s : Finset (Site d)}
    (hps : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r⌋₊ + 1) ⊆ s)
    (hqs : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w' i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r'⌋₊ + 1) ⊆ s) :
    |linInterp d R ζ r w - linInterp d R ζ r' w'|
      ≤ Real.sqrt (∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2)
        * Real.sqrt (∑ z ∈ s, ζ z ^ 2) := by
  classical
  have hrep : linInterp d R ζ r w - linInterp d R ζ r' w'
      = ∑ i : Fin s.card,
          (interpCoeff d R r w (Sandpile.siteEnum s i)
            - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * ζ (Sandpile.siteEnum s i) := by
    rw [linInterp_eq_sum R r ζ w hps, linInterp_eq_sum R r' ζ w' hqs, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin s.card))
    (fun i => interpCoeff d R r w (Sandpile.siteEnum s i)
      - interpCoeff d R r' w' (Sandpile.siteEnum s i))
    (fun i => ζ (Sandpile.siteEnum s i))
  have hc : ∑ i : Fin s.card, (interpCoeff d R r w (Sandpile.siteEnum s i)
        - interpCoeff d R r' w' (Sandpile.siteEnum s i)) ^ 2
      = ∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2 := by
    rw [Sandpile.sum_siteEnum s fun z => (interpCoeff d R r w z - interpCoeff d R r' w' z) ^ 2]
    exact (tsum_coeffDiff_sq R r r' w w' hps hqs).symm
  have hz : ∑ i : Fin s.card, ζ (Sandpile.siteEnum s i) ^ 2 = ∑ z ∈ s, ζ z ^ 2 :=
    Sandpile.sum_siteEnum s fun z => ζ z ^ 2
  have hcn : (0:ℝ) ≤ ∑ i : Fin s.card, (interpCoeff d R r w (Sandpile.siteEnum s i)
      - interpCoeff d R r' w' (Sandpile.siteEnum s i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hrep]
  calc |∑ i : Fin s.card, (interpCoeff d R r w (Sandpile.siteEnum s i)
          - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * ζ (Sandpile.siteEnum s i)|
      = Real.sqrt ((∑ i : Fin s.card, (interpCoeff d R r w (Sandpile.siteEnum s i)
          - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * ζ (Sandpile.siteEnum s i)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i : Fin s.card, (interpCoeff d R r w (Sandpile.siteEnum s i)
          - interpCoeff d R r' w' (Sandpile.siteEnum s i)) ^ 2)
        * ∑ i : Fin s.card, ζ (Sandpile.siteEnum s i) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i : Fin s.card, (interpCoeff d R r w (Sandpile.siteEnum s i)
          - interpCoeff d R r' w' (Sandpile.siteEnum s i)) ^ 2)
        * Real.sqrt (∑ i : Fin s.card, ζ (Sandpile.siteEnum s i) ^ 2) := Real.sqrt_mul hcn _
    _ = Real.sqrt (∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2)
        * Real.sqrt (∑ z ∈ s, ζ z ^ 2) := by rw [hc, hz]

/-- The `ℓ¹` displacement of a point of `ℝ × ℝ^d` is at most `1 + d` times its
distance. -/
theorem sum_abs_sub_le_dist (p q : ℝ × Sandpile.Continuum.Space d) :
    |p.1 - q.1| + ∑ i : Fin d, |p.2 i - q.2 i| ≤ (1 + (d : ℝ)) * dist p q := by
  have htime : |p.1 - q.1| ≤ dist p q := by
    rw [Prod.dist_eq, ← Real.dist_eq]
    exact le_max_left _ _
  have hspace : ∀ i : Fin d, |p.2 i - q.2 i| ≤ dist p q := by
    intro i
    have h1 : |p.2 i - q.2 i| ≤ ‖p.2 - q.2‖ := by
      have := abs_coord_le_norm (p.2 - q.2) i
      simpa using this
    have h2 : ‖p.2 - q.2‖ = dist p.2 q.2 := (dist_eq_norm _ _).symm
    rw [h2] at h1
    exact le_trans h1 (by rw [Prod.dist_eq]; exact le_max_right _ _)
  have hsum : ∑ i : Fin d, |p.2 i - q.2 i| ≤ (d : ℝ) * dist p q := by
    calc ∑ i : Fin d, |p.2 i - q.2 i| ≤ ∑ _i : Fin d, dist p q :=
          Finset.sum_le_sum fun i _ => hspace i
      _ = (d : ℝ) * dist p q := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith [htime, hsum]

/-- **The interpolated field is continuous on every box of nonnegative times and
bounded space, for every sample of the scenery.**  This is the path continuity the
quantitative Kolmogorov criterion asks of the process it is applied to.  It needs
no bound on the mesh values: the field is the pairing of its coefficient vector
with the scenery on the finite set the box reaches, and the coefficient vector is
Hölder in the point. -/
theorem continuousOn_linInterp_box
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (R : ℝ) (hR : 1 ≤ R) (ζ : Site d → ℝ) (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L) :
    ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => linInterp d R ζ p.1 p.2)
      (Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Sandpile.Continuum.Space d) L) := by
  classical
  obtain ⟨C, hC, hmod⟩ := exists_sqrt_tsum_interpCoeff_sub_modulus hHK hd hd3 hθ0 hθ1
    T (2 * (d : ℝ) * L) hT (by positivity)
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  set n : ℕ := ⌈|R| * L⌉₊ + 1 + 1 + (⌊R ^ 2 * T⌋₊ + 1) with hn
  set s : Finset (Site d) := Sandpile.boxFinset (0 : Site d) n with hsdef
  set β : ℝ := min (1 - (d : ℝ) / 4) ((1 - θ) / 4) with hβ
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hβ0 : (0:ℝ) < β := lt_min (by linarith) (by linarith)
  -- the membership facts
  have hmem : ∀ p ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Sandpile.Continuum.Space d) L,
      (0 ≤ p.1 ∧ p.1 ≤ T) ∧ ‖p.2‖ ≤ L := by
    intro p hp
    refine ⟨⟨(Set.mem_Icc.mp (Set.mem_prod.mp hp).1).1, (Set.mem_Icc.mp (Set.mem_prod.mp hp).1).2⟩,
      ?_⟩
    have := (Set.mem_prod.mp hp).2
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this
  have hbox : ∀ p ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Sandpile.Continuum.Space d) L,
      ∀ ε : Fin d → Bool,
        Sandpile.boxFinset (fun i => ⌊R * p.2 i⌋ + if ε i then 1 else 0)
          (⌊R ^ 2 * p.1⌋₊ + 1) ⊆ s := by
    intro p hp ε
    obtain ⟨⟨hp0, hpT⟩, hpL⟩ := hmem p hp
    refine subset_trans (interp_box_subset R L p.1 p.2 hpL ε) (boxFinset_zero_mono ?_)
    have : ⌊R ^ 2 * p.1⌋₊ ≤ ⌊R ^ 2 * T⌋₊ :=
      Nat.floor_le_floor (mul_le_mul_of_nonneg_left hpT (sq_nonneg R))
    omega
  have hws : ∀ p ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Sandpile.Continuum.Space d) L,
      ∀ q ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Sandpile.Continuum.Space d) L,
      (∑ i : Fin d, |p.2 i - q.2 i|) ≤ 2 * (d : ℝ) * L := by
    intro p hp q hq
    obtain ⟨_, hpL⟩ := hmem p hp
    obtain ⟨_, hqL⟩ := hmem q hq
    calc ∑ i : Fin d, |p.2 i - q.2 i| ≤ ∑ _i : Fin d, (2 * L) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : |p.2 i| ≤ L := le_trans (abs_coord_le_norm p.2 i) hpL
          have h2 : |q.2 i| ≤ L := le_trans (abs_coord_le_norm q.2 i) hqL
          calc |p.2 i - q.2 i| ≤ |p.2 i| + |q.2 i| := abs_sub _ _
            _ ≤ 2 * L := by linarith
      _ = 2 * (d : ℝ) * L := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- the Hölder bound on the box
  set A : ℝ := C * Real.sqrt (∑ z ∈ s, ζ z ^ 2) with hA
  have hA0 : (0:ℝ) ≤ A := by positivity
  have hholder : ∀ p ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Sandpile.Continuum.Space d) L,
      ∀ q ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Sandpile.Continuum.Space d) L,
      |linInterp d R ζ p.1 p.2 - linInterp d R ζ q.1 q.2|
        ≤ A * ((1 + (d : ℝ)) * dist p q) ^ β := by
    intro p hp q hq
    obtain ⟨⟨hp0, hpT⟩, _⟩ := hmem p hp
    obtain ⟨⟨hq0, hqT⟩, _⟩ := hmem q hq
    have hcs := abs_linInterp_sub_le_cauchy R p.1 q.1 ζ p.2 q.2 (hbox p hp) (hbox q hq)
    have hmd := hmod R hR p.1 q.1 p.2 q.2 hp0 hq0 hpT hqT (hws p hp q hq)
    have hδ0 : (0:ℝ) ≤ |p.1 - q.1| + ∑ i : Fin d, |p.2 i - q.2 i| := by
      have h1 : (0:ℝ) ≤ ∑ i : Fin d, |p.2 i - q.2 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      have h2 := abs_nonneg (p.1 - q.1)
      linarith
    have hmono : (|p.1 - q.1| + ∑ i : Fin d, |p.2 i - q.2 i|) ^ β
        ≤ ((1 + (d : ℝ)) * dist p q) ^ β :=
      Real.rpow_le_rpow hδ0 (sum_abs_sub_le_dist p q) hβ0.le
    have hζ0 : (0:ℝ) ≤ Real.sqrt (∑ z ∈ s, ζ z ^ 2) := Real.sqrt_nonneg _
    calc |linInterp d R ζ p.1 p.2 - linInterp d R ζ q.1 q.2|
        ≤ Real.sqrt (∑' y : Site d,
            (interpCoeff d R p.1 p.2 y - interpCoeff d R q.1 q.2 y) ^ 2)
          * Real.sqrt (∑ z ∈ s, ζ z ^ 2) := hcs
      _ ≤ C * (|p.1 - q.1| + ∑ i : Fin d, |p.2 i - q.2 i|) ^ β
          * Real.sqrt (∑ z ∈ s, ζ z ^ 2) := mul_le_mul_of_nonneg_right hmd hζ0
      _ ≤ C * ((1 + (d : ℝ)) * dist p q) ^ β * Real.sqrt (∑ z ∈ s, ζ z ^ 2) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hC.le) hζ0
      _ = A * ((1 + (d : ℝ)) * dist p q) ^ β := by rw [hA]; ring
  -- continuity from the Hölder bound
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  set B : ℝ := A * (1 + (d : ℝ)) ^ β with hB
  have hB0 : (0:ℝ) ≤ B := by positivity
  refine ⟨(ε / (B + 1)) ^ (1 / β), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro a ha hab
  have hd0 : (0:ℝ) ≤ dist a b := dist_nonneg
  have hkey : (dist a b) ^ β < ε / (B + 1) := by
    have h1 : (dist a b) ^ β < ((ε / (B + 1)) ^ (1 / β)) ^ β := Real.rpow_lt_rpow hd0 hab hβ0
    have h2 : ((ε / (B + 1)) ^ (1 / β)) ^ β = ε / (B + 1) := by
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ0.ne', Real.rpow_one]
    rwa [h2] at h1
  have hsplit : ((1 + (d : ℝ)) * dist a b) ^ β = (1 + (d : ℝ)) ^ β * (dist a b) ^ β :=
    Real.mul_rpow (by positivity) hd0
  have hfin : A * ((1 + (d : ℝ)) * dist a b) ^ β < ε := by
    rw [hsplit]
    have hBd : A * ((1 + (d : ℝ)) ^ β * (dist a b) ^ β) = B * (dist a b) ^ β := by
      rw [hB]; ring
    rw [← mul_assoc] at hBd ⊢
    rw [hBd]
    have h3 : B * (dist a b) ^ β ≤ B * (ε / (B + 1)) :=
      mul_le_mul_of_nonneg_left hkey.le hB0
    have h4 : B * (ε / (B + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith : (0:ℝ) < B + 1)]
      nlinarith [hε, hB0]
    linarith
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hholder a ha b hb) hfin

/-- **The `p`-th moment of the interpolated rescaled field at one point.**  The
one-point form of `exists_moment_linInterp_sub_le`. -/
theorem exists_moment_linInterp_le (hd : 1 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      Integrable (fun z => |z| ^ p) ν →
      ∀ (R r : ℝ) (w : Sandpile.Continuum.Space d) (s : Finset (Site d)),
        (∀ ε : Fin d → Bool,
          Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0)
            (⌊R ^ 2 * r⌋₊ + 1) ⊆ s) →
        (∫ σ, |linInterp d R (Sandpile.scenery d σ) r w
              - ∫ τ, linInterp d R (Sandpile.scenery d τ) r w
                ∂(Sandpile.centeredMassLaw d ν)| ^ p ∂(Sandpile.centeredMassLaw d ν)) ^ (1 / p)
          ≤ C * Sandpile.resampleMoment ν p ^ (1 / p)
            * Real.sqrt (∑' y : Site d, interpCoeff d R r w y ^ 2) := by
  classical
  obtain ⟨C, hC, hmom⟩ := exists_moment_linear_pi p hp
  refine ⟨C, hC, ?_⟩
  intro ν hν hint R r w s hps
  haveI := hν
  have hrep : ∀ σ : Site d → ℝ,
      linInterp d R (Sandpile.scenery d σ) r w
        = ∑ i : Fin s.card,
            interpCoeff d R r w (Sandpile.siteEnum s i)
              * Sandpile.scenery d σ (Sandpile.siteEnum s i) :=
    fun σ => linInterp_eq_sum R r (Sandpile.scenery d σ) w hps
  have hmeas : Measurable (fun ξ : Fin s.card → ℝ =>
      ∑ i, interpCoeff d R r w (Sandpile.siteEnum s i) * ξ i) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hmean : (∫ τ, linInterp d R (Sandpile.scenery d τ) r w
        ∂(Sandpile.centeredMassLaw d ν))
      = ∫ η, (∑ i, interpCoeff d R r w (Sandpile.siteEnum s i) * η i)
          ∂(Measure.pi fun _ : Fin s.card => ν) := by
    simp only [hrep]
    exact integral_scenery_pick ν hd (Sandpile.siteEnum s) (Sandpile.siteEnum_injective s) _
      hmeas.aestronglyMeasurable
  have hmeas2 : Measurable (fun ξ : Fin s.card → ℝ =>
      |(∑ i, interpCoeff d R r w (Sandpile.siteEnum s i) * ξ i)
        - ∫ η, (∑ i, interpCoeff d R r w (Sandpile.siteEnum s i) * η i)
            ∂(Measure.pi fun _ : Fin s.card => ν)| ^ p) :=
    ((hmeas.sub measurable_const).abs).pow_const p
  have hlhs : (∫ σ, |linInterp d R (Sandpile.scenery d σ) r w
              - ∫ τ, linInterp d R (Sandpile.scenery d τ) r w
                ∂(Sandpile.centeredMassLaw d ν)| ^ p ∂(Sandpile.centeredMassLaw d ν))
      = ∫ ξ, |(∑ i, interpCoeff d R r w (Sandpile.siteEnum s i) * ξ i)
          - ∫ η, (∑ i, interpCoeff d R r w (Sandpile.siteEnum s i) * η i)
              ∂(Measure.pi fun _ : Fin s.card => ν)| ^ p
          ∂(Measure.pi fun _ : Fin s.card => ν) := by
    rw [hmean]
    simp only [hrep]
    exact integral_scenery_pick ν hd (Sandpile.siteEnum s) (Sandpile.siteEnum_injective s) _
      hmeas2.aestronglyMeasurable
  have hsum : ∑ i : Fin s.card, interpCoeff d R r w (Sandpile.siteEnum s i) ^ 2
      = ∑' y : Site d, interpCoeff d R r w y ^ 2 := by
    rw [Sandpile.sum_siteEnum s fun z => interpCoeff d R r w z ^ 2]
    exact (tsum_interpCoeff_sq R r w hps).symm
  rw [hlhs, ← hsum]
  exact hmom s.card ν hν hint _

/-- **The interpolated field at one point has mean zero.** -/
theorem integral_linInterp_eq_zero (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hνint : Integrable (fun z : ℝ => z) ν)
    (R r : ℝ) (w : Sandpile.Continuum.Space d) :
    ∫ τ, linInterp d R (Sandpile.scenery d τ) r w ∂(Sandpile.centeredMassLaw d ν) = 0 := by
  classical
  set s : Finset (Site d) := Sandpile.boxFinset (0 : Site d)
    (⌈|R| * ‖w‖⌉₊ + 1 + 1 + (⌊R ^ 2 * r⌋₊ + 1)) with hsdef
  have hps : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * r⌋₊ + 1) ⊆ s := fun ε => interp_box_subset R ‖w‖ r w le_rfl ε
  have hrep : ∀ σ : Site d → ℝ,
      linInterp d R (Sandpile.scenery d σ) r w
        = ∑ i : Fin s.card,
            interpCoeff d R r w (Sandpile.siteEnum s i)
              * Sandpile.scenery d σ (Sandpile.siteEnum s i) :=
    fun σ => linInterp_eq_sum R r (Sandpile.scenery d σ) w hps
  have hmeas : Measurable (fun ξ : Fin s.card → ℝ =>
      ∑ i, interpCoeff d R r w (Sandpile.siteEnum s i) * ξ i) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  simp only [hrep]
  rw [integral_scenery_pick ν hd (Sandpile.siteEnum s) (Sandpile.siteEnum_injective s) _
    hmeas.aestronglyMeasurable]
  exact integral_linear_pi_eq_zero ν hmean hνint _

/-- **The `ℓ²` norm of the coefficient vector at one point, with a bound free of
the scale.** -/
theorem exists_sqrt_tsum_interpCoeff_sq_le_uniform
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ (r : ℝ) (w : Sandpile.Continuum.Space d),
      0 ≤ r → r ≤ T → Real.sqrt (∑' y : Site d, interpCoeff d R r w y ^ 2) ≤ C := by
  obtain ⟨C, hC, hγ⟩ := exists_sqrt_tsum_interpCoeff_sq_le hHK hd hd3
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have he : (0:ℝ) ≤ 2 - (d : ℝ) / 2 := by linarith
  refine ⟨Real.sqrt (C * (2 + T) ^ (2 - (d : ℝ) / 2)), by positivity, ?_⟩
  intro R hR r w hr hrT
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hR2 : (1:ℝ) ≤ R ^ 2 := by nlinarith
  have hbase : (2:ℝ) + R ^ 2 * T ≤ (2 + T) * R ^ 2 := by nlinarith
  have h1 : (2 + R ^ 2 * T) ^ (2 - (d : ℝ) / 2) ≤ ((2 + T) * R ^ 2) ^ (2 - (d : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) hbase he
  have h2 : ((2 + T) * R ^ 2) ^ (2 - (d : ℝ) / 2)
      = (2 + T) ^ (2 - (d : ℝ) / 2) * R ^ (2 * (2 - (d : ℝ) / 2)) := by
    rw [Real.mul_rpow (by linarith) (by positivity), LatticeProb.rpow_sq_eq hR0.le]
  have h3 : Real.sqrt (C * ((2 + T) ^ (2 - (d : ℝ) / 2) * R ^ (2 * (2 - (d : ℝ) / 2))))
      = Real.sqrt (C * (2 + T) ^ (2 - (d : ℝ) / 2)) * R ^ (2 - (d : ℝ) / 2) := by
    rw [← mul_assoc, Real.sqrt_mul (by positivity), LatticeProb.sqrt_rpow_eq hR0.le]
    congr 2
    ring
  have hstep : Real.sqrt (C * (2 + R ^ 2 * T) ^ (2 - (d : ℝ) / 2))
      ≤ Real.sqrt (C * (2 + T) ^ (2 - (d : ℝ) / 2)) * R ^ (2 - (d : ℝ) / 2) := by
    rw [← h3]
    refine Real.sqrt_le_sqrt ?_
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 hC.le
  have habs : |R ^ ((d : ℝ) / 2 - 2)| = R ^ ((d : ℝ) / 2 - 2) :=
    abs_of_nonneg (Real.rpow_nonneg hR0.le _)
  have hprod : R ^ ((d : ℝ) / 2 - 2) * R ^ (2 - (d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hR0, show (d : ℝ) / 2 - 2 + (2 - (d : ℝ) / 2) = 0 by ring,
      Real.rpow_zero]
  have hkey := hγ R T r w hr hrT
  rw [habs] at hkey
  refine le_trans hkey ?_
  calc R ^ ((d : ℝ) / 2 - 2) * Real.sqrt (C * (2 + R ^ 2 * T) ^ (2 - (d : ℝ) / 2))
      ≤ R ^ ((d : ℝ) / 2 - 2)
        * (Real.sqrt (C * (2 + T) ^ (2 - (d : ℝ) / 2)) * R ^ (2 - (d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hR0.le _)
    _ = (R ^ ((d : ℝ) / 2 - 2) * R ^ (2 - (d : ℝ) / 2))
        * Real.sqrt (C * (2 + T) ^ (2 - (d : ℝ) / 2)) := by ring
    _ = Real.sqrt (C * (2 + T) ^ (2 - (d : ℝ) / 2)) := by rw [hprod, one_mul]

/-- **The one-point moment bound of the criterion's uniform-norm clause, with a
constant free of the scale.** -/
theorem exists_one_point_moment_linInterp
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (p : ℝ) (hp : 2 ≤ p) (T : ℝ) (hT : 0 ≤ T) :
    ∃ M : ℝ, 0 < M ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∫ z, z ∂ν = 0) →
      Integrable (fun z => |z| ^ p) ν →
      ∀ R : ℝ, 1 ≤ R → ∀ (r : ℝ) (w : Sandpile.Continuum.Space d), 0 ≤ r → r ≤ T →
        ∫ σ, |linInterp d R (Sandpile.scenery d σ) r w| ^ p
            ∂(Sandpile.centeredMassLaw d ν)
          ≤ M * Sandpile.resampleMoment ν p := by
  classical
  obtain ⟨C₉, hC₉, hmom⟩ := exists_moment_linInterp_le hd p hp
  obtain ⟨Cγ, hCγ, hgam⟩ := exists_sqrt_tsum_interpCoeff_sq_le_uniform hHK hd hd3 T hT
  have hp0 : (0:ℝ) < p := by linarith
  refine ⟨(C₉ * Cγ) ^ p, Real.rpow_pos_of_pos (by positivity) p, ?_⟩
  intro ν hν hmean hint R hR r w hr hrT
  haveI := hν
  have hνint : Integrable (fun z : ℝ => z) ν :=
    LatticeProb.integrable_abs_of_rpow ν (by linarith) (fun z => z)
      measurable_id.aestronglyMeasurable hint
  set s : Finset (Site d) := Sandpile.boxFinset (0 : Site d)
    (⌈|R| * ‖w‖⌉₊ + 1 + 1 + (⌊R ^ 2 * r⌋₊ + 1)) with hsdef
  have hps : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * r⌋₊ + 1) ⊆ s := fun ε => interp_box_subset R ‖w‖ r w le_rfl ε
  have hzero := integral_linInterp_eq_zero hd ν hmean hνint R r w
  have h1 := hmom ν hν hint R r w s hps
  rw [hzero] at h1
  simp only [sub_zero] at h1
  have h2 := hgam R hR r w hr hrT
  have hm0 : (0:ℝ) ≤ Sandpile.resampleMoment ν p := LatticeProb.pairMoment_nonneg ν p
  have hmr : (0:ℝ) ≤ Sandpile.resampleMoment ν p ^ (1 / p) := Real.rpow_nonneg hm0 _
  have hInt0 : (0:ℝ) ≤ ∫ σ, |linInterp d R (Sandpile.scenery d σ) r w| ^ p
      ∂(Sandpile.centeredMassLaw d ν) :=
    integral_nonneg fun σ => Real.rpow_nonneg (abs_nonneg _) _
  have hchain : (∫ σ, |linInterp d R (Sandpile.scenery d σ) r w| ^ p
        ∂(Sandpile.centeredMassLaw d ν)) ^ (1 / p)
      ≤ C₉ * Sandpile.resampleMoment ν p ^ (1 / p) * Cγ := by
    refine le_trans h1 ?_
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hpow := rpow_le_of_rpow_inv_le hp0 hInt0 hchain
  refine le_trans hpow (le_of_eq ?_)
  have hgroup : C₉ * Sandpile.resampleMoment ν p ^ (1 / p) * Cγ
      = (C₉ * Cγ) * Sandpile.resampleMoment ν p ^ (1 / p) := by ring
  have hmid : (Sandpile.resampleMoment ν p ^ (1 / p)) ^ p = Sandpile.resampleMoment ν p := by
    rw [← Real.rpow_mul hm0, one_div_mul_cancel hp0.ne', Real.rpow_one]
  rw [hgroup, Real.mul_rpow (by positivity) hmr, hmid]

end Sandpile.Support
