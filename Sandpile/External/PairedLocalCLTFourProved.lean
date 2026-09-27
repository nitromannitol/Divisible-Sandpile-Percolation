import Sandpile.External.PairedLocalCLTFour
import Sandpile.External.LocalCLTProved
import Sandpile.External.GaussianFourierProved
import Sandpile.Support.TightKernel

open MeasureTheory

noncomputable section

def aux_paired_gaussRegion : Set (Fin 4 → ℝ) :=
  {θ | ∀ i, |θ i| ≤ Real.pi / 4}

def aux_paired_character (z : Fin 4 → ℤ) : (Fin 4 → ℝ) → ℂ :=
  fun θ => ∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)

def aux_paired_fourierIntegrand (l : ℕ) (z : Fin 4 → ℤ) : (Fin 4 → ℝ) → ℂ :=
  fun θ =>
    aux_paired_character z θ *
      (((∑ i : Fin 4, Real.cos (θ i)) / 4 : ℝ) ^ l : ℂ)

def aux_paired_gaussianIntegrand (l : ℕ) (z : Fin 4 → ℤ) : (Fin 4 → ℝ) → ℂ :=
  fun θ =>
    (Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 8) : ℂ) * aux_paired_character z θ

theorem aux_paired_exp_neg_le_inv_cube {u : ℝ} (hu : 0 < u) :
    Real.exp (-u) ≤ 27 / u ^ 3 := by
  have hlin : u ≤ 3 * Real.exp (u / 3) := by
    have h := Real.add_one_le_exp (u / 3)
    nlinarith
  have hcube : u ^ 3 ≤ 27 * Real.exp u := by
    calc
      u ^ 3 ≤ (3 * Real.exp (u / 3)) ^ 3 := by
        exact pow_le_pow_left₀ (le_of_lt hu) hlin 3
      _ = 27 * Real.exp u := by
        calc
          (3 * Real.exp (u / 3)) ^ 3 = 27 * (Real.exp (u / 3)) ^ 3 := by ring_nf
          _ = 27 * Real.exp u := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring_nf
  have hm := mul_le_mul_of_nonneg_right hcube (Real.exp_nonneg (-u))
  have hexp : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_assoc, hexp, mul_one] at hm
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < u ^ 3)).2
  simpa [mul_comm] using hm

theorem aux_paired_fourier_integrand_norm (l : ℕ) (z : Fin 4 → ℤ)
    (θ : Fin 4 → ℝ) :
    ‖aux_paired_fourierIntegrand l z θ‖ = |LatticeProb.charFn 4 θ| ^ l := by
  dsimp [aux_paired_fourierIntegrand, aux_paired_character]
  rw [norm_mul, norm_prod]
  simp only [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem aux_paired_character_norm (z : Fin 4 → ℤ) (θ : Fin 4 → ℝ) :
    ‖aux_paired_character z θ‖ = 1 := by
  dsimp [aux_paired_character]
  rw [norm_prod]
  simp [Complex.norm_exp]

theorem aux_paired_fourier_integrable (l : ℕ) (z : Fin 4 → ℤ) :
    IntegrableOn (aux_paired_fourierIntegrand l z)
      (LatticeProb.LocalCLT.torusBox 4) volume := by
  change Integrable (aux_paired_fourierIntegrand l z)
    (volume.restrict (LatticeProb.LocalCLT.torusBox 4))
  have h := LatticeProb.LocalCLT.fourier_integrand_integrable 4 l z
  refine h.congr ?_
  filter_upwards with θ
  dsimp [aux_paired_fourierIntegrand, aux_paired_character]
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  push_cast
  rfl

theorem aux_paired_gaussian_integrable {l : ℕ} (hl : 0 < l) (z : Fin 4 → ℤ) :
    Integrable (aux_paired_gaussianIntegrand l z) := by
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  have hbase : Integrable (fun θ : Fin 4 → ℝ =>
      (Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 8) : ℂ)) := by
    have h := aux_lclt_full_gaussian_integrable (d := 4) ((l : ℝ) / 8) (by positivity)
    exact h.ofReal.congr (Filter.Eventually.of_forall (fun θ => by
      ring_nf
      rfl))
  have hchar : AEStronglyMeasurable (aux_paired_character z) := by
    apply Measurable.aestronglyMeasurable
    change Measurable (fun θ : Fin 4 → ℝ =>
      ∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
    measurability
  have hb : ∀ᵐ θ : Fin 4 → ℝ, ‖aux_paired_character z θ‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall (fun θ => by
      rw [aux_paired_character_norm z θ])
  change Integrable (fun θ : Fin 4 → ℝ =>
    (Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 8) : ℂ) *
      aux_paired_character z θ)
  exact hbase.mul_bdd hchar hb

theorem aux_paired_core_error {l : ℕ} (hl : 2 ≤ l) (z : Fin 4 → ℤ) :
    ‖∫ θ in aux_paired_gaussRegion,
        aux_paired_fourierIntegrand l z θ - aux_paired_gaussianIntegrand l z θ‖ ≤
      9216 / (l : ℝ) * (Real.pi / ((l : ℝ) / 192)) ^ 2 := by
  let G := aux_paired_gaussRegion
  let f := aux_paired_fourierIntegrand l z
  let g := aux_paired_gaussianIntegrand l z
  have hG : MeasurableSet G := by
    dsimp [G, aux_paired_gaussRegion]
    change MeasurableSet {θ : Fin 4 → ℝ | ∀ i, |θ i| ≤ Real.pi / 4}
    measurability
  have hnorm :
      ‖∫ θ in G, f θ - g θ‖ ≤ ∫ θ in G, ‖f θ - g θ‖ := by
    exact norm_integral_le_integral_norm (fun θ => f θ - g θ)
  have hpoint : ∀ θ ∈ G, ‖f θ - g θ‖ ≤
      (l : ℝ) *
          ((∑ i : Fin 4, θ i ^ 2) ^ 2 / (24 * 4) +
            ((∑ i : Fin 4, θ i ^ 2) / (2 * 4)) ^ 2) *
        Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / (16 * 4)) := by
    intro θ hθ
    have htheta : ∀ i : Fin 4, |θ i| ≤ Real.pi / 2 := by
      intro i
      have hi := hθ i
      exact hi.trans (by linarith [Real.pi_pos])
    have hS : (∑ i : Fin 4, θ i ^ 2) ≤ (4 : ℝ) := by
      have hcoord : ∀ i : Fin 4, θ i ^ 2 ≤ (Real.pi / 4) ^ 2 := by
        intro i
        have hp : 0 ≤ Real.pi / 4 := by positivity
        have habs : |θ i| ≤ |Real.pi / 4| := by
          simpa [abs_of_nonneg hp] using hθ i
        exact sq_le_sq.mpr habs
      calc
        ∑ i : Fin 4, θ i ^ 2 ≤ ∑ _i : Fin 4, (Real.pi / 4) ^ 2 :=
          Finset.sum_le_sum fun i _ => hcoord i
        _ = 4 * (Real.pi / 4) ^ 2 := by simp
        _ ≤ 4 := by
          have hpi : Real.pi ≤ 4 := Real.pi_le_four
          have hp0 : 0 ≤ Real.pi := Real.pi_pos.le
          have hprod : 0 ≤ (4 - Real.pi) * (4 + Real.pi) :=
            mul_nonneg (sub_nonneg.mpr hpi) (by linarith)
          nlinarith
    have hc := aux_lclt_gaussian_power_comparison (d := 4) (n := l) (by omega) hl θ
      htheta hS
    have heq : f θ - g θ = aux_paired_character z θ *
        (((LatticeProb.charFn 4 θ) ^ l : ℂ) -
          (Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 8) : ℂ)) := by
      dsimp [f, g, aux_paired_fourierIntegrand, aux_paired_gaussianIntegrand,
        aux_paired_character]
      simp only [LatticeProb.charFn]
      rw [Complex.ofReal_div]
      norm_num
      ring1
    rw [heq, norm_mul, aux_paired_character_norm]
    convert hc using 1 <;> norm_num
  have hpoint' : ∀ θ ∈ G, ‖f θ - g θ‖ ≤
      9216 / (l : ℝ) * Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) := by
    intro θ hθ
    have h := hpoint θ hθ
    have hS0 : 0 ≤ ∑ i : Fin 4, θ i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hq := aux_lclt_comparison_pointwise (d := 4) (n := l) (by norm_num)
      (by omega) (∑ i : Fin 4, θ i ^ 2) hS0
    have hq' :
        (l : ℝ) *
            ((∑ i : Fin 4, θ i ^ 2) ^ 2 / (24 * 4) +
              ((∑ i : Fin 4, θ i ^ 2) / (2 * 4)) ^ 2) *
          Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / (16 * 4)) ≤
        9216 / (l : ℝ) * Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) := by
      calc
        _ ≤ 2304 * (4 : ℝ) / (l : ℝ) *
            Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / (48 * 4)) := by
          simpa using hq
        _ = 9216 / (l : ℝ) *
            Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) := by
          congr 2 <;> ring_nf
    exact h.trans hq'
  have hl0 : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hgi : Integrable (fun θ : Fin 4 → ℝ =>
      Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192)) := by
    have h := aux_lclt_full_gaussian_integrable (d := 4) ((l : ℝ) / 192) (by positivity)
    refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
    ring_nf
  have hset : ∫ θ in G, Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) ≤
      ∫ θ : Fin 4 → ℝ, Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) := by
    apply setIntegral_le_integral hgi
    filter_upwards with θ
    positivity
  have hconst : ∫ θ in G, 9216 / (l : ℝ) *
      Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) =
      9216 / (l : ℝ) * ∫ θ in G,
        Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) := by
    rw [integral_const_mul]
  have hfiG : IntegrableOn f G volume := by
    apply (aux_paired_fourier_integrable l z).mono_set
    intro θ hθ
    change ∀ i, |θ i| ≤ Real.pi / 4 at hθ
    simp only [LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    exact ⟨fun i => by linarith [(abs_le.mp (hθ i)).1, Real.pi_pos],
      fun i => by linarith [(abs_le.mp (hθ i)).2, Real.pi_pos]⟩
  have hgiG : IntegrableOn g G volume := by
    simpa [g] using (aux_paired_gaussian_integrable (l := l) (by omega) z).integrableOn.mono_set
      (Set.subset_univ G)
  have hdiff : IntegrableOn (fun θ => ‖f θ - g θ‖) G volume :=
    (hfiG.sub hgiG).norm
  have hbound : IntegrableOn (fun θ : Fin 4 → ℝ =>
      9216 / (l : ℝ) * Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192)) G volume :=
    (hgi.const_mul _).integrableOn
  calc
    ‖∫ θ in G, f θ - g θ‖ ≤ ∫ θ in G, ‖f θ - g θ‖ := hnorm
    _ ≤ ∫ θ in G, 9216 / (l : ℝ) *
          Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) := by
      exact setIntegral_mono_on hdiff hbound hG hpoint'
    _ = 9216 / (l : ℝ) * ∫ θ in G,
          Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) := hconst
    _ ≤ 9216 / (l : ℝ) * ∫ θ : Fin 4 → ℝ,
          Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) := by
      gcongr
    _ = 9216 / (l : ℝ) * (Real.pi / ((l : ℝ) / 192)) ^ 2 := by
      have hfull := aux_lclt_full_gaussian (d := 4) ((l : ℝ) / 192) (by positivity)
      have hfull' : ∫ θ : Fin 4 → ℝ,
          Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 192) =
          (Real.pi / ((l : ℝ) / 192)) ^ 2 := by
        calc
          _ = ∫ θ : Fin 4 → ℝ,
              Real.exp (-((l : ℝ) / 192) * (∑ i : Fin 4, θ i ^ 2)) := by
            apply integral_congr_ae
            filter_upwards with θ
            congr 1
            ring_nf
          _ = (Real.pi / ((l : ℝ) / 192)) ^ ((4 : ℝ) / 2) := hfull
          _ = (Real.pi / ((l : ℝ) / 192)) ^ 2 := by norm_num
      rw [hfull']

theorem aux_paired_bool_corner_union {d : ℕ} {η : ℝ}
    (hη0 : 0 < η) (_hηp : η ≤ Real.pi / 2) :
    (⋃ b : Fin d → Bool, {u : Fin d → ℝ |
      ∀ i, if b i then u i ∈ Set.Ioo (Real.pi - η) Real.pi
        else u i ∈ Set.Icc Real.pi (Real.pi + η)}) =
      {u : Fin d → ℝ | ∀ i, u i ∈ Set.Ioc (Real.pi - η) (Real.pi + η)} := by
  classical
  ext u
  constructor
  · intro hu i
    rcases Set.mem_iUnion.mp hu with ⟨b, hb⟩
    by_cases hbi : b i
    · have hi := hb i
      simp only [hbi, ↓reduceIte] at hi
      exact ⟨hi.1, le_trans (le_of_lt hi.2) (by linarith [hη0])⟩
    · have hi := hb i
      simp only [hbi] at hi
      exact ⟨by linarith [hi.1], hi.2⟩
  · intro hu
    let b : Fin d → Bool := fun i => decide (u i < Real.pi)
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    intro i
    by_cases hi : u i < Real.pi
    · simp only [b, hi, decide_true]
      exact ⟨hu i |>.1, hi⟩
    · simp only [b, hi, decide_false]
      exact ⟨le_of_not_gt hi, hu i |>.2⟩

theorem aux_paired_bool_corner_union_ae {d : ℕ} {η : ℝ} :
    {u : Fin d → ℝ | ∀ i, u i ∈ Set.Ioc (Real.pi - η) (Real.pi + η)} =ᵐ[volume]
      {u : Fin d → ℝ | ∀ i, |u i - Real.pi| ≤ η} := by
  have h := Measure.univ_pi_Ioc_ae_eq_Icc
    (μ := fun _ : Fin d => (volume : Measure ℝ))
    (f := fun _ => Real.pi - η) (g := fun _ => Real.pi + η)
  rw [← volume_pi] at h
  convert h using 1
  · apply Set.ext
    intro u
    change (∀ i, u i ∈ Set.Ioc (Real.pi - η) (Real.pi + η)) ↔
      (∀ i ∈ Set.univ, u i ∈ Set.Ioc (Real.pi - η) (Real.pi + η))
    simp
  · apply Set.ext
    intro u
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    constructor
    · intro hu
      constructor <;> intro i
      · have hi := abs_le.mp (hu i)
        linarith
      · have hi := abs_le.mp (hu i)
        linarith
    · intro hu i
      exact abs_le.mpr ⟨by linarith [hu.1 i], by linarith [hu.2 i]⟩

theorem aux_paired_antipode_corner_assembly {d n : ℕ} (η : ℝ)
    (hη0 : 0 < η) (hηp : η ≤ Real.pi / 2) (z : LatticeProb.Site d) :
    let f : (Fin d → ℝ) → ℂ := fun θ =>
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
    let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
      {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
        else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
    ∑ b, ∫ θ in C b, f θ =
      ∫ θ in {θ : Fin d → ℝ | ∀ i, |θ i - Real.pi| ≤ η}, f θ := by
  classical
  dsimp
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
      (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
    {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
  let Q : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
    {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc Real.pi (Real.pi + η)}
  let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
  let B : Set (Fin d → ℝ) := {θ : Fin d → ℝ | ∀ i, |θ i - Real.pi| ≤ η}
  have hT : MeasurableSet T := LatticeProb.LocalCLT.torusBox_measurable d
  have hfiT : IntegrableOn f T volume := by
    simpa [IntegrableOn, f, T, Complex.ofReal_pow, Complex.ofReal_div] using
      LatticeProb.LocalCLT.fourier_integrand_integrable d n z
  have hfcont : Continuous f := by fun_prop
  have hCmeas : ∀ b, MeasurableSet (C b) := by
    intro b
    dsimp [C]
    measurability
  have hQmeas : ∀ b, MeasurableSet (Q b) := by
    intro b
    dsimp [Q]
    measurability
  have hCsub : ∀ b, C b ⊆ T := by
    intro b θ hθ
    simp only [T, LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    constructor
    · intro i
      by_cases hbi : b i
      · have hi := hθ i
        simp only [hbi, ↓reduceIte] at hi
        linarith [hi.1, Real.pi_pos]
      · have hi := hθ i
        simp only [hbi] at hi
        exact hi.1
    · intro i
      by_cases hbi : b i
      · have hi := hθ i
        simp only [hbi, ↓reduceIte] at hi
        exact le_of_lt hi.2
      · have hi := hθ i
        simp only [hbi] at hi
        linarith [hi.2, Real.pi_pos]
  have hfiC : ∀ b, IntegrableOn f (C b) volume := fun b =>
    hfiT.mono_set (hCsub b)
  have hfiB : IntegrableOn f B volume := by
    have hBcompact : IsCompact B := by
      have hcomp := isCompact_pi_infinite (fun _ : Fin d =>
        (isCompact_Icc : IsCompact (Set.Icc (Real.pi - η) (Real.pi + η))))
      convert hcomp using 1
      ext θ
      simp only [B, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · intro hθ i
        have hi := abs_le.mp (hθ i)
        exact ⟨by linarith, by linarith⟩
      · intro hθ i
        exact abs_le.mpr ⟨by linarith [(hθ i).1], by linarith [(hθ i).2]⟩
    exact hfcont.continuousOn.integrableOn_compact hBcompact
  have hCpair : Pairwise (Function.onFun Disjoint C) := by
    intro b c hbc
    refine Set.disjoint_right.mpr ?_
    intro θ hb hc
    have hex : ∃ i, b i ≠ c i := by
      by_contra h
      apply hbc
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    rcases hex with ⟨i, hdiff⟩
    cases hbval : b i <;> cases hcval : c i
    · exact False.elim (hdiff (by simp [hbval, hcval]))
    · have hi := hb i
      have hj := hc i
      simp [hbval, hcval] at hi hj
      linarith [hi.1, hj.2, hηp, Real.pi_pos]
    · have hi := hb i
      have hj := hc i
      simp [hbval, hcval] at hi hj
      linarith [hi.1, hj.2, hηp, Real.pi_pos]
    · exact False.elim (hdiff (by simp [hbval, hcval]))
  have hQpair : Pairwise (Function.onFun Disjoint Q) := by
    intro b c hbc
    refine Set.disjoint_right.mpr ?_
    intro θ hb hc
    have hex : ∃ i, b i ≠ c i := by
      by_contra h
      apply hbc
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    rcases hex with ⟨i, hdiff⟩
    cases hbval : b i <;> cases hcval : c i
    · exact False.elim (hdiff (by simp [hbval, hcval]))
    · have hi := hb i
      have hj := hc i
      simp [hbval, hcval] at hi hj
      linarith [hi.2, hj.1]
    · have hi := hb i
      have hj := hc i
      simp [hbval, hcval] at hi hj
      linarith [hi.2, hj.1]
    · exact False.elim (hdiff (by simp [hbval, hcval]))
  have hper : ∀ b, (∫ θ in C b, f θ) = ∫ θ in Q b, f θ := by
    intro b
    let m : Fin d → ℤ := fun i => if b i then 0 else 1
    have hpre : (fun u : Fin d → ℝ =>
        u + fun i => 2 * Real.pi * (m i : ℝ)) ⁻¹' Q b = C b := by
      ext θ
      constructor
      · intro hθ i
        cases hbval : b i
        · have hi := hθ i
          simp [hbval, m] at hi
          simp
          exact ⟨by linarith [hi.1, Real.pi_pos], by linarith [hi.2, Real.pi_pos]⟩
        · have hi := hθ i
          simp [hbval, m] at hi
          simp
          exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
      · intro hθ i
        cases hbval : b i
        · have hi := hθ i
          simp [hbval] at hi
          simp [hbval, m]
          exact ⟨by linarith [hi.1, Real.pi_pos], by linarith [hi.2, Real.pi_pos]⟩
        · have hi := hθ i
          simp [hbval] at hi
          simp [hbval, m]
          exact ⟨hi.1, hi.2⟩
    rw [← hpre]
    simpa [f] using (aux_lclt_periodic_setIntegral z m (Q b))
  have hsumC := integral_iUnion_fintype (f := f) hCmeas hCpair hfiC
  have hsumQ := integral_iUnion_fintype (f := f) hQmeas hQpair (fun b =>
    hfiB.mono_set (by
      intro θ hθ
      have h := hθ
      dsimp [Q, B] at h ⊢
      intro i
      by_cases hi : b i
      · have hi' := h i
        simp [hi] at hi'
        exact abs_le.mpr ⟨by linarith [hi'.1], by linarith [hi'.2]⟩
      · have hi' := h i
        simp [hi] at hi'
        exact abs_le.mpr ⟨by linarith [hi'.1], by linarith [hi'.2]⟩))
  change (∑ b, ∫ θ in C b, f θ) = ∫ θ in B, f θ
  calc
    (∑ b, ∫ θ in C b, f θ) = ∑ b, ∫ θ in Q b, f θ := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hper b
    _ = ∫ θ in ⋃ b, Q b, f θ := hsumQ.symm
    _ = ∫ θ in B, f θ := by
      have hQunion : (⋃ b, Q b) =
          {u : Fin d → ℝ | ∀ i, u i ∈ Set.Ioc (Real.pi - η) (Real.pi + η)} := by
        simpa [Q] using (aux_paired_bool_corner_union hη0 hηp)
      rw [hQunion]
      exact setIntegral_congr_set (aux_paired_bool_corner_union_ae (d := d) (η := η))

theorem aux_paired_corner_split {d n : ℕ} (hd : 1 ≤ d) (η : ℝ)
    (hη0 : 0 < η) (hηp : η < Real.pi / 2) (z : LatticeProb.Site d) :
    let f : (Fin d → ℝ) → ℂ := fun θ =>
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
    let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
    let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
      {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
        else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
    let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
    let R : Set (Fin d → ℝ) := T \ (G ∪ ⋃ b, C b)
    ∫ θ in T, f θ = (∫ θ in G, f θ) + (∑ b, ∫ θ in C b, f θ) +
      (∫ θ in R, f θ) := by
  classical
  dsimp
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
      (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
  let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
    {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
  let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
  let R : Set (Fin d → ℝ) := T \ (G ∪ ⋃ b, C b)
  have hT : MeasurableSet T := LatticeProb.LocalCLT.torusBox_measurable d
  have hG : MeasurableSet G := by
    dsimp [G]
    measurability
  have hCmeas : ∀ b, MeasurableSet (C b) := by
    intro b
    dsimp [C]
    measurability
  have hCsub : ∀ b, C b ⊆ T := by
    intro b θ hθ
    simp only [T, LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    constructor
    · intro i
      by_cases hbi : b i
      · have hi := hθ i
        simp [hbi] at hi
        linarith [hi.1, Real.pi_pos]
      · have hi := hθ i
        simp [hbi] at hi
        exact hi.1
    · intro i
      by_cases hbi : b i
      · have hi := hθ i
        simp [hbi] at hi
        exact le_of_lt hi.2
      · have hi := hθ i
        simp [hbi] at hi
        linarith [hi.2, Real.pi_pos]
  have hGsub : G ⊆ T := by
    intro θ hθ
    simp only [T, LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    constructor <;> intro i
    · exact by linarith [(abs_le.mp (hθ i)).1, hηp, Real.pi_pos]
    · exact by linarith [(abs_le.mp (hθ i)).2, hηp, Real.pi_pos]
  have hfiT : IntegrableOn f T volume := by
    simpa [IntegrableOn, f, T, Complex.ofReal_pow, Complex.ofReal_div] using
      LatticeProb.LocalCLT.fourier_integrand_integrable d n z
  have hfiG : IntegrableOn f G volume := hfiT.mono_set hGsub
  have hfiC : ∀ b, IntegrableOn f (C b) volume := fun b => hfiT.mono_set (hCsub b)
  have hCpair : Pairwise (Function.onFun Disjoint C) := by
    intro b c hbc
    refine Set.disjoint_right.mpr ?_
    intro θ hb hc
    have hex : ∃ i, b i ≠ c i := by
      by_contra h
      apply hbc
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    rcases hex with ⟨i, hdiff⟩
    cases hbval : b i <;> cases hcval : c i
    · exact False.elim (hdiff (by simp [hbval, hcval]))
    · have hi := hb i
      have hj := hc i
      simp [hbval, hcval] at hi hj
      linarith [hi.1, hj.2, hηp, Real.pi_pos]
    · have hi := hb i
      have hj := hc i
      simp [hbval, hcval] at hi hj
      linarith [hi.1, hj.2, hηp, Real.pi_pos]
    · exact False.elim (hdiff (by simp [hbval, hcval]))
  have hdis : Disjoint G (⋃ b, C b) := by
    refine Set.disjoint_right.mpr ?_
    intro θ hθC hθG
    rcases Set.mem_iUnion.mp hθC with ⟨b, hb⟩
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    let i : Fin d := Classical.choice inferInstance
    by_cases hbi : b i
    · have hi := hb i
      simp [hbi] at hi
      linarith [(abs_le.mp (hθG i)).2, hi.1, hηp, Real.pi_pos]
    · have hi := hb i
      simp [hbi] at hi
      linarith [(abs_le.mp (hθG i)).1, hi.2, hηp, Real.pi_pos]
  have hU : MeasurableSet (G ∪ ⋃ b, C b) :=
    hG.union (MeasurableSet.iUnion hCmeas)
  have hUsub : G ∪ ⋃ b, C b ⊆ T := by
    exact Set.union_subset hGsub (Set.iUnion_subset (fun b => hCsub b))
  have hfiU : IntegrableOn f (G ∪ ⋃ b, C b) volume := hfiT.mono_set hUsub
  have hfiR : IntegrableOn f R volume := by
    exact hfiT.mono_set (by intro θ hθ; exact hθ.1)
  have hsplit : (∫ θ in T, f θ) =
      (∫ θ in (G ∪ ⋃ b, C b), f θ) + (∫ θ in R, f θ) := by
    have h := setIntegral_sdiff hU hfiT hUsub
    change (∫ θ in T, f θ) = (∫ θ in G ∪ ⋃ b, C b, f θ) +
      (∫ θ in T \ (G ∪ ⋃ b, C b), f θ)
    rw [h]
    simp only [sub_eq_add_neg]
    abel
  have hUC : (∫ θ in (G ∪ ⋃ b, C b), f θ) =
      (∫ θ in G, f θ) + (∫ θ in ⋃ b, C b, f θ) := by
    exact setIntegral_union (μ := volume) (f := f) hdis (MeasurableSet.iUnion hCmeas) hfiG
      (hfiT.mono_set (Set.iUnion_subset (fun b => hCsub b)))
  have hsum := integral_iUnion_fintype (f := f) hCmeas hCpair hfiC
  change (∫ θ in T, f θ) =
    (∫ θ in G, f θ) + (∑ b, ∫ θ in C b, f θ) + (∫ θ in R, f θ)
  calc
    (∫ θ in T, f θ) = (∫ θ in G ∪ ⋃ b, C b, f θ) + (∫ θ in R, f θ) := hsplit
    _ = ((∫ θ in G, f θ) + (∫ θ in ⋃ b, C b, f θ)) + (∫ θ in R, f θ) := by rw [hUC]
    _ = (∫ θ in G, f θ) + (∑ b, ∫ θ in C b, f θ) + (∫ θ in R, f θ) := by rw [hsum]

theorem aux_paired_corner_boundary_ae {d : ℕ} {η : ℝ} (b : Fin d → Bool) :
    {θ : Fin d → ℝ | ∀ i, if b i then θ i ∈ Set.Ioc (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)} =ᵐ[volume]
    {θ : Fin d → ℝ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)} := by
  have hz : volume (⋃ i : Fin d, {θ : Fin d → ℝ | θ i = Real.pi}) = 0 :=
    measure_iUnion_null (fun i => LatticeProb.LocalCLT.volume_hyperplane_eq_zero d i Real.pi)
  have hne : ∀ᵐ θ : Fin d → ℝ ∂volume, ∀ i, θ i ≠ Real.pi := by
    rw [ae_iff]
    apply measure_mono_null _ hz
    intro θ hθ
    push Not at hθ
    exact Set.mem_iUnion.mpr ⟨hθ.choose, hθ.choose_spec⟩
  filter_upwards [hne] with θ hθ
  change (∀ i, if b i then θ i ∈ Set.Ioc (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)) =
    (∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η))
  apply propext
  constructor <;> intro h i <;> by_cases hb : b i
  · have hi := h i
    simp [hb] at hi ⊢
    exact ⟨hi.1, lt_of_le_of_ne hi.2 (hθ i)⟩
  · have hi := h i
    simpa [hb] using hi
  · have hi := h i
    simp [hb] at hi ⊢
    exact ⟨hi.1, le_of_lt hi.2⟩
  · have hi := h i
    simpa [hb] using hi

theorem aux_paired_pi_exp (m : ℤ) :
    Complex.exp (Complex.ofReal (Real.pi * (m : ℝ)) * Complex.I) =
      (-1 : ℂ) ^ m.natAbs := by
  cases m with
  | ofNat k =>
      change Complex.exp (Complex.ofReal (Real.pi * (k : ℝ)) * Complex.I) =
        (-1 : ℂ) ^ k
      rw [show Complex.ofReal (Real.pi * (k : ℝ)) * Complex.I =
        (k : ℤ) * (Real.pi * Complex.I) by push_cast; ring_nf]
      rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
      simp
  | negSucc k =>
      have hneg : Complex.exp (Complex.ofReal (Real.pi * ((-k - 1 : ℤ) : ℝ)) * Complex.I) =
          (-1 : ℂ) ^ (k + 1) := by
        rw [show Complex.ofReal (Real.pi * ((-k - 1 : ℤ) : ℝ)) * Complex.I =
          (-k - 1 : ℤ) * (Real.pi * Complex.I) by push_cast; ring_nf]
        rw [Complex.exp_int_mul, Complex.exp_pi_mul_I,
          show (-k - 1 : ℤ) = -(k + 1) by omega, zpow_neg]
        have hk : (↑k + 1 : ℤ) = (↑(k + 1) : ℤ) := by omega
        rw [hk, zpow_natCast, ← inv_pow]
        simp
      convert hneg using 1
      · push_cast
        ring_nf
      · rw [Int.natAbs_negSucc, pow_succ]

theorem aux_paired_pi_shift_fourier {l : ℕ} (z : Fin 4 → ℤ)
    (θ : Fin 4 → ℝ) :
    aux_paired_fourierIntegrand l z (θ + fun _ => Real.pi) =
      ((-1 : ℂ) ^ l * ∏ k, Complex.exp
        (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I)) *
        aux_paired_fourierIntegrand l z θ := by
  have hchar : aux_paired_character z (θ + fun _ => Real.pi) =
      (∏ k, Complex.exp (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I)) *
        aux_paired_character z θ := by
    dsimp [aux_paired_character]
    calc
      (∏ k, Complex.exp (Complex.ofReal ((θ k + Real.pi) * ((z k : ℤ) : ℝ)) * Complex.I)) =
          ∏ k, (Complex.exp (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I) *
            Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [show (θ k + Real.pi) * ((z k : ℤ) : ℝ) =
          θ k * ((z k : ℤ) : ℝ) + Real.pi * ((z k : ℤ) : ℝ) by ring_nf]
        rw [Complex.ofReal_add, add_mul, Complex.exp_add]
        ring_nf
      _ = (∏ k, Complex.exp (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I)) *
          ∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I) :=
        Finset.prod_mul_distrib
  have hcos : (∑ i : Fin 4, Real.cos (θ i + Real.pi)) =
      -(∑ i : Fin 4, Real.cos (θ i)) := by
    calc
      (∑ i : Fin 4, Real.cos (θ i + Real.pi)) =
          ∑ i : Fin 4, -Real.cos (θ i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
        ring_nf
      _ = -(∑ i : Fin 4, Real.cos (θ i)) := by
        rw [Finset.sum_neg_distrib]
  dsimp [aux_paired_fourierIntegrand]
  rw [hchar, hcos]
  rw [show ((-(∑ i : Fin 4, Real.cos (θ i)) / 4 : ℝ) ^ l : ℂ) =
      ((-1 : ℂ) ^ l) * (((∑ i : Fin 4, Real.cos (θ i)) / 4 : ℝ) ^ l : ℂ) by
        have hp : (-(∑ i : Fin 4, Real.cos (θ i)) / 4 : ℝ) ^ l =
            (-1 : ℝ) ^ l * ((∑ i : Fin 4, Real.cos (θ i)) / 4) ^ l := by
          rw [show -(∑ i : Fin 4, Real.cos (θ i)) / 4 =
            -((∑ i : Fin 4, Real.cos (θ i)) / 4) by ring_nf, neg_pow]
        calc
          (((-(∑ i : Fin 4, Real.cos (θ i)) / 4 : ℝ) : ℂ) ^ l) =
              (((-(∑ i : Fin 4, Real.cos (θ i)) / 4 : ℝ) ^ l : ℝ) : ℂ) :=
            (Complex.ofReal_pow _ _).symm
          _ = (((-1 : ℝ) ^ l * ((∑ i : Fin 4, Real.cos (θ i)) / 4) ^ l : ℝ) : ℂ) := by
            rw [hp]
          _ = ((-1 : ℂ) ^ l) *
              (((∑ i : Fin 4, Real.cos (θ i)) / 4 : ℝ) ^ l : ℂ) := by
            norm_num [Complex.ofReal_mul, Complex.ofReal_pow]]
  ring1

theorem aux_paired_pi_shift_integral {l : ℕ} (z : Fin 4 → ℤ) :
    (∫ θ in {θ : Fin 4 → ℝ | ∀ i, |θ i - Real.pi| ≤ Real.pi / 4},
        aux_paired_fourierIntegrand l z θ) =
      ((-1 : ℂ) ^ l * ∏ k, Complex.exp
        (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (∫ θ in aux_paired_gaussRegion, aux_paired_fourierIntegrand l z θ) := by
  let p : Fin 4 → ℝ := fun _ => Real.pi
  let B : Set (Fin 4 → ℝ) := {θ | ∀ i, |θ i - Real.pi| ≤ Real.pi / 4}
  let G : Set (Fin 4 → ℝ) := aux_paired_gaussRegion
  let f : (Fin 4 → ℝ) → ℂ := aux_paired_fourierIntegrand l z
  let tr : (Fin 4 → ℝ) → Fin 4 → ℝ := fun u => u + p
  have hmp : MeasurePreserving tr volume volume := by
    have h := measurePreserving_add_left volume p
    simpa [tr, add_comm] using h
  have hemb : MeasurableEmbedding tr := by
    have h := (Homeomorph.addLeft p).measurableEmbedding
    simpa [tr, add_comm] using h
  have hpre : tr ⁻¹' B = G := by
    ext u
    simp only [B, G, aux_paired_gaussRegion, tr, Set.mem_preimage, Set.mem_setOf_eq,
      Pi.add_apply]
    constructor
    · intro h i
      have hi := h i
      simpa [p] using hi
    · intro h i
      have hi := h i
      simpa [p] using hi
  have hchange := hmp.setIntegral_preimage_emb hemb f B
  have hpt : ∀ u, f (tr u) =
      ((-1 : ℂ) ^ l * ∏ k, Complex.exp
        (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I)) * f u := by
    intro u
    exact aux_paired_pi_shift_fourier z u
  change (∫ θ in B, f θ) = _
  calc
    (∫ θ in B, f θ) = ∫ θ in tr ⁻¹' B, f (tr θ) := hchange.symm
    _ = ∫ θ in G, f (tr θ) := by rw [hpre]
    _ = ∫ θ in G, ((-1 : ℂ) ^ l * ∏ k, Complex.exp
          (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I)) * f θ := by
      apply integral_congr_ae
      filter_upwards with θ
      exact hpt θ
    _ = ((-1 : ℂ) ^ l * ∏ k, Complex.exp
          (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I)) *
        ∫ θ in G, f θ := by rw [integral_const_mul]

theorem aux_paired_mixed_pointwise {d n : ℕ} (hd : 1 ≤ d) (η : ℝ)
    (hη0 : 0 < η) (hηp : η < Real.pi / 2) (θ : Fin d → ℝ)
    (z : LatticeProb.Site d)
    (hθT : θ ∈ LatticeProb.LocalCLT.torusBox d)
    (hlo : ∃ i, |θ i| ≤ η) (hhi : ∃ j, Real.pi - η ≤ |θ j|) :
    ‖(∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)‖ ≤
      Real.exp (- (n : ℝ) / (d : ℝ)) := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  have hij : i ≠ j := by
    intro hij
    subst j
    have hpi : Real.pi ≤ 2 * η := by linarith [hi, hj]
    linarith [hηp, Real.pi_pos]
  have hd2 : 2 ≤ d := by
    have hi' := i.isLt
    have hj' := j.isLt
    omega
  have hTcoord : ∀ k : Fin d, |θ k| ≤ Real.pi := by
    intro k
    have ht := hθT
    simp only [LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def] at ht
    exact abs_le.mpr ⟨ht.1 k, ht.2 k⟩
  have hcosη : 0 ≤ Real.cos η := by
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hη0]) hηp.le
  have hcoslow : Real.cos η ≤ Real.cos (θ i) := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by linarith [hηp, Real.pi_pos]) hi
    rw [Real.cos_abs] at hc
    exact hc
  have hcoshigh : Real.cos (θ j) ≤ -Real.cos η := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi - η by linarith [hηp, Real.pi_pos])
      (hTcoord j) hj
    rw [Real.cos_abs] at hc
    rw [Real.cos_sub, Real.cos_pi, Real.sin_pi] at hc
    simpa using hc
  have hsumUpper : ∑ k : Fin d, Real.cos (θ k) ≤
      (d : ℝ) - (1 + Real.cos η) := by
    have hrest : ∑ k ∈ Finset.univ.erase j, Real.cos (θ k) ≤
        (d : ℝ) - 1 := by
      calc
        ∑ k ∈ Finset.univ.erase j, Real.cos (θ k) ≤
            ∑ k ∈ Finset.univ.erase j, (1 : ℝ) :=
          Finset.sum_le_sum (fun k hk => Real.cos_le_one _)
        _ = (d : ℝ) - 1 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
          norm_num
          rw [Nat.cast_sub (by omega)]
          norm_num
    have hdecomp := Finset.sum_erase_add Finset.univ (fun k : Fin d => Real.cos (θ k))
      (Finset.mem_univ j)
    rw [← hdecomp]
    linarith
  have hsumLower : -(d : ℝ) + (1 + Real.cos η) ≤ ∑ k : Fin d, Real.cos (θ k) := by
    have hrest : -(d : ℝ) + 1 ≤ ∑ k ∈ Finset.univ.erase i, Real.cos (θ k) := by
      calc
        -(d : ℝ) + 1 = ∑ k ∈ Finset.univ.erase i, (-1 : ℝ) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
          norm_num
          rw [Nat.cast_sub (by omega)]
          ring_nf
        _ ≤ ∑ k ∈ Finset.univ.erase i, Real.cos (θ k) :=
          Finset.sum_le_sum (fun k hk => Real.neg_one_le_cos _)
    have hdecomp := Finset.sum_erase_add Finset.univ (fun k : Fin d => Real.cos (θ k))
      (Finset.mem_univ i)
    rw [← hdecomp]
    linarith
  let q : ℝ := LatticeProb.charFn d θ
  have hqabs : |q| ≤ 1 - 1 / (d : ℝ) := by
    rw [abs_le]
    constructor
    · dsimp [q, LatticeProb.charFn]
      apply (le_div_iff₀ hd0).2
      have hident : -(1 - 1 / (d : ℝ)) * (d : ℝ) = -(d : ℝ) + 1 := by
        field_simp
        ring_nf
      rw [hident]
      linarith
    · dsimp [q, LatticeProb.charFn]
      apply (div_le_iff₀ hd0).2
      have hident : (1 - 1 / (d : ℝ)) * (d : ℝ) = (d : ℝ) - 1 := by
        field_simp
      rw [hident]
      linarith
  have hqnonneg : 0 ≤ 1 - 1 / (d : ℝ) := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hdiv : 1 / (d : ℝ) ≤ 1 := (div_le_iff₀ hd0).2 (by linarith)
    linarith
  have hnorm :
      ‖(∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
          (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)‖ = |q| ^ n := by
    change ‖(∏ k, Complex.exp
        (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
          (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)‖ =
      |LatticeProb.charFn d θ| ^ n
    rw [norm_mul, norm_prod]
    simp only [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero,
      Finset.prod_const_one, one_mul]
    rfl
  rw [hnorm]
  calc
    |q| ^ n ≤ (1 - 1 / (d : ℝ)) ^ n := pow_le_pow_left₀ (abs_nonneg _) hqabs n
    _ ≤ Real.exp (-(1 / (d : ℝ))) ^ n :=
      pow_le_pow_left₀ hqnonneg (Real.one_sub_le_exp_neg _) n
    _ = Real.exp (- (n : ℝ) / (d : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring_nf

theorem aux_paired_residual_integral {l : ℕ} (hl : 1 ≤ l) (z : Fin 4 → ℤ) :
    let T : Set (Fin 4 → ℝ) := LatticeProb.LocalCLT.torusBox 4
    let G : Set (Fin 4 → ℝ) := aux_paired_gaussRegion
    let C : (Fin 4 → Bool) → Set (Fin 4 → ℝ) := fun b =>
      {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - Real.pi / 4) Real.pi
        else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + Real.pi / 4)}
    let R : Set (Fin 4 → ℝ) := T \ (G ∪ ⋃ b, C b)
    ‖∫ θ in R, aux_paired_fourierIntegrand l z θ‖ ≤
      20000000000000 / (l : ℝ) ^ 3 := by
  classical
  dsimp
  let η : ℝ := Real.pi / 4
  let T : Set (Fin 4 → ℝ) := LatticeProb.LocalCLT.torusBox 4
  let G : Set (Fin 4 → ℝ) := aux_paired_gaussRegion
  let C : (Fin 4 → Bool) → Set (Fin 4 → ℝ) := fun b =>
    {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
  let R : Set (Fin 4 → ℝ) := T \ (G ∪ ⋃ b, C b)
  let F : Set (Fin 4 → ℝ) := {θ | θ ∈ T ∧ ∃ i, η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η}
  let M : Set (Fin 4 → ℝ) := {θ | θ ∈ T ∧ θ ∉ F ∧
    (∃ i, |θ i| ≤ η) ∧ (∃ j, Real.pi - η ≤ |θ j|)}
  have hT : MeasurableSet T := by
    exact LatticeProb.LocalCLT.torusBox_measurable 4
  have hG : MeasurableSet G := by
    dsimp [G, aux_paired_gaussRegion]
    measurability
  have hC : ∀ b, MeasurableSet (C b) := by
    intro b
    dsimp [C]
    measurability
  have hF : MeasurableSet F := by
    dsimp [F]
    measurability
  have hM : MeasurableSet M := by
    dsimp [M]
    measurability
  have hRmeas : MeasurableSet R := by
    dsimp [R]
    exact hT.diff (hG.union (MeasurableSet.iUnion hC))
  have hRint : IntegrableOn (aux_paired_fourierIntegrand l z) R volume := by
    apply (aux_paired_fourier_integrable l z).mono_set
    intro θ hθ
    exact hθ.1
  have hFsub : F ⊆ T := by
    intro θ hθ
    exact hθ.1
  have hMsub : M ⊆ T := by
    intro θ hθ
    exact hθ.1
  have hMixBound : ∀ θ ∈ M,
      ‖aux_paired_fourierIntegrand l z θ‖ ≤ Real.exp (-(l : ℝ) / 4) := by
    intro θ hθ
    exact aux_paired_mixed_pointwise (d := 4) (n := l) (by omega) η
      (by dsimp [η]; positivity) (by dsimp [η]; linarith [Real.pi_pos]) θ z hθ.1
      hθ.2.2.1 hθ.2.2.2
  have hpi : 0 < Real.pi := Real.pi_pos
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hηp : η < Real.pi / 2 := by dsimp [η]; linarith
  have hne : ∀ᵐ θ : Fin 4 → ℝ ∂volume, ∀ i, θ i ≠ Real.pi := by
    have hz : volume (⋃ i : Fin 4, {θ : Fin 4 → ℝ | θ i = Real.pi}) = 0 :=
      measure_iUnion_null (fun i => LatticeProb.LocalCLT.volume_hyperplane_eq_zero 4 i Real.pi)
    rw [ae_iff]
    apply measure_mono_null _ hz
    intro θ hθ
    push Not at hθ
    exact Set.mem_iUnion.mpr ⟨hθ.choose, hθ.choose_spec⟩
  have hRcover : ∀ᵐ θ : Fin 4 → ℝ ∂volume, θ ∈ R → θ ∈ F ∪ M := by
    filter_upwards [hne] with θ hθpi
    intro hθR
    change θ ∈ T ∧ θ ∉ (G ∪ ⋃ b, C b) at hθR
    have hnotG : ¬ θ ∈ G := by
      intro h
      exact hθR.2 (Or.inl h)
    have hnotC : θ ∉ ⋃ b, C b := by
      intro h
      exact hθR.2 (Or.inr h)
    by_cases hFar : θ ∈ F
    · exact Or.inl hFar
    · right
      refine ⟨hθR.1, hFar, ?_, ?_⟩
      · by_contra hlow
        push Not at hlow
        apply hnotC
        let b : Fin 4 → Bool := fun i => decide (0 < θ i)
        refine Set.mem_iUnion.mpr ⟨b, ?_⟩
        intro i
        have hTi := hθR.1
        have hcoord : |θ i| ≤ Real.pi := by
          simp only [T, LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def] at hTi
          exact abs_le.mpr ⟨hTi.1 i, hTi.2 i⟩
        have hnotfar : ¬ (η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η) := by
          intro hf
          exact hFar ⟨hθR.1, ⟨i, hf.1, hf.2⟩⟩
        have hhigh : Real.pi - η < |θ i| := by
          by_contra hlowhigh
          have hbetween : η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η :=
            ⟨(hlow i).le, le_of_not_gt hlowhigh⟩
          exact hnotfar hbetween
        by_cases hi : 0 < θ i
        · simp only [b, hi, decide_true]
          have hcoord' := abs_le.mp hcoord
          have hlt : θ i < Real.pi := lt_of_le_of_ne hcoord'.2 (hθpi i)
          exact ⟨by simpa [abs_of_pos hi] using hhigh, hlt⟩
        · simp only [b, hi, decide_false]
          have hneg : θ i ≤ 0 := le_of_not_gt hi
          have hcoord' := abs_le.mp hcoord
          exact ⟨by linarith [hcoord'.1], by
              rw [abs_of_nonpos hneg] at hhigh
              linarith [hhigh]
            ⟩
      · change ¬ (∀ i, |θ i| ≤ η) at hnotG
        push Not at hnotG
        obtain ⟨i, hi⟩ := hnotG
        refine ⟨i, ?_⟩
        have hi' : η < |θ i| := hi
        have hnotfar : ¬ (η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η) := by
          intro hf
          exact hFar ⟨hθR.1, ⟨i, hf.1, hf.2⟩⟩
        exact le_of_not_ge (fun hle => hnotfar ⟨hi'.le, hle⟩)
  have hfiT : IntegrableOn (fun θ => ‖aux_paired_fourierIntegrand l z θ‖) T volume := by
    exact (aux_paired_fourier_integrable l z).norm
  have hfiU : IntegrableOn (fun θ => ‖aux_paired_fourierIntegrand l z θ‖) (F ∪ M) volume :=
    hfiT.mono_set (Set.union_subset hFsub hMsub)
  have hmono : ∫ θ in R, ‖aux_paired_fourierIntegrand l z θ‖ ≤
      ∫ θ in F ∪ M, ‖aux_paired_fourierIntegrand l z θ‖ :=
    setIntegral_mono_set hfiU (Filter.Eventually.of_forall (fun θ => norm_nonneg _)) hRcover
  have hFbound : ∫ θ in F, ‖aux_paired_fourierIntegrand l z θ‖ ≤
      (2 * Real.pi) ^ 4 * Real.exp (-(l : ℝ) * (2 / 4) * η ^ 2 / Real.pi ^ 2) := by
    exact aux_lclt_far_region_integral_norm (d := 4) (n := l) (by omega) η hη0 hηp.le z
  have hvolT : volume.real T = (2 * Real.pi) ^ 4 := by
    rw [Measure.real_def]
    dsimp [T, LatticeProb.LocalCLT.torusBox]
    rw [Real.volume_Icc_pi_toReal]
    · simp [Real.pi_pos.le]
      ring_nf
    · intro i
      linarith [Real.pi_pos]
  have hTfinite : volume T < ⊤ := by
    dsimp [T, LatticeProb.LocalCLT.torusBox]
    exact measure_Icc_lt_top
  have hMfinite : volume M < ⊤ := (measure_mono hMsub).trans_lt hTfinite
  have hMvol : volume.real M ≤ (2 * Real.pi) ^ 4 := by
    calc
      volume.real M ≤ volume.real T := measureReal_mono hMsub (ne_of_lt (by finiteness))
      _ = (2 * Real.pi) ^ 4 := hvolT
  have hMbound : ∫ θ in M, ‖aux_paired_fourierIntegrand l z θ‖ ≤
      Real.exp (-(l : ℝ) / 4) * (2 * Real.pi) ^ 4 := by
    have hconst : IntegrableOn (fun _ : Fin 4 → ℝ => Real.exp (-(l : ℝ) / 4)) M volume :=
      integrableOn_const hMfinite.ne (by finiteness)
    have hle := setIntegral_mono_on
      (hfiT.mono_set hMsub) hconst hM (fun θ hθ => hMixBound θ hθ)
    rw [setIntegral_const] at hle
    have hle' : (∫ θ in M, ‖aux_paired_fourierIntegrand l z θ‖) ≤
        volume.real M * Real.exp (-(l : ℝ) / 4) := by
      simpa [smul_eq_mul] using hle
    calc
      _ ≤ volume.real M * Real.exp (-(l : ℝ) / 4) := hle'
      _ = Real.exp (-(l : ℝ) / 4) * volume.real M := by ring_nf
      _ ≤ Real.exp (-(l : ℝ) / 4) * (2 * Real.pi) ^ 4 :=
        mul_le_mul_of_nonneg_left hMvol (Real.exp_nonneg _)
  have hUM : (∫ θ in F ∪ M, ‖aux_paired_fourierIntegrand l z θ‖) ≤
      (2 * Real.pi) ^ 4 * Real.exp (-(l : ℝ) * (2 / 4) * η ^ 2 / Real.pi ^ 2) +
        Real.exp (-(l : ℝ) / 4) * (2 * Real.pi) ^ 4 := by
    have hdis : Disjoint F M := by
      refine Set.disjoint_right.mpr ?_
      intro θ hθM hθF
      exact hθM.2.1 hθF
    have hfiF : IntegrableOn (fun θ => ‖aux_paired_fourierIntegrand l z θ‖) F volume :=
      hfiT.mono_set hFsub
    have hfiM : IntegrableOn (fun θ => ‖aux_paired_fourierIntegrand l z θ‖) M volume :=
      hfiT.mono_set hMsub
    rw [setIntegral_union hdis hM hfiF hfiM]
    linarith
  have hpow : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hexpF : (2 * Real.pi) ^ 4 * Real.exp (-(l : ℝ) * (2 / 4) * η ^ 2 / Real.pi ^ 2) ≤
      10000000000000 / (l : ℝ) ^ 3 := by
    have hu : 0 < (l : ℝ) * (2 / 4) * η ^ 2 / Real.pi ^ 2 := by positivity
    have he := aux_paired_exp_neg_le_inv_cube hu
    have he' : Real.exp (-(l : ℝ) * (2 / 4) * η ^ 2 / Real.pi ^ 2) ≤
        27 / ((l : ℝ) * (2 / 4) * η ^ 2 / Real.pi ^ 2) ^ 3 := by
      convert he using 1; ring_nf
    calc
      _ ≤ (2 * Real.pi) ^ 4 * (27 /
          ((l : ℝ) * (2 / 4) * η ^ 2 / Real.pi ^ 2) ^ 3) := by
            exact mul_le_mul_of_nonneg_left he' (by positivity)
      _ ≤ 10000000000000 / (l : ℝ) ^ 3 := by
        dsimp [η]
        have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
        have hpi4 : Real.pi ^ 4 ≤ (4 : ℝ) ^ 4 :=
          pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 4
        field_simp [ne_of_gt hpow, ne_of_gt hpi2]
        nlinarith [hpi4]
  have hexpM : Real.exp (-(l : ℝ) / 4) * (2 * Real.pi) ^ 4 ≤
      10000000000000 / (l : ℝ) ^ 3 := by
    have hu : 0 < (l : ℝ) / 4 := by positivity
    have he := aux_paired_exp_neg_le_inv_cube hu
    have he' : Real.exp (-(l : ℝ) / 4) ≤ 27 / ((l : ℝ) / 4) ^ 3 := by
      convert he using 1; ring_nf
    calc
      _ ≤ (27 / ((l : ℝ) / 4) ^ 3) * (2 * Real.pi) ^ 4 := by
        exact mul_le_mul_of_nonneg_right he' (by positivity)
      _ ≤ 10000000000000 / (l : ℝ) ^ 3 := by
        field_simp [ne_of_gt hpow]
        have hpi4 : Real.pi ^ 4 ≤ (4 : ℝ) ^ 4 :=
          pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 4
        nlinarith [hpi4]
  calc
    ‖∫ θ in R, aux_paired_fourierIntegrand l z θ‖ ≤
        ∫ θ in R, ‖aux_paired_fourierIntegrand l z θ‖ :=
      norm_integral_le_integral_norm (μ := volume.restrict R)
        (fun θ => aux_paired_fourierIntegrand l z θ)
    _ ≤ ∫ θ in F ∪ M, ‖aux_paired_fourierIntegrand l z θ‖ := hmono
    _ ≤ 20000000000000 / (l : ℝ) ^ 3 := by
      calc
        _ ≤ (2 * Real.pi) ^ 4 * Real.exp (-(l : ℝ) * (2 / 4) * η ^ 2 / Real.pi ^ 2) +
            Real.exp (-(l : ℝ) / 4) * (2 * Real.pi) ^ 4 := hUM
        _ ≤ 10000000000000 / (l : ℝ) ^ 3 +
            10000000000000 / (l : ℝ) ^ 3 := add_le_add hexpF hexpM
        _ = 20000000000000 / (l : ℝ) ^ 3 := by ring_nf

theorem aux_paired_scalar_main {n : ℕ} (hn : 1 ≤ n) (S : ℝ) (hS : 0 ≤ S) :
    |4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
        4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) * Real.exp (-2 * S / (n + 1)) -
        8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n)| ≤
      1000 / (n : ℝ) ^ 3 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 0 < (n + 1 : ℝ) := by positivity
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpi2 : 1 ≤ Real.pi ^ 2 := by nlinarith [sq_nonneg (Real.pi - 1)]
  let a : ℝ := 2 * S / (n + 1 : ℝ)
  let b : ℝ := 2 * S / (n : ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    apply (div_le_div_iff₀ hn1 hn0).2
    nlinarith [hS]
  have hba : b - a = a / (n : ℝ) := by
    dsimp [a, b]
    field_simp
    ring_nf
  have hexpdiff : |Real.exp (-a) - Real.exp (-b)| ≤ 1 / (n : ℝ) := by
    have hfac : Real.exp (-a) - Real.exp (-b) =
        Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
      rw [show -b = -a + -(b - a) by ring_nf, Real.exp_add]
      ring_nf
    have hnonneg : 0 ≤ Real.exp (-a) - Real.exp (-b) := by
      apply sub_nonneg.mpr
      exact Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg hnonneg, hfac]
    have hlin := Real.one_sub_le_exp_neg (b - a)
    have hlin' : 1 - Real.exp (-(b - a)) ≤ b - a := by linarith
    have hmul := mul_le_mul_of_nonneg_left hlin' (Real.exp_nonneg (-a))
    have hunit : a * Real.exp (-a) ≤ 1 := by
      have h := Real.add_one_le_exp a
      have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-a))
      rw [← Real.exp_add] at hm
      simp at hm
      nlinarith
    calc
      Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤
          Real.exp (-a) * (b - a) := hmul
      _ = a * Real.exp (-a) / (n : ℝ) := by rw [hba]; ring_nf
      _ ≤ 1 / (n : ℝ) := by
        exact (div_le_div_of_nonneg_right hunit (le_of_lt hn0))
  have hcoef : |4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) -
        4 / (Real.pi ^ 2 * (n : ℝ) ^ 2)| ≤ 12 / (n : ℝ) ^ 3 := by
    have hsign : 4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) -
        4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) ≤ 0 := by
      have hden : (n : ℝ) ^ 2 ≤ (n + 1 : ℝ) ^ 2 := by nlinarith
      have hden0 : 0 < Real.pi ^ 2 * (n : ℝ) ^ 2 := by positivity
      have hden1 : 0 < Real.pi ^ 2 * (n + 1 : ℝ) ^ 2 := by positivity
      have hfrac : 4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) ≤
          4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) := by
        apply (div_le_div_iff₀ hden1 hden0).2
        nlinarith [hden]
      exact sub_nonpos.mpr hfrac
    rw [abs_of_nonpos hsign]
    have hpi2pos : 0 < Real.pi ^ 2 := sq_pos_of_pos hpi0
    field_simp [ne_of_gt hn0, ne_of_gt hn1, ne_of_gt hpi2pos]
    nlinarith [hpi2]
  have hcoef0 : |4 / (Real.pi ^ 2 * (n : ℝ) ^ 2)| ≤ 4 / (n : ℝ) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have hpi2pos : 0 < Real.pi ^ 2 := sq_pos_of_pos hpi0
    have hden0 : 0 < Real.pi ^ 2 * (n : ℝ) ^ 2 := by positivity
    have hden1 : 0 < (n : ℝ) ^ 2 := by positivity
    have hfrac : 4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) ≤ 4 / (n : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ hden0 hden1).2
      nlinarith [hpi2]
    exact hfrac
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hea : Real.exp (-a) ≤ 1 := by
    simpa using (Real.exp_le_exp.mpr (show -a ≤ (0 : ℝ) by linarith))
  have he0 : Real.exp (-b) ≤ 1 := by
    simpa using (Real.exp_le_exp.mpr (show -b ≤ (0 : ℝ) by linarith))
  have hdecomp :
      4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-b) +
          4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) * Real.exp (-a) -
          8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-b) =
        (4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) -
          4 / (Real.pi ^ 2 * (n : ℝ) ^ 2)) * Real.exp (-a) +
        (4 / (Real.pi ^ 2 * (n : ℝ) ^ 2)) *
          (Real.exp (-a) - Real.exp (-b)) := by ring_nf
  have harg0 : -2 * S / (n : ℝ) = -b := by dsimp [b]; ring_nf
  have harg1 : -2 * S / (n + 1 : ℝ) = -a := by dsimp [a]; ring_nf
  rw [harg0, harg1, hdecomp]
  calc
    |(4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) -
          4 / (Real.pi ^ 2 * (n : ℝ) ^ 2)) * Real.exp (-a) +
        (4 / (Real.pi ^ 2 * (n : ℝ) ^ 2)) *
          (Real.exp (-a) - Real.exp (-b))| ≤
        |4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) -
          4 / (Real.pi ^ 2 * (n : ℝ) ^ 2)| * |Real.exp (-a)| +
        |4 / (Real.pi ^ 2 * (n : ℝ) ^ 2)| *
          |Real.exp (-a) - Real.exp (-b)| := by
      calc
        _ ≤ |(4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) -
            4 / (Real.pi ^ 2 * (n : ℝ) ^ 2)) * Real.exp (-a)| +
            |(4 / (Real.pi ^ 2 * (n : ℝ) ^ 2)) *
              (Real.exp (-a) - Real.exp (-b))| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ 12 / (n : ℝ) ^ 3 + 4 / (n : ℝ) ^ 2 * (1 / (n : ℝ)) := by
      rw [abs_of_nonneg (Real.exp_nonneg (-a))]
      apply add_le_add
      · calc
          _ ≤ (12 / (n : ℝ) ^ 3) * 1 :=
            mul_le_mul hcoef hea (by positivity) (by positivity)
          _ = 12 / (n : ℝ) ^ 3 := by ring_nf
      · exact mul_le_mul hcoef0 hexpdiff (by positivity) (by positivity)
    _ ≤ 1000 / (n : ℝ) ^ 3 := by
      field_simp [ne_of_gt hn0]
      nlinarith

theorem aux_paired_gaussian_tail {l : ℕ} (hl : 1 ≤ l) (z : Fin 4 → ℤ) :
    ‖(∫ θ in aux_paired_gaussRegion, aux_paired_gaussianIntegrand l z θ) -
        ∫ θ : Fin 4 → ℝ, aux_paired_gaussianIntegrand l z θ‖ ≤
      10000000000000 / (l : ℝ) ^ 3 := by
  let G := aux_paired_gaussRegion
  let g := aux_paired_gaussianIntegrand l z
  have hG : MeasurableSet G := by
    dsimp [G, aux_paired_gaussRegion]
    measurability
  have hgi : Integrable g := aux_paired_gaussian_integrable (by omega) z
  have hgiG : IntegrableOn g G volume := hgi.integrableOn
  have hgiGc : IntegrableOn g Gᶜ volume := hgi.integrableOn
  have hsplit : (∫ θ : Fin 4 → ℝ, g θ) =
      (∫ θ in G, g θ) + ∫ θ in Gᶜ, g θ := by
    rw [← setIntegral_union disjoint_compl_right hG.compl hgiG hgiGc]
    simp
  have hnorm : ‖∫ θ in Gᶜ, g θ‖ ≤ ∫ θ in Gᶜ, ‖g θ‖ :=
    norm_integral_le_integral_norm (μ := volume.restrict Gᶜ) g
  have hgnorm : ∀ θ, ‖g θ‖ =
      Real.exp (-(l : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 8) := by
    intro θ
    dsimp [g, aux_paired_gaussianIntegrand]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
      aux_paired_character_norm]
    ring_nf
  have htail := aux_lclt_gaussian_tail (d := 4) ((l : ℝ) / 8) (Real.pi / 4)
    (by positivity) (by positivity)
  have htail' : (∫ θ in Gᶜ, ‖g θ‖) ≤
      (Real.pi / ((l : ℝ) / 8 / 2)) ^ 2 *
        Real.exp (-((l : ℝ) / 8) * (Real.pi / 4) ^ 2 / 2) := by
    rw [show Gᶜ = {θ : Fin 4 → ℝ | ¬ ∀ i, |θ i| ≤ Real.pi / 4} by
      ext θ; simp [G, aux_paired_gaussRegion]]
    simp_rw [hgnorm]
    convert htail using 1
    all_goals norm_num
    all_goals ring_nf
  have hlr : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hexp : (Real.pi / ((l : ℝ) / 8 / 2)) ^ 2 *
        Real.exp (-((l : ℝ) / 8) * (Real.pi / 4) ^ 2 / 2) ≤
      10000000000000 / (l : ℝ) ^ 3 := by
    have hu : 0 < ((l : ℝ) / 8) * (Real.pi / 4) ^ 2 / 2 := by positivity
    have he := aux_paired_exp_neg_le_inv_cube hu
    have he' : Real.exp (-((l : ℝ) / 8) * (Real.pi / 4) ^ 2 / 2) ≤
        27 / (((l : ℝ) / 8) * (Real.pi / 4) ^ 2 / 2) ^ 3 := by
      convert he using 1; ring_nf
    calc
      _ ≤ (Real.pi / ((l : ℝ) / 8 / 2)) ^ 2 *
          (27 / (((l : ℝ) / 8) * (Real.pi / 4) ^ 2 / 2) ^ 3) :=
        mul_le_mul_of_nonneg_left he' (by positivity)
      _ ≤ 10000000000000 / (l : ℝ) ^ 3 := by
        have hpi4 : Real.pi ^ 4 ≤ (4 : ℝ) ^ 4 :=
          pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 4
        have hpi6 : Real.pi ^ 6 ≤ (4 : ℝ) ^ 6 :=
          pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 6
        have hpi3 : (3 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
        have hpi4lower : (81 : ℝ) ≤ Real.pi ^ 4 := by
          have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hpi3 4
          norm_num at h ⊢
          exact h
        have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
        have hl2 : (1 : ℝ) ≤ (l : ℝ) ^ 2 := by nlinarith [sq_nonneg ((l : ℝ) - 1)]
        have hprod : (81 : ℝ) ≤ (l : ℝ) ^ 2 * Real.pi ^ 4 := by
          calc
            (81 : ℝ) = 1 * 81 := by norm_num
            _ ≤ (l : ℝ) ^ 2 * 81 := by gcongr
            _ ≤ (l : ℝ) ^ 2 * Real.pi ^ 4 := by gcongr
        field_simp [ne_of_gt hlr, ne_of_gt (sq_pos_of_pos Real.pi_pos)]
        nlinarith [hpi4, hpi6, hprod]
  rw [show (∫ θ in G, g θ) - ∫ θ : Fin 4 → ℝ, g θ = -∫ θ in Gᶜ, g θ by
    rw [hsplit]; ring_nf]
  calc
    ‖-∫ θ in Gᶜ, g θ‖ = ‖∫ θ in Gᶜ, g θ‖ := norm_neg _
    _ ≤ ∫ θ in Gᶜ, ‖g θ‖ := hnorm
    _ ≤ 10000000000000 / (l : ℝ) ^ 3 := htail'.trans hexp

theorem aux_paired_gaussian_difference {n : ℕ} (hn : 1 ≤ n) (z : Fin 4 → ℤ) :
    ‖(∫ θ in aux_paired_gaussRegion,
        aux_paired_gaussianIntegrand n z θ -
          aux_paired_gaussianIntegrand (n + 1) z θ)‖ ≤
      10000 / (n : ℝ) ^ 3 := by
  let G := aux_paired_gaussRegion
  let g := fun l : ℕ => aux_paired_gaussianIntegrand l z
  have hG : MeasurableSet G := by
    dsimp [G, aux_paired_gaussRegion]
    measurability
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hS : ∀ θ : Fin 4 → ℝ, 0 ≤ ∑ i : Fin 4, θ i ^ 2 := fun θ =>
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hpoint : ∀ θ ∈ G, ‖g n θ - g (n + 1) θ‖ ≤
      2 / (n : ℝ) * Real.exp (-(n : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 16) := by
    intro θ hθ
    let S : ℝ := ∑ i : Fin 4, θ i ^ 2
    have hS0 : 0 ≤ S := hS θ
    have hexp : Real.exp (-(n : ℝ) * S / 8) -
        Real.exp (-((n + 1 : ℕ) : ℝ) * S / 8) ≤
        S / 8 * Real.exp (-(n : ℝ) * S / 8) := by
      have hfac : Real.exp (-(n : ℝ) * S / 8) -
          Real.exp (-((n + 1 : ℕ) : ℝ) * S / 8) =
          Real.exp (-(n : ℝ) * S / 8) * (1 - Real.exp (-S / 8)) := by
        rw [show -((n + 1 : ℕ) : ℝ) * S / 8 =
            -(n : ℝ) * S / 8 + -S / 8 by push_cast; ring_nf, Real.exp_add]
        ring_nf
      have hlin := Real.one_sub_le_exp_neg (S / 8)
      have hlin' : 1 - Real.exp (-S / 8) ≤ S / 8 := by
        calc
          1 - Real.exp (-S / 8) ≤ 1 - (1 - S / 8) := by
            simpa [div_eq_mul_inv] using sub_le_sub_left hlin 1
          _ = S / 8 := by ring_nf
      rw [hfac]
      calc
        Real.exp (-(n : ℝ) * S / 8) * (1 - Real.exp (-S / 8)) ≤
            Real.exp (-(n : ℝ) * S / 8) * (S / 8) :=
          mul_le_mul_of_nonneg_left hlin' (Real.exp_nonneg _)
        _ = S / 8 * Real.exp (-(n : ℝ) * S / 8) := by ring_nf
    have hnonneg : 0 ≤ Real.exp (-(n : ℝ) * S / 8) -
        Real.exp (-((n + 1 : ℕ) : ℝ) * S / 8) := by
      apply sub_nonneg.mpr
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith [hS0]
    have hnorm : ‖g n θ - g (n + 1) θ‖ =
        Real.exp (-(n : ℝ) * S / 8) -
          Real.exp (-((n + 1 : ℕ) : ℝ) * S / 8) := by
      dsimp [g, aux_paired_gaussianIntegrand, S]
      rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num]
      rw [← sub_mul]
      have hnonneg' : 0 ≤ Real.exp ((-↑n * ∑ i : Fin 4, θ i ^ 2) / 8) -
          Real.exp ((-(↑n + 1) * ∑ i : Fin 4, θ i ^ 2) / 8) := by
        simpa [S] using hnonneg
      rw [← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hnonneg', aux_paired_character_norm]
      simp
    rw [hnorm]
    have hu : 0 ≤ (n : ℝ) * S / 16 := by positivity
    have hunit : (n : ℝ) * S / 16 * Real.exp (-(n : ℝ) * S / 16) ≤ 1 := by
      have h := Real.add_one_le_exp ((n : ℝ) * S / 16)
      have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-(n : ℝ) * S / 16))
      have hprod : Real.exp ((n : ℝ) * S / 16) *
          Real.exp (-(n : ℝ) * S / 16) = 1 := by
        calc
          _ = Real.exp ((n : ℝ) * S / 16 + -(n : ℝ) * S / 16) :=
            (Real.exp_add _ _).symm
          _ = 1 := by ring_nf; simp
      nlinarith [hm, hprod]
    calc
      Real.exp (-(n : ℝ) * S / 8) -
          Real.exp (-((n + 1 : ℕ) : ℝ) * S / 8) ≤
          S / 8 * Real.exp (-(n : ℝ) * S / 8) := hexp
      _ = 2 / (n : ℝ) * ((n : ℝ) * S / 16) *
          Real.exp (-(n : ℝ) * S / 16) * Real.exp (-(n : ℝ) * S / 16) := by
        have he : Real.exp (-(n : ℝ) * S / 8) =
            Real.exp (-(n : ℝ) * S / 16) * Real.exp (-(n : ℝ) * S / 16) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
        rw [he]
        field_simp [ne_of_gt hn0]
        ring_nf
      _ ≤ 2 / (n : ℝ) * Real.exp (-(n : ℝ) * S / 16) := by
        have := mul_le_mul_of_nonneg_right hunit (Real.exp_nonneg (-(n : ℝ) * S / 16))
        have hp : 0 ≤ 2 / (n : ℝ) := by positivity
        gcongr
        nlinarith
  have hbound : IntegrableOn (fun θ : Fin 4 → ℝ =>
      2 / (n : ℝ) * Real.exp (-(n : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 16)) G volume := by
    have hi := aux_lclt_full_gaussian_integrable (d := 4) ((n : ℝ) / 16) (by positivity)
    have hi' : Integrable (fun θ : Fin 4 → ℝ =>
        2 / (n : ℝ) * Real.exp (-(n : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 16)) := by
      refine (hi.const_mul (2 / (n : ℝ))).congr ?_
      filter_upwards with θ
      congr 1
      ring_nf
    exact hi'.integrableOn
  have hnorm : ‖∫ θ in G, g n θ - g (n + 1) θ‖ ≤
      ∫ θ in G, ‖g n θ - g (n + 1) θ‖ :=
    norm_integral_le_integral_norm (μ := volume.restrict G)
      (fun θ => g n θ - g (n + 1) θ)
  have hle := setIntegral_mono_on
    ((aux_paired_gaussian_integrable (l := n) (by omega) z).integrableOn.sub
      (aux_paired_gaussian_integrable (l := n + 1) (by omega) z).integrableOn).norm
    hbound hG hpoint
  have hfull := aux_lclt_full_gaussian (d := 4) ((n : ℝ) / 16) (by positivity)
  calc
    ‖∫ θ in G, g n θ - g (n + 1) θ‖ ≤
        ∫ θ in G, ‖g n θ - g (n + 1) θ‖ := hnorm
    _ ≤ ∫ θ in G, 2 / (n : ℝ) *
        Real.exp (-(n : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 16) := hle
    _ ≤ 2 / (n : ℝ) * ∫ θ : Fin 4 → ℝ,
        Real.exp (-(n : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 16) := by
      rw [integral_const_mul]
      have hbase : Integrable (fun θ : Fin 4 → ℝ =>
          Real.exp (-(n : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 16)) := by
        exact (aux_lclt_full_gaussian_integrable (d := 4) ((n : ℝ) / 16) (by positivity)).congr
          (Filter.Eventually.of_forall (fun θ => by ring_nf))
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hbase (by
          filter_upwards with θ
          positivity))
        (by positivity)
    _ = 2 / (n : ℝ) * (Real.pi / ((n : ℝ) / 16)) ^ 2 := by
      have hfull' : ∫ θ : Fin 4 → ℝ,
          Real.exp (-(n : ℝ) * (∑ i : Fin 4, θ i ^ 2) / 16) =
          (Real.pi / ((n : ℝ) / 16)) ^ 2 := by
        calc
          _ = ∫ θ : Fin 4 → ℝ,
              Real.exp (-((n : ℝ) / 16) * (∑ i : Fin 4, θ i ^ 2)) := by
            apply integral_congr_ae
            filter_upwards with θ
            congr 1
            ring_nf
          _ = (Real.pi / ((n : ℝ) / 16)) ^ ((4 : ℝ) / 2) := hfull
          _ = (Real.pi / ((n : ℝ) / 16)) ^ 2 := by norm_num
      rw [hfull']
    _ ≤ 10000 / (n : ℝ) ^ 3 := by
      have hpi2 : Real.pi ^ 2 ≤ (4 : ℝ) ^ 2 :=
        pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 2
      field_simp [ne_of_gt hn0]
      nlinarith [hpi2]

theorem aux_paired_integral_pair {n : ℕ} (hn : 2 ≤ n) (z : Fin 4 → ℤ) :
    ‖((∫ θ in LatticeProb.LocalCLT.torusBox 4,
          aux_paired_fourierIntegrand n z θ) +
        (∫ θ in LatticeProb.LocalCLT.torusBox 4,
          aux_paired_fourierIntegrand (n + 1) z θ)) -
      (((64 * Real.pi ^ 2 / (n : ℝ) ^ 2) *
          Real.exp (-2 * (∑ i : Fin 4, (z i : ℝ) ^ 2) / n) +
        64 * Real.pi ^ 2 / (n + 1 : ℝ) ^ 2 *
          Real.exp (-2 * (∑ i : Fin 4, (z i : ℝ) ^ 2) / (n + 1)) : ℝ) : ℂ)‖ ≤
      100000000000000 / (n : ℝ) ^ 3 := by
  let G : Set (Fin 4 → ℝ) := aux_paired_gaussRegion
  let T : Set (Fin 4 → ℝ) := LatticeProb.LocalCLT.torusBox 4
  let B : Set (Fin 4 → ℝ) := {θ | ∀ i, |θ i - Real.pi| ≤ Real.pi / 4}
  let C : (Fin 4 → Bool) → Set (Fin 4 → ℝ) := fun b =>
    {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - Real.pi / 4) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + Real.pi / 4)}
  let R : Set (Fin 4 → ℝ) := T \ (G ∪ ⋃ b, C b)
  let IF : ℕ → ℂ := fun l => ∫ θ in G, aux_paired_fourierIntegrand l z θ
  let IC : ℕ → ℂ := fun l => ∑ b, ∫ θ in C b, aux_paired_fourierIntegrand l z θ
  let IR : ℕ → ℂ := fun l => ∫ θ in R, aux_paired_fourierIntegrand l z θ
  let JG : ℕ → ℂ := fun l => ∫ θ in G, aux_paired_gaussianIntegrand l z θ
  let JU : ℕ → ℂ := fun l => ∫ θ : Fin 4 → ℝ, aux_paired_gaussianIntegrand l z θ
  let σ : ℕ → ℂ := fun l =>
    (-1 : ℂ) ^ l * ∏ k, Complex.exp
      (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I)
  have hsplit : ∀ l : ℕ, 1 ≤ l →
      (∫ θ in T, aux_paired_fourierIntegrand l z θ) =
        IF l + IC l + IR l := by
    intro l hl
    dsimp [IF, IC, IR, G, T, C, R, aux_paired_fourierIntegrand,
      aux_paired_character]
    exact aux_paired_corner_split (d := 4) (n := l) (by norm_num) (Real.pi / 4)
      (by positivity) (by linarith [Real.pi_pos]) z
  have hcorner : ∀ l : ℕ, IC l = σ l * IF l := by
    intro l
    have ha := aux_paired_antipode_corner_assembly (d := 4) (n := l) (Real.pi / 4)
      (by positivity) (by linarith [Real.pi_pos]) z
    calc
      IC l = ∫ θ in B, aux_paired_fourierIntegrand l z θ := by
        simpa [IC, C, B, aux_paired_fourierIntegrand, aux_paired_character] using ha
      _ = σ l * IF l := by
        simpa [σ, IF] using (aux_paired_pi_shift_integral (l := l) z)
  have hσ : σ (n + 1) = -σ n := by
    dsimp [σ]
    rw [pow_succ]
    ring1
  have hσnorm : ‖σ n‖ = 1 := by
    dsimp [σ]
    rw [norm_mul, norm_pow, norm_neg]
    simp [Complex.norm_exp]
  have hcore_num : ∀ {l : ℕ}, 2 ≤ l →
      ‖IF l - JG l‖ ≤ 1000000000000 / (l : ℝ) ^ 3 := by
    intro l hl
    have h := aux_paired_core_error hl z
    have hlr : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
    have hpi2 : Real.pi ^ 2 ≤ (4 : ℝ) ^ 2 :=
      pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 2
    have hfi : IntegrableOn (aux_paired_fourierIntegrand l z)
        aux_paired_gaussRegion volume := by
      apply (aux_paired_fourier_integrable l z).mono_set
      intro θ hθ
      simp only [LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
      constructor
      · intro i
        linarith [(abs_le.mp (hθ i)).1, Real.pi_pos]
      · intro i
        linarith [(abs_le.mp (hθ i)).2, Real.pi_pos]
    have hgi : IntegrableOn (aux_paired_gaussianIntegrand l z)
        aux_paired_gaussRegion volume :=
      (aux_paired_gaussian_integrable (l := l) (by omega) z).integrableOn
    have heq : IF l - JG l =
        ∫ θ in aux_paired_gaussRegion,
          aux_paired_fourierIntegrand l z θ -
            aux_paired_gaussianIntegrand l z θ := by
      rw [integral_sub hfi hgi]
    rw [heq]
    calc
      ‖∫ θ in aux_paired_gaussRegion,
          aux_paired_fourierIntegrand l z θ -
            aux_paired_gaussianIntegrand l z θ‖ ≤
          9216 / (l : ℝ) * (Real.pi / ((l : ℝ) / 192)) ^ 2 := h
      _ ≤ 1000000000000 / (l : ℝ) ^ 3 := by
        field_simp [ne_of_gt hlr]
        nlinarith [hpi2]
  have hmon : ∀ {l : ℕ}, n ≤ l →
      1 / (l : ℝ) ^ 3 ≤ 1 / (n : ℝ) ^ 3 := by
    intro l hnl
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hpow : (n : ℝ) ^ 3 ≤ (l : ℝ) ^ 3 := by
      gcongr
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hcentral : ‖(IF n + IF (n + 1)) - (JG n + JG (n + 1))‖ ≤
      2000000000000 / (n : ℝ) ^ 3 := by
    have hGsub : aux_paired_gaussRegion ⊆ LatticeProb.LocalCLT.torusBox 4 := by
      intro θ hθ
      simp only [LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
      constructor
      · intro i
        linarith [(abs_le.mp (hθ i)).1, Real.pi_pos]
      · intro i
        linarith [(abs_le.mp (hθ i)).2, Real.pi_pos]
    have hfiN : IntegrableOn (aux_paired_fourierIntegrand n z) G := by
      apply (aux_paired_fourier_integrable n z).mono_set
      simpa [G] using hGsub
    have hfiN1 : IntegrableOn (aux_paired_fourierIntegrand (n + 1) z) G := by
      apply (aux_paired_fourier_integrable (n + 1) z).mono_set
      simpa [G] using hGsub
    have hgiN : IntegrableOn (aux_paired_gaussianIntegrand n z) G := by
      simpa [G] using
        (aux_paired_gaussian_integrable (l := n) (by omega) z).integrableOn
    have hgiN1 : IntegrableOn (aux_paired_gaussianIntegrand (n + 1) z) G := by
      simpa [G] using
        (aux_paired_gaussian_integrable (l := n + 1) (by omega) z).integrableOn
    have heq : (IF n + IF (n + 1)) - (JG n + JG (n + 1)) =
        (IF n - JG n) + (IF (n + 1) - JG (n + 1)) := by
      ring_nf
    rw [heq]
    calc
      ‖(IF n - JG n) + (IF (n + 1) - JG (n + 1))‖ ≤
          ‖IF n - JG n‖ + ‖IF (n + 1) - JG (n + 1)‖ := norm_add_le _ _
      _ ≤ 1000000000000 / (n : ℝ) ^ 3 +
          1000000000000 / (n : ℝ) ^ 3 := by
        gcongr
        · exact hcore_num hn
        · exact (hcore_num (show 2 ≤ n + 1 by omega)).trans
            (by gcongr; omega)
      _ = 2000000000000 / (n : ℝ) ^ 3 := by ring_nf
  have hcorner_bound : ‖IC n + IC (n + 1)‖ ≤
      2000000000000 / (n : ℝ) ^ 3 + 10000 / (n : ℝ) ^ 3 := by
    have hdiff : ‖IF n - IF (n + 1)‖ ≤
        2000000000000 / (n : ℝ) ^ 3 + 10000 / (n : ℝ) ^ 3 := by
      have hn1 : 1 ≤ n := by omega
      have hgd := aux_paired_gaussian_difference hn1 z
      have heq : IF n - IF (n + 1) =
          (IF n - JG n) + (JG n - JG (n + 1)) +
            (JG (n + 1) - IF (n + 1)) := by ring_nf
      rw [heq]
      calc
        ‖(IF n - JG n) + (JG n - JG (n + 1)) +
              (JG (n + 1) - IF (n + 1))‖ ≤
            ‖IF n - JG n‖ + ‖JG n - JG (n + 1)‖ +
              ‖JG (n + 1) - IF (n + 1)‖ := by
          calc
            _ ≤ ‖(IF n - JG n) + (JG n - JG (n + 1))‖ +
                ‖JG (n + 1) - IF (n + 1)‖ := norm_add_le _ _
            _ ≤ (‖IF n - JG n‖ + ‖JG n - JG (n + 1)‖) +
                ‖JG (n + 1) - IF (n + 1)‖ :=
              add_le_add (norm_add_le _ _) (le_refl _)
            _ = _ := by ring_nf
        _ ≤ 1000000000000 / (n : ℝ) ^ 3 +
            10000 / (n : ℝ) ^ 3 + 1000000000000 / (n : ℝ) ^ 3 := by
          gcongr
          · exact hcore_num hn
          · have hgd' : ‖JG n - JG (n + 1)‖ ≤ 10000 / (n : ℝ) ^ 3 := by
              have hfi : IntegrableOn (aux_paired_gaussianIntegrand n z) G := by
                simpa [G] using
                  (aux_paired_gaussian_integrable (l := n) (by omega) z).integrableOn
              have hfi1 : IntegrableOn (aux_paired_gaussianIntegrand (n + 1) z) G := by
                simpa [G] using
                  (aux_paired_gaussian_integrable (l := n + 1) (by omega) z).integrableOn
              rw [show JG n - JG (n + 1) =
                ∫ θ in G, aux_paired_gaussianIntegrand n z θ -
                  aux_paired_gaussianIntegrand (n + 1) z θ by
                rw [integral_sub hfi hfi1]]
              exact hgd
            exact hgd'
          · simpa [norm_sub_rev] using (hcore_num (show 2 ≤ n + 1 by omega)).trans
              (by gcongr; omega)
        _ = 2000000000000 / (n : ℝ) ^ 3 + 10000 / (n : ℝ) ^ 3 := by ring_nf
    rw [hcorner n, hcorner (n + 1), hσ]
    calc
      ‖σ n * IF n + -σ n * IF (n + 1)‖ = ‖σ n * (IF n - IF (n + 1))‖ := by ring_nf
      _ = ‖IF n - IF (n + 1)‖ := by rw [norm_mul, hσnorm, one_mul]
      _ ≤ _ := hdiff
  have hres : ‖IR n + IR (n + 1)‖ ≤
      40000000000000 / (n : ℝ) ^ 3 := by
    calc
      ‖IR n + IR (n + 1)‖ ≤ ‖IR n‖ + ‖IR (n + 1)‖ := norm_add_le _ _
      _ ≤ 20000000000000 / (n : ℝ) ^ 3 +
          20000000000000 / (n : ℝ) ^ 3 := by
        gcongr
        · have hn1 : 1 ≤ n := by omega
          exact aux_paired_residual_integral (l := n) hn1 z
        · exact (aux_paired_residual_integral (l := n + 1) (by omega) z).trans
            (by gcongr; omega)
      _ = 40000000000000 / (n : ℝ) ^ 3 := by ring_nf
  have htail : ‖(JG n - JU n) + (JG (n + 1) - JU (n + 1))‖ ≤
      20000000000000 / (n : ℝ) ^ 3 := by
    calc
      ‖(JG n - JU n) + (JG (n + 1) - JU (n + 1))‖ ≤
          ‖JG n - JU n‖ + ‖JG (n + 1) - JU (n + 1)‖ := norm_add_le _ _
      _ ≤ 10000000000000 / (n : ℝ) ^ 3 +
          10000000000000 / (n : ℝ) ^ 3 := by
        gcongr
        · have hn1 : 1 ≤ n := by omega
          exact aux_paired_gaussian_tail hn1 z
        · exact (aux_paired_gaussian_tail (l := n + 1) (by omega) z).trans
            (by gcongr; omega)
      _ = 20000000000000 / (n : ℝ) ^ 3 := by ring_nf
  have hJU : ∀ {l : ℕ}, 1 ≤ l → JU l =
      (((64 * Real.pi ^ 2 / (l : ℝ) ^ 2) *
          Real.exp (-2 * (∑ i : Fin 4, (z i : ℝ) ^ 2) / l) : ℝ) : ℂ) := by
    intro l hl
    have h := aux_lclt_gaussian_fourier_integral (d := 4) (by norm_num) l
      (by omega) z
    dsimp [JU, aux_paired_gaussianIntegrand, aux_paired_character]
    convert h using 1
    all_goals norm_num
    all_goals ring_nf
  have hdecomp :
      ((∫ θ in T, aux_paired_fourierIntegrand n z θ) +
        (∫ θ in T, aux_paired_fourierIntegrand (n + 1) z θ)) -
      (JU n + JU (n + 1)) =
        ((IF n + IF (n + 1)) - (JG n + JG (n + 1))) +
          (IC n + IC (n + 1)) + (IR n + IR (n + 1)) +
          ((JG n - JU n) + (JG (n + 1) - JU (n + 1))) := by
    have hn1 : 1 ≤ n := by omega
    rw [hsplit n hn1, hsplit (n + 1) (by omega)]
    ring_nf
  have hmain :
      (((64 * Real.pi ^ 2 / (n : ℝ) ^ 2) *
          Real.exp (-2 * (∑ i : Fin 4, (z i : ℝ) ^ 2) / n) +
        64 * Real.pi ^ 2 / (n + 1 : ℝ) ^ 2 *
          Real.exp (-2 * (∑ i : Fin 4, (z i : ℝ) ^ 2) / (n + 1)) : ℝ) : ℂ) =
        JU n + JU (n + 1) := by
    rw [hJU (by omega), hJU (by omega)]
    rw [← Complex.ofReal_add]
    congr 1
    norm_num
  rw [hmain]
  change ‖((∫ θ in T, aux_paired_fourierIntegrand n z θ) +
    (∫ θ in T, aux_paired_fourierIntegrand (n + 1) z θ)) -
    (JU n + JU (n + 1))‖ ≤ _
  rw [hdecomp]
  calc
    ‖((IF n + IF (n + 1)) - (JG n + JG (n + 1))) +
          (IC n + IC (n + 1)) + (IR n + IR (n + 1)) +
          ((JG n - JU n) + (JG (n + 1) - JU (n + 1)))‖ ≤
        ‖(IF n + IF (n + 1)) - (JG n + JG (n + 1))‖ +
          ‖IC n + IC (n + 1)‖ + ‖IR n + IR (n + 1)‖ +
          ‖(JG n - JU n) + (JG (n + 1) - JU (n + 1))‖ := by
      calc
        _ ≤ ‖((IF n + IF (n + 1)) - (JG n + JG (n + 1))) +
              (IC n + IC (n + 1)) + (IR n + IR (n + 1))‖ +
              ‖(JG n - JU n) + (JG (n + 1) - JU (n + 1))‖ := norm_add_le _ _
        _ ≤ (‖((IF n + IF (n + 1)) - (JG n + JG (n + 1))) +
              (IC n + IC (n + 1))‖ + ‖IR n + IR (n + 1)‖) +
              ‖(JG n - JU n) + (JG (n + 1) - JU (n + 1))‖ :=
            add_le_add (norm_add_le _ _) (le_refl _)
        _ ≤ ((‖(IF n + IF (n + 1)) - (JG n + JG (n + 1))‖ +
              ‖IC n + IC (n + 1)‖) + ‖IR n + IR (n + 1)‖) +
              ‖(JG n - JU n) + (JG (n + 1) - JU (n + 1))‖ :=
            add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)
        _ = _ := by ring_nf
    _ ≤ 100000000000000 / (n : ℝ) ^ 3 := by
      calc
        _ ≤ 2000000000000 / (n : ℝ) ^ 3 +
            (2000000000000 / (n : ℝ) ^ 3 + 10000 / (n : ℝ) ^ 3) +
            40000000000000 / (n : ℝ) ^ 3 +
            20000000000000 / (n : ℝ) ^ 3 := by
          exact add_le_add (add_le_add (add_le_add hcentral hcorner_bound) hres) htail
        _ ≤ 100000000000000 / (n : ℝ) ^ 3 := by
          calc
            _ = 64000000010000 / (n : ℝ) ^ 3 := by ring_nf
            _ ≤ 100000000000000 / (n : ℝ) ^ 3 := by
              gcongr
              norm_num
-- FROZEN-STATEMENT-BEGIN
/-- The dimension-four paired local limit estimate, proved rather than assumed. -/
theorem Sandpile.External.pairedLocalCLTFour : Sandpile.External.PairedLocalCLTFour
-- FROZEN-STATEMENT-END
:= by
  refine ⟨1000000000000000, by norm_num, ?_⟩
  intro n hn x y
  by_cases hn2 : 2 ≤ n
  · let z : Fin 4 → ℤ := x - y
    let S : ℝ := ∑ i : Fin 4, (z i : ℝ) ^ 2
    have hS : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hp := aux_paired_integral_pair hn2 z
    have hinvN := aux_lclt_fourier_inversion (d := 4) (by norm_num) n x y
    have hinvN1 := aux_lclt_fourier_inversion (d := 4) (by norm_num) (n + 1) x y
    have hInt : ∀ l : ℕ,
        (∫ θ in LatticeProb.LocalCLT.torusBox 4,
            (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
              ((∑ i : Fin 4, Real.cos (θ i)) / 4) ^ l) =
          ∫ θ in LatticeProb.LocalCLT.torusBox 4,
            aux_paired_fourierIntegrand l z θ := by
      intro l
      apply integral_congr_ae
      filter_upwards with θ
      dsimp [aux_paired_fourierIntegrand, aux_paired_character]
      norm_num [Complex.ofReal_div, Complex.ofReal_pow]
    have hInt' : ∀ l : ℕ,
        (∫ θ in LatticeProb.LocalCLT.torusBox 4,
            (∏ k, Complex.exp (Complex.ofReal (θ k * (((x - y) k : ℤ) : ℝ)) * Complex.I)) *
              ((∑ i : Fin 4, Real.cos (θ i)) / 4) ^ l) =
          ∫ θ in LatticeProb.LocalCLT.torusBox 4,
            aux_paired_fourierIntegrand l z θ := by
      intro l
      simpa [z] using hInt l
    have hInt'' : ∀ l : ℕ,
        (∫ θ in LatticeProb.LocalCLT.torusBox 4,
            (∏ k, Complex.exp (Complex.ofReal (θ k * (((x - y) k : ℤ) : ℝ)) * Complex.I)) *
              ((∑ i : Fin 4, Real.cos (θ i)) / (4 : ℂ)) ^ l) =
          ∫ θ in LatticeProb.LocalCLT.torusBox 4,
            aux_paired_fourierIntegrand l z θ := by
      intro l
      convert hInt' l using 1
    have hN :
        (∫ θ in LatticeProb.LocalCLT.torusBox 4,
            (∏ k, Complex.exp ((θ k : ℂ) * ((x k : ℂ) - (y k : ℂ)) * Complex.I)) *
              (((∑ i : Fin 4, Real.cos (θ i)) / 4 : ℝ) : ℂ) ^ n) =
          ∫ θ in LatticeProb.LocalCLT.torusBox 4,
            aux_paired_fourierIntegrand n z θ := by
      convert hInt' n using 1
      all_goals norm_num
    have hN1 :
        (∫ θ in LatticeProb.LocalCLT.torusBox 4,
            (∏ k, Complex.exp ((θ k : ℂ) * ((x k : ℂ) - (y k : ℂ)) * Complex.I)) *
              (((∑ i : Fin 4, Real.cos (θ i)) / 4 : ℝ) : ℂ) ^ (n + 1)) =
          ∫ θ in LatticeProb.LocalCLT.torusBox 4,
            aux_paired_fourierIntegrand (n + 1) z θ := by
      convert hInt' (n + 1) using 1
      all_goals norm_num
    have hN2 :
        (∫ θ in LatticeProb.LocalCLT.torusBox 4,
            (∏ k, Complex.exp ((θ k : ℂ) * ((x k : ℂ) - (y k : ℂ)) * Complex.I)) *
              ((∑ i : Fin 4, Real.cos (θ i) : ℂ) / 4) ^ n) =
          ∫ θ in LatticeProb.LocalCLT.torusBox 4,
            aux_paired_fourierIntegrand n z θ := by
      convert hN using 1
      all_goals norm_num
    have hN12 :
        (∫ θ in LatticeProb.LocalCLT.torusBox 4,
            (∏ k, Complex.exp ((θ k : ℂ) * ((x k : ℂ) - (y k : ℂ)) * Complex.I)) *
              ((∑ i : Fin 4, Real.cos (θ i) : ℂ) / 4) ^ (n + 1)) =
          ∫ θ in LatticeProb.LocalCLT.torusBox 4,
            aux_paired_fourierIntegrand (n + 1) z θ := by
      convert hN1 using 1
      all_goals norm_num
    have hN3 :
        (∫ θ in LatticeProb.LocalCLT.torusBox 4,
            (∏ k, Complex.exp ((θ k : ℂ) * ((x k : ℂ) - (y k : ℂ)) * Complex.I)) *
              ((∑ i : Fin 4, Complex.cos (θ i)) / 4) ^ n) =
          ∫ θ in LatticeProb.LocalCLT.torusBox 4,
            aux_paired_fourierIntegrand n z θ := by
      simpa only [Complex.ofReal_cos] using hN2
    have hN13 :
        (∫ θ in LatticeProb.LocalCLT.torusBox 4,
            (∏ k, Complex.exp ((θ k : ℂ) * ((x k : ℂ) - (y k : ℂ)) * Complex.I)) *
              ((∑ i : Fin 4, Complex.cos (θ i)) / 4) ^ (n + 1)) =
          ∫ θ in LatticeProb.LocalCLT.torusBox 4,
            aux_paired_fourierIntegrand (n + 1) z θ := by
      simpa only [Complex.ofReal_cos] using hN12
    have hcoef :
        (((4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
              4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) *
                Real.exp (-2 * S / (n + 1)) : ℝ) : ℂ)) =
          (((64 * Real.pi ^ 2 / (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
              64 * Real.pi ^ 2 / (n + 1 : ℝ) ^ 2 *
                Real.exp (-2 * S / (n + 1)) : ℝ) : ℂ) /
            (2 * Real.pi) ^ 4 := by
      norm_num
      field_simp [ne_of_gt Real.pi_pos]
      ring_nf
    have hfour :
        ((Sandpile.heatKernel 4 n x y + Sandpile.heatKernel 4 (n + 1) x y : ℝ) : ℂ) -
            (((4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
              4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) *
                Real.exp (-2 * S / (n + 1)) : ℝ) : ℂ)) =
          (((∫ θ in LatticeProb.LocalCLT.torusBox 4,
              aux_paired_fourierIntegrand n z θ) +
            (∫ θ in LatticeProb.LocalCLT.torusBox 4,
              aux_paired_fourierIntegrand (n + 1) z θ)) -
            (((64 * Real.pi ^ 2 / (n : ℝ) ^ 2) *
                Real.exp (-2 * S / n) +
              64 * Real.pi ^ 2 / (n + 1 : ℝ) ^ 2 *
                Real.exp (-2 * S / (n + 1)) : ℝ) : ℂ)) /
          (2 * Real.pi) ^ 4 := by
      norm_num at hinvN hinvN1
      rw [Complex.ofReal_add, hinvN, hinvN1, hN3, hN13]
      rw [hcoef]
      ring_nf
    have hnormfour :
        ‖((Sandpile.heatKernel 4 n x y + Sandpile.heatKernel 4 (n + 1) x y : ℝ) : ℂ) -
            (((4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
              4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) *
                Real.exp (-2 * S / (n + 1)) : ℝ) : ℂ))‖ ≤
          100000000000000 / (n : ℝ) ^ 3 := by
      rw [hfour, norm_div]
      have hden : 1 ≤ ‖((2 * Real.pi) ^ 4 : ℂ)‖ := by
        norm_num [Complex.normSq, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
        have hbase : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        have hp4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hbase 4
        norm_num at hp4
        exact hp4
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < ‖((2 * Real.pi) ^ 4 : ℂ)‖)).2
        (by
          have := hp
          calc
            ‖((∫ θ in LatticeProb.LocalCLT.torusBox 4,
                aux_paired_fourierIntegrand n z θ) +
              (∫ θ in LatticeProb.LocalCLT.torusBox 4,
                aux_paired_fourierIntegrand (n + 1) z θ)) -
              (((64 * Real.pi ^ 2 / (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
                64 * Real.pi ^ 2 / (n + 1 : ℝ) ^ 2 *
                  Real.exp (-2 * S / (n + 1)) : ℝ) : ℂ)‖ ≤
                100000000000000 / (n : ℝ) ^ 3 := by
              simpa [S, z] using hp
            _ ≤ 100000000000000 / (n : ℝ) ^ 3 *
                ‖((2 * Real.pi) ^ 4 : ℂ)‖ := by
              exact le_mul_of_one_le_right (by positivity) hden)
    have hscalar := aux_paired_scalar_main (n := n) (by omega) S hS
    have htotal :
        |Sandpile.heatKernel 4 n x y + Sandpile.heatKernel 4 (n + 1) x y -
            8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n)| ≤
          1000000000000000 / (n : ℝ) ^ 3 := by
      have hreal :
          |(Sandpile.heatKernel 4 n x y + Sandpile.heatKernel 4 (n + 1) x y) -
              (4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
                4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) *
                  Real.exp (-2 * S / (n + 1)))| ≤
            100000000000000 / (n : ℝ) ^ 3 := by
        have hnormfour' := hnormfour
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hnormfour'
        exact hnormfour'
      calc
        _ ≤ |(Sandpile.heatKernel 4 n x y + Sandpile.heatKernel 4 (n + 1) x y) -
              (4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
                4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) *
                  Real.exp (-2 * S / (n + 1)))| +
            |4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
                4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) *
                  Real.exp (-2 * S / (n + 1)) -
                8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n)| := by
          rw [show (Sandpile.heatKernel 4 n x y + Sandpile.heatKernel 4 (n + 1) x y -
              8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n)) =
            ((Sandpile.heatKernel 4 n x y + Sandpile.heatKernel 4 (n + 1) x y) -
              (4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
                4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) *
                  Real.exp (-2 * S / (n + 1)))) +
              (4 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n) +
                4 / (Real.pi ^ 2 * (n + 1 : ℝ) ^ 2) *
                  Real.exp (-2 * S / (n + 1)) -
                8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) * Real.exp (-2 * S / n)) by ring_nf]
          exact abs_add_le _ _
        _ ≤ 100000000000000 / (n : ℝ) ^ 3 + 1000 / (n : ℝ) ^ 3 :=
          add_le_add hreal hscalar
        _ ≤ 1000000000000000 / (n : ℝ) ^ 3 := by
          calc
            _ = 100000000001000 / (n : ℝ) ^ 3 := by ring_nf
            _ ≤ 1000000000000000 / (n : ℝ) ^ 3 := by
              gcongr
              norm_num
    simpa [S, z] using htotal
  · have hn1 : n = 1 := by omega
    subst n
    have hk0 := Sandpile.heatKernel_nonneg 1 x y
    have hk1 := Sandpile.heatKernel_nonneg 2 x y
    have hk0' := Sandpile.heatKernel_le_one (d := 4) (by norm_num) 1 x y
    have hk1' := Sandpile.heatKernel_le_one (d := 4) (by norm_num) 2 x y
    have he : Real.exp (-2 * (∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2) / 1) ≤ 1 := by
      have hsum : 0 ≤ ∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg _)
      simpa using (Real.exp_le_exp.mpr (show
        -2 * (∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2) / 1 ≤ (0 : ℝ) by
          linarith))
    have hgauss : 0 ≤ 8 / (Real.pi ^ 2 * (1 : ℝ) ^ 2) *
        Real.exp (-2 * (∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2) / 1) := by positivity
    have hgauss' : 8 / (Real.pi ^ 2 * (1 : ℝ) ^ 2) *
        Real.exp (-2 * (∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2) / 1) ≤ 1 := by
      have hp : (0 : ℝ) < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      have hform : (8 * Real.exp (-2 *
          (∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2) / 1)) /
          Real.pi ^ 2 ≤ 1 := by
        apply (div_le_iff₀ hp).2
        nlinarith [Real.pi_gt_three, he]
      norm_num at hform ⊢
      convert hform using 1; ring_nf
    rw [abs_le]
    constructor
    · nlinarith [hk0', hk1', hgauss]
    · nlinarith [hk0, hk1, hgauss']
