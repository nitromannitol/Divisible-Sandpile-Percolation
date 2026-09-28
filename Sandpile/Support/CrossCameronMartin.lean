import Sandpile.Support.CrossTiltMap
import Sandpile.Support.CrossCubeBlocks
import Sandpile.Support.LimNoiseCoordinates

/-!
# The Cameron--Martin shift of a white noise

The Cameron--Martin shift of Step 3 of `prop:fixed-scale-crossings` (`sandpile.tex:2334-2345`):

  "Let `P_ℓ` be the law obtained by adding the deterministic density `(ℓ/𝔪)dz` on every unit
   cube that the rule can reveal ... Since the unit kernel has mass `𝔪`, the shift raises
   every field value used by the exploration by `ℓ`."

Here the shifted law is the exponential tilt of the white noise by `a 𝒲(k) - a²‖k‖²/2`,
where `k` is the indicator of the shifted region, and the statement proved
(`whiteNoise_tilted_map_shift`) is that under this tilt the WHOLE family `(𝒲(g_t))_t` has
the law of `(𝒲(g_t) + a⟨g_t,k⟩)_t`, for an arbitrary index type. Applied with `g_t` the
ball kernels at the points of the rectangle and `k` the indicator of the revealed region,
`⟨g_t,k⟩ = 𝔪` and the field is raised by `a𝔪` at every point of the rectangle at once.

The proof is the classical one. Split `𝒲(g_t) = (⟨g_t,k⟩/‖k‖²)𝒲(k) + Z_t` where `Z` is
`cmResidual`; the residual family `Z` is jointly Gaussian with `𝒲(k)`
(`isGaussianProcess_cmResidual`) and uncorrelated with it, hence independent of it
(`indepFun_cmResidual`), so the joint law is a product. The tilt is a function of the first
factor alone, so it tilts only that factor (`tilted_prod_left`), where it is the
one-dimensional Cameron--Martin identity `tilted_gaussianReal_zero`. Reassembling
`𝒲(g_t) = (⟨g_t,k⟩/‖k‖²)𝒲(k) + Z_t` turns the shift of the single Gaussian direction into
the shift of every coordinate by `a⟨g_t,k⟩`.
-/

open MeasureTheory ProbabilityTheory
open Sandpile.Continuum
open scoped NNReal ENNReal

namespace Sandpile.Support

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : (Space d → ℝ) → Ω → ℝ}

/-- The residual of the field after removing its component along `k`. -/
private noncomputable def cmResidual (W : (Space d → ℝ) → Ω → ℝ) (k : Space d → ℝ)
    {T : Type} (g : T → (Space d → ℝ)) (t : T) (ω : Ω) : ℝ :=
  W (g t) ω - ((∫ y : Space d, g t y * k y) / (∫ y : Space d, k y * k y)) * W k ω

omit [IsProbabilityMeasure P] in
/-- `cmResidual` is measurable, as a difference of the white noise applied to `g t` and a
constant multiple of the white noise applied to `k`. -/
private theorem measurable_cmResidual (hW : IsWhiteNoise d W P) {k : Space d → ℝ}
    (hk : MemLp k 2 (volume : Measure (Space d))) {T : Type} (g : T → (Space d → ℝ))
    (hg : ∀ t, MemLp (g t) 2 (volume : Measure (Space d))) (t : T) :
    Measurable (cmResidual W k g t) :=
  (hW.meas _ (hg t)).sub (measurable_const.mul (hW.meas _ hk))

omit [IsProbabilityMeasure P] in
/-- The residual family and `𝒲(k)` are jointly Gaussian: every one of them is a fixed linear
combination of two values of the white noise. -/
private theorem isGaussianProcess_cmResidual (hW : IsWhiteNoise d W P) (k : Space d → ℝ)
    {T : Type} (g : T → (Space d → ℝ)) :
    IsGaussianProcess (Sum.elim (fun (_ : Unit) => W k) (cmResidual W k g)) P := by
  classical
  refine hW.gaussian.of_isGaussianProcess ?_
  rintro (_ | t)
  · refine ⟨{k}, ContinuousLinearMap.proj
      (R := ℝ) (φ := fun _ : ({k} : Finset (Space d → ℝ)) => ℝ) ⟨k, by simp⟩, ?_⟩
    intro ω
    simp [Finset.restrict]
  · refine ⟨{g t, k}, (ContinuousLinearMap.proj
      (R := ℝ) (φ := fun _ : ({g t, k} : Finset (Space d → ℝ)) => ℝ) ⟨g t, by simp⟩)
        - ((∫ y : Space d, g t y * k y) / (∫ y : Space d, k y * k y)) •
          (ContinuousLinearMap.proj
            (R := ℝ) (φ := fun _ : ({g t, k} : Finset (Space d → ℝ)) => ℝ) ⟨k, by simp⟩), ?_⟩
    intro ω
    simp [cmResidual, Finset.restrict]

/-- `𝒲(k)` is independent of the residual family. -/
private theorem indepFun_cmResidual (hW : IsWhiteNoise d W P) {k : Space d → ℝ}
    (hk : MemLp k 2 (volume : Measure (Space d))) (hv : ∫ y : Space d, k y * k y ≠ 0)
    {T : Type} (g : T → (Space d → ℝ))
    (hg : ∀ t, MemLp (g t) 2 (volume : Measure (Space d))) :
    IndepFun (fun ω => W k ω) (fun ω => fun t : T => cmResidual W k g t ω) P := by
  have hpair : IndepFun (fun ω => fun _ : Unit => W k ω)
      (fun ω => fun t : T => cmResidual W k g t ω) P := by
    refine (isGaussianProcess_cmResidual hW k g).indepFun_of_covariance_eq_zero
      (fun _ => (hW.meas _ hk).aemeasurable)
      (fun t => (measurable_cmResidual hW hk g hg t).aemeasurable) ?_
    intro _ t
    have hWk : MemLp (W k) 2 P := (hW.gaussian.hasGaussianLaw_eval k).memLp_two
    have hWg : MemLp (W (g t)) 2 P := (hW.gaussian.hasGaussianLaw_eval (g t)).memLp_two
    have hsub : cmResidual W k g t
        = fun ω => W (g t) ω -
            ((∫ y : Space d, g t y * k y) / (∫ y : Space d, k y * k y)) * W k ω := rfl
    rw [covariance_comm, hsub, covariance_fun_sub_left hWg (hWk.const_mul _) hWk,
      covariance_const_mul_left,
      covariance_whiteNoise hW _ _ (hg t) hk, covariance_whiteNoise hW _ _ hk hk,
      div_mul_cancel₀ _ hv, sub_self]
  exact hpair.comp (measurable_pi_apply ()) measurable_id

/-- **The Cameron--Martin shift of a white noise.**  Tilting by `a 𝒲(k) - a²‖k‖²/2` gives the
family `(𝒲(g_t))_t` the law of `(𝒲(g_t) + a⟨g_t,k⟩)_t`. -/
theorem whiteNoise_tilted_map_shift (hW : IsWhiteNoise d W P) {k : Space d → ℝ}
    (hk : MemLp k 2 (volume : Measure (Space d)))
    (hv : 0 < ∫ y : Space d, k y * k y)
    {T : Type} (g : T → (Space d → ℝ))
    (hg : ∀ t, MemLp (g t) 2 (volume : Measure (Space d))) (a : ℝ) :
    (P.tilted (fun ω => a * W k ω - a ^ 2 * (∫ y : Space d, k y * k y) / 2)).map
        (fun ω => fun t : T => W (g t) ω)
      = P.map (fun ω => fun t : T => W (g t) ω + a * ∫ y : Space d, g t y * k y) := by
  classical
  set v : ℝ := ∫ y : Space d, k y * k y with hvdef
  set c : T → ℝ := fun t => ∫ y : Space d, g t y * k y with hcdef
  set Z : T → Ω → ℝ := cmResidual W k g with hZdef
  have hvne : v ≠ 0 := ne_of_gt hv
  have hZmeas : Measurable fun ω => fun t : T => Z t ω :=
    measurable_pi_lambda _ fun t => measurable_cmResidual hW hk g hg t
  have hWkmeas : Measurable (W k) := hW.meas _ hk
  set Φ : Ω → ℝ × (T → ℝ) := fun ω => (W k ω, fun t : T => Z t ω) with hΦdef
  have hΦmeas : Measurable Φ := hWkmeas.prodMk hZmeas
  set Ψ : ℝ × (T → ℝ) → (T → ℝ) := fun p => fun t : T => p.2 t + (c t / v) * p.1 with hΨdef
  have hΨmeas : Measurable Ψ :=
    measurable_pi_lambda _ fun t =>
      ((measurable_pi_apply t).comp measurable_snd).add (measurable_const.mul measurable_fst)
  have hΨΦ : (Ψ ∘ Φ) = fun ω => fun t : T => W (g t) ω := by
    funext ω t
    simp only [Function.comp_apply, hΨdef, hΦdef, hZdef, cmResidual, hcdef, hvdef]
    ring
  -- the tilt is a function of the first coordinate of `Φ`
  set q : ℝ × (T → ℝ) → ℝ := fun p => a * p.1 - a ^ 2 * v / 2 with hqdef
  have hqmeas : Measurable q := (measurable_const.mul measurable_fst).sub measurable_const
  have htiltmap := tilted_map (Φ := Φ) (g := q) P hΦmeas hqmeas
  -- the law of `Φ` is a product
  have hprod : P.map Φ = (P.map (W k)).prod (P.map fun ω => fun t : T => Z t ω) :=
    (indepFun_cmResidual hW hk hvne g hg).map_prod_eq_prod_map_map
      hWkmeas.aemeasurable hZmeas.aemeasurable
  have hgaussk : P.map (W k) = gaussianReal 0 (Real.toNNReal v) :=
    map_whiteNoise_eq_gaussianReal W P hW k hk
  have hcoe : ((Real.toNNReal v : ℝ≥0) : ℝ) = v := Real.coe_toNNReal v hv.le
  have htiltk : (P.map (W k)).tilted (fun y : ℝ => a * y - a ^ 2 * v / 2)
      = (P.map (W k)).map (fun y : ℝ => y + a * v) := by
    rw [hgaussk, gaussianReal_map_add_const]
    have hnn : Real.toNNReal v ≠ 0 := by
      intro hzero
      rw [hzero] at hcoe
      simp only [NNReal.coe_zero] at hcoe
      exact absurd hcoe.symm (ne_of_gt hv)
    have h := tilted_gaussianReal_zero (Real.toNNReal v) hnn a
    rw [hcoe] at h
    rw [h]
    norm_num
  -- assemble
  have hstep : (P.map Φ).tilted q = (P.map Φ).map (Prod.map (fun y : ℝ => y + a * v) id) := by
    rw [hprod]
    haveI : IsProbabilityMeasure (P.map (W k)) :=
      Measure.isProbabilityMeasure_map hWkmeas.aemeasurable
    haveI : IsProbabilityMeasure (P.map fun ω => fun t : T => Z t ω) :=
      Measure.isProbabilityMeasure_map hZmeas.aemeasurable
    rw [hqdef, tilted_prod_left (g := fun y : ℝ => a * y - a ^ 2 * v / 2) _ _ (by fun_prop),
      htiltk, ← Measure.map_id (μ := P.map fun ω => fun t : T => Z t ω),
      Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]
  have hmain : (P.tilted (fun ω => q (Φ ω))).map Φ
      = (P.map Φ).map (Prod.map (fun y : ℝ => y + a * v) id) := by
    rw [htiltmap, hstep]
  calc (P.tilted (fun ω => a * W k ω - a ^ 2 * v / 2)).map (fun ω => fun t : T => W (g t) ω)
      = ((P.tilted (fun ω => q (Φ ω))).map Φ).map Ψ := by
        rw [Measure.map_map hΨmeas hΦmeas, hΨΦ]
    _ = ((P.map Φ).map (Prod.map (fun y : ℝ => y + a * v) id)).map Ψ := by rw [hmain]
    _ = P.map (fun ω => fun t : T => W (g t) ω + a * c t) := by
        rw [Measure.map_map hΨmeas (by fun_prop), Measure.map_map (by fun_prop) hΦmeas]
        congr 1
        funext ω t
        simp only [Function.comp_apply, hΨdef, Prod.map, hΦdef, hZdef, cmResidual, hcdef, hvdef,
          id_eq]
        have h2 : (∫ y : Space d, k y ^ 2) = ∫ y : Space d, k y * k y := by
          simp [sq]
        have hv2 : (∫ y : Space d, k y ^ 2) ≠ 0 := by
          rw [h2]
          exact hvdef ▸ hvne
        field_simp
        ring

end Sandpile.Support
