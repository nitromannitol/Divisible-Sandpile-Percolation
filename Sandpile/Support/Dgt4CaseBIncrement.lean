import Sandpile.Support.Dgt4CaseBTail
import LatticeProb.Prob.KaramataOrigin

/-!
# From the case (b) estimates to the increment integral

The passage from the two estimates of case (b) of `prop:dgt4-contact-asymptotics` to the
proposition (`sandpile.tex:5328-5336`).

The paper's sentence is: "By \eqref{eq:dgt4-frechet-integrated-tail},
$\P(-\zeta(0)>t)\int_0^t dr/\E(-\zeta(0)-r)_+\to1-1/\alpha$. Since $\E u_{n+1}(0)-\E u_n(0)$ is
asymptotic to $\E(-\zeta(0)-\E u_n(0)/G(0,0))_+\to0$ by \eqref{eq:dgt4-b-mean-increment}, we have
$\E u_{n+1}(0)/\E u_n(0)\to1$, so by regular variation
$\E(-\zeta(0)-r)_+\sim\E(-\zeta(0)-\E u_n(0)/G(0,0))_+$ uniformly for $r$ between
$\E u_n(0)/G(0,0)$ and $\E u_{n+1}(0)/G(0,0)$."

Everything in this module is one-dimensional: `I` is the integrated lower tail
`t \mapsto \E(-\zeta(0)-t)_+`, antitone, positive and regularly varying of index `1-\alpha`, and
`t n` is the level `\E u_n(0)/G(0,0)`. The uniform replacement is Potter's bounds, which the
shared library proves.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

/-- The levels increase from some point on: the increment is asymptotic to a positive
multiple of the positive quantity `I (t n)`. -/
theorem eventually_level_le_succ {I : ℝ → ℝ} {t : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hIpos : ∀ s : ℝ, 0 < I s)
    (h : Tendsto (fun n : ℕ => (t (n + 1) - t n) / I (t n)) atTop (𝓝 c)) :
    ∀ᶠ n in atTop, t n ≤ t (n + 1) := by
  filter_upwards [h.eventually (lt_mem_nhds hc)] with n hn
  have hI := hIpos (t n)
  have hkey : t (n + 1) - t n = ((t (n + 1) - t n) / I (t n)) * I (t n) := by
    field_simp
  nlinarith [mul_pos hn hI, hkey]

/-- `E u_{n+1}(0)/E u_n(0) → 1` (`sandpile.tex:5325`), in the reciprocal form the
Potter comparison consumes: the increment is bounded by the antitone `I`, and the
levels diverge. -/
theorem tendsto_level_ratio_one {I : ℝ → ℝ} {t : ℕ → ℝ} {c : ℝ}
    (hIanti : Antitone I) (hIpos : ∀ s : ℝ, 0 < I s)
    (ht0 : ∀ n : ℕ, 0 ≤ t n) (htinf : Tendsto t atTop atTop)
    (h : Tendsto (fun n : ℕ => (t (n + 1) - t n) / I (t n)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => t n / t (n + 1)) atTop (𝓝 1) := by
  have htp : ∀ᶠ n in atTop, 0 < t n := htinf.eventually_gt_atTop 0
  have hzero : Tendsto (fun n : ℕ => I (t n) / t n) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_
      (Filter.Tendsto.div_atTop (f := fun _ : ℕ => I 0) tendsto_const_nhds htinf)
    · exact div_nonneg (hIpos _).le (ht0 n)
    · filter_upwards [htinf.eventually_ge_atTop 0, htp] with n hn hn0
      exact div_le_div_of_nonneg_right (hIanti hn) hn0.le
  have hq : Tendsto (fun n : ℕ => (t (n + 1) - t n) / t n) atTop (𝓝 0) := by
    have hmul := h.mul hzero
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [htp] with n hn
    have hI := (hIpos (t n)).ne'
    field_simp
  have hr : Tendsto (fun n : ℕ => t (n + 1) / t n) atTop (𝓝 1) := by
    have hadd := (tendsto_const_nhds (α := ℕ) (f := atTop) (x := (1 : ℝ))).add hq
    rw [add_zero] at hadd
    refine hadd.congr' ?_
    filter_upwards [htp] with n hn
    field_simp
    ring
  have hinv := hr.inv₀ one_ne_zero
  rw [inv_one] at hinv
  exact hinv.congr fun n => inv_div _ _

/-- The uniform replacement of `sandpile.tex:5326-5328`: a regularly varying antitone
function takes asymptotically equal values at two levels whose ratio tends to one.
This is Potter's bounds, `LatticeProb.potter_bounds_pos`. -/
theorem tendsto_tail_ratio_one {I : ℝ → ℝ} {ρ : ℝ} {t : ℕ → ℝ}
    (hIanti : Antitone I) (hIpos : ∀ s : ℝ, 0 < I s)
    (hIrv : LatticeProb.RegularlyVaryingAtTop I ρ)
    (hmono : ∀ᶠ n in atTop, t n ≤ t (n + 1))
    (htinf : Tendsto t atTop atTop)
    (hu : Tendsto (fun n : ℕ => t n / t (n + 1)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => I (t n) / I (t (n + 1))) atTop (𝓝 1) := by
  have hIev : ∀ᶠ r in atTop, 0 < I r := Eventually.of_forall hIpos
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hmono] with n hn
    have h1 : I (t (n + 1)) ≤ I (t n) := hIanti hn
    have h2 : 0 < I (t (n + 1)) := hIpos _
    have h3 : 1 ≤ I (t n) / I (t (n + 1)) := (one_le_div h2).mpr h1
    linarith
  · intro a ha
    set δ : ℝ := (a - 1) / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; linarith
    obtain ⟨r₀, hr₀, hP⟩ := LatticeProb.potter_bounds_pos hIrv hIanti hIev δ hδ
    have hu1 : Tendsto (fun n : ℕ => (t n / t (n + 1)) ^ (ρ + δ)) atTop (𝓝 1) := by
      simpa using hu.rpow_const (Or.inl one_ne_zero)
    have hu2 : Tendsto (fun n : ℕ => (t n / t (n + 1)) ^ (ρ - δ)) atTop (𝓝 1) := by
      simpa using hu.rpow_const (Or.inl one_ne_zero)
    have hmaxx : Tendsto (fun n : ℕ =>
        max ((t n / t (n + 1)) ^ (ρ + δ)) ((t n / t (n + 1)) ^ (ρ - δ))) atTop (𝓝 1) := by
      simpa using hu1.max hu2
    have hmax : Tendsto (fun n : ℕ => (1 + δ) *
        max ((t n / t (n + 1)) ^ (ρ + δ)) ((t n / t (n + 1)) ^ (ρ - δ))) atTop (𝓝 ((1 + δ) * 1)) :=
      tendsto_const_nhds.mul hmaxx
    rw [mul_one] at hmax
    have hlt : 1 + δ < a := by rw [hδdef]; linarith
    filter_upwards [hmax.eventually (gt_mem_nhds hlt), htinf.eventually_ge_atTop r₀,
      (htinf.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop r₀] with n hn hr1 hr2
    exact lt_of_le_of_lt (hP (t (n + 1)) (t n) hr2 hr1) hn

/-- The reciprocal of an antitone positive function is monotone and nonnegative, hence
integrable on every `Ioc 0 T`. -/
theorem integrableOn_inv_Ioc {I : ℝ → ℝ} (hIanti : Antitone I) (hIpos : ∀ s : ℝ, 0 < I s)
    (T : ℝ) : IntegrableOn (fun r => (I r)⁻¹) (Ioc 0 T) := by
  refine LatticeProb.integrableOn_Ioc_of_monotone_nonneg ?_ ?_ T
  · intro x y hxy
    exact inv_anti₀ (hIpos y) (hIanti hxy)
  · intro r
    exact (inv_pos.mpr (hIpos r)).le

/-- Splitting `\int_0^{t_{n+1}}` at `t_n`. -/
theorem integral_Ioc_sub_Ioc {I : ℝ → ℝ} (hIanti : Antitone I) (hIpos : ∀ s : ℝ, 0 < I s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ r in Ioc (0 : ℝ) b, (I r)⁻¹) - ∫ r in Ioc (0 : ℝ) a, (I r)⁻¹
      = ∫ r in Ioc a b, (I r)⁻¹ := by
  have hint : IntegrableOn (fun r => (I r)⁻¹) (Ioc (0 : ℝ) b) := integrableOn_inv_Ioc hIanti hIpos b
  have h1 : IntegrableOn (fun r => (I r)⁻¹) (Ioc (0 : ℝ) a) :=
    hint.mono_set (Ioc_subset_Ioc_right hab)
  have h2 : IntegrableOn (fun r => (I r)⁻¹) (Ioc a b) :=
    hint.mono_set (Ioc_subset_Ioc_left ha)
  have hdisj : Disjoint (Ioc (0 : ℝ) a) (Ioc a b) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx'.1 (not_lt.mpr hx.2)
  have hun : Ioc (0 : ℝ) a ∪ Ioc a b = Ioc (0 : ℝ) b := Set.Ioc_union_Ioc_eq_Ioc ha hab
  have hsplit := MeasureTheory.setIntegral_union hdisj measurableSet_Ioc h1 h2
  rw [hun] at hsplit
  rw [hsplit]
  ring

/-- The two-sided bound on one increment of `\int_0^t dr/\E(-\zeta(0)-r)_+`, from the
monotonicity of the integrand alone. -/
theorem integral_Ioc_inv_bounds {I : ℝ → ℝ} (hIanti : Antitone I) (hIpos : ∀ s : ℝ, 0 < I s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) * (I a)⁻¹ ≤ (∫ r in Ioc a b, (I r)⁻¹) ∧
      (∫ r in Ioc a b, (I r)⁻¹) ≤ (b - a) * (I b)⁻¹ := by
  have h2 : IntegrableOn (fun r => (I r)⁻¹) (Ioc a b) :=
    (integrableOn_inv_Ioc hIanti hIpos b).mono_set (Ioc_subset_Ioc_left ha)
  have hvol : volume.real (Ioc a b) = b - a := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  have hconst : ∀ c : ℝ, (∫ _r in Ioc a b, c) = (b - a) * c := by
    intro c
    rw [setIntegral_const, smul_eq_mul, hvol]
  have hcint : ∀ c : ℝ, IntegrableOn (fun _ : ℝ => c) (Ioc a b) := fun c =>
    integrableOn_const measure_Ioc_lt_top.ne (by simp)
  refine ⟨?_, ?_⟩
  · rw [← hconst ((I a)⁻¹)]
    refine setIntegral_mono_on (hcint _) h2 measurableSet_Ioc fun x hx => ?_
    exact inv_anti₀ (hIpos x) (hIanti hx.1.le)
  · rw [← hconst ((I b)⁻¹)]
    refine setIntegral_mono_on h2 (hcint _) measurableSet_Ioc fun x hx => ?_
    exact inv_anti₀ (hIpos b) (hIanti hx.2)

/-- The display after `eq:dgt4-b-mean-increment` (`sandpile.tex:5329`):
`\int_{\E u_n(0)/G(0,0)}^{\E u_{n+1}(0)/G(0,0)}dr/\E(-\zeta(0)-r)_+\to1/G(0,0)`. -/
theorem tendsto_recip_integral_increment {I : ℝ → ℝ} {t : ℕ → ℝ} {c : ℝ}
    (hIanti : Antitone I) (hIpos : ∀ s : ℝ, 0 < I s)
    (ht0 : ∀ n : ℕ, 0 ≤ t n) (hmono : ∀ᶠ n in atTop, t n ≤ t (n + 1))
    (hratio : Tendsto (fun n : ℕ => I (t n) / I (t (n + 1))) atTop (𝓝 1))
    (h : Tendsto (fun n : ℕ => (t (n + 1) - t n) / I (t n)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (∫ r in Ioc (0 : ℝ) (t (n + 1)), (I r)⁻¹) -
        ∫ r in Ioc (0 : ℝ) (t n), (I r)⁻¹) atTop (𝓝 c) := by
  have hlow : Tendsto (fun n : ℕ => (t (n + 1) - t n) * (I (t n))⁻¹) atTop (𝓝 c) :=
    h.congr fun n => (div_eq_mul_inv _ _)
  have hup : Tendsto (fun n : ℕ => (t (n + 1) - t n) * (I (t (n + 1)))⁻¹) atTop (𝓝 c) := by
    have hmul := h.mul hratio
    rw [mul_one] at hmul
    refine hmul.congr fun n => ?_
    have h1 := (hIpos (t n)).ne'
    have h2 := (hIpos (t (n + 1))).ne'
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [hmono] with n hn
    rw [integral_Ioc_sub_Ioc hIanti hIpos (ht0 n) hn]
    exact (integral_Ioc_inv_bounds hIanti hIpos (ht0 n) hn).1
  · filter_upwards [hmono] with n hn
    rw [integral_Ioc_sub_Ioc hIanti hIpos (ht0 n) hn]
    exact (integral_Ioc_inv_bounds hIanti hIpos (ht0 n) hn).2

end Sandpile
