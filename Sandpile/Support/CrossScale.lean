/-
The crossing scale `b(s)` of `sandpile.tex:2089-2098` and the dilation of a
planar crossing, which is the deterministic half of the rescaled crossing
estimate `sandpile.tex:2394-2402`:

  "Observe that [the fixed-scale proposition] and [the field scaling] imply
   that, for all `a>0` and `h>0`, there is `p>0` such that for every `L ≥ 1`,
   there is `s_0 = s_0(a,h,L) ∈ (0,1]` such that
   `P(H_{[-a,a]×[0,2h]}(L b(s); 𝒳_s)) ≥ p` for every `0 < s < s_0`.
   Indeed, if `R = h/s`, then the event in [that display] has the same
   probability as `H_{[-(a/h)R,(a/h)R]×[0,2R]}(Lh/R)`."

The change of variables is `u ↦ u/s`, which carries `[-a,a]×[0,2h]` to
`[-(a/h)R,(a/h)R]×[0,2R]` with `R = h/s`, and the level `L b(s)` for `𝒳_s` to
the level `L b(s) / κ(s)` for `𝒳_1`, where `κ(s)` is the factor of the field
scaling: `κ(s) = s` in dimension two and `κ(s) = √s` in dimension three.  In
both dimensions `b(s)/κ(s) = s = h/R`, which is why one and the same level
`Lh/R` appears.  What is recorded here is the deterministic content: a crossing
survives a dilation of the plane, and survives multiplication of the field and
the level by a common positive factor.
-/
import Sandpile.Support.CrossTranslate

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- `b(s)` of `sandpile.tex:2089-2098`: `s²` in dimension two, `s^{3/2}` in
dimension three. -/
noncomputable def crossScale (d : ℕ) (s : ℝ) : ℝ :=
  if d = 2 then s ^ 2 else s ^ (3 / 2 : ℝ)

theorem crossScale_pos {d : ℕ} {s : ℝ} (hs : 0 < s) : 0 < crossScale d s := by
  unfold crossScale
  split_ifs with h
  · positivity
  · exact Real.rpow_pos_of_pos hs _

/-- The field-scaling factor `κ(s)` of `sandpile.tex:2105-2112`: `s` in
dimension two, `√s` in dimension three. -/
noncomputable def fieldScale (d : ℕ) (s : ℝ) : ℝ :=
  if d = 2 then s else Real.sqrt s

theorem fieldScale_pos {d : ℕ} {s : ℝ} (hs : 0 < s) : 0 < fieldScale d s := by
  unfold fieldScale
  split_ifs with h
  · exact hs
  · exact Real.sqrt_pos.mpr hs

/-- `b(s) = κ(s) · s` in both dimensions: this is why the rescaled estimate is
at the single level `L h / R`. -/
theorem crossScale_eq_fieldScale_mul {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) :
    crossScale d s = fieldScale d s * s := by
  rcases hd with rfl | rfl
  · show (if (2 : ℕ) = 2 then s ^ 2 else s ^ (3 / 2 : ℝ))
      = (if (2 : ℕ) = 2 then s else Real.sqrt s) * s
    rw [if_pos rfl, if_pos rfl]
    ring
  · show (if (3 : ℕ) = 2 then s ^ 2 else s ^ (3 / 2 : ℝ))
      = (if (3 : ℕ) = 2 then s else Real.sqrt s) * s
    rw [if_neg (by norm_num), if_neg (by norm_num), Real.sqrt_eq_rpow,
      show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]

/-- A crossing survives a dilation of the plane by a positive factor. -/
theorem crosses_scale {t : ℝ} (ht : 0 < t) {a b : Fin 2 → ℝ} {i : Fin 2}
    {S : Set (Sandpile.Continuum.Space 2)}
    (h : Crosses a b i ((fun u => t • u) ⁻¹' S)) :
    Crosses (fun k => t * a k) (fun k => t * b k) i S := by
  obtain ⟨Γ, hsub, hcomp, hconn, ⟨p, hp, hpa⟩, ⟨q, hq, hqb⟩⟩ := h
  have hcont : Continuous (fun u : Sandpile.Continuum.Space 2 => t • u) :=
    continuous_const_smul t
  refine ⟨(fun u => t • u) '' Γ, ?_, hcomp.image hcont,
    hconn.image _ hcont.continuousOn, ⟨t • p, ⟨p, hp, rfl⟩, ?_⟩,
    ⟨t • q, ⟨q, hq, rfl⟩, ?_⟩⟩
  · rintro w ⟨u, huΓ, rfl⟩
    obtain ⟨h1, h2⟩ := hsub huΓ
    refine ⟨h1, ?_⟩
    intro k
    have hk := h2 k
    simp only [PiLp.smul_apply, smul_eq_mul]
    constructor
    · nlinarith [hk.1]
    · nlinarith [hk.2]
  · simp only [PiLp.smul_apply, smul_eq_mul, hpa]
  · simp only [PiLp.smul_apply, smul_eq_mul, hqb]

/-- A crossing survives multiplication of the field and the level by a common
positive factor. -/
theorem crosses_mul_level {t : ℝ} (ht : 0 < t) {a b : Fin 2 → ℝ} {i : Fin 2}
    {f : Sandpile.Continuum.Space 2 → ℝ} {l : ℝ}
    (h : Crosses a b i {u | l ≤ f u}) :
    Crosses a b i {u | t * l ≤ t * f u} :=
  crosses_of_le_on (fun _ _ hu => mul_le_mul_of_nonneg_left hu ht.le) h

/-- The deterministic half of the rescaled crossing estimate
`sandpile.tex:2394-2402`.  Writing `𝒳_s(u) = κ(s)·𝒳_1(u/s)`, a crossing of
`[-A/s, A/s] × [0, 2h/s]` by `{𝒳_1 ≥ L s}` is a crossing of `[-A,A] × [0,2h]` by
`{𝒳_s ≥ L b(s)}`.  With `R = h/s` the first rectangle is
`[-(A/h)R, (A/h)R] × [0,2R]` and the first level is `L h / R`, which is the
proposition's level at aspect ratio `A/h`. -/
theorem crosses_rescale {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s)
    {A h L : ℝ} {i : Fin 2} {X1 : Sandpile.Continuum.Space 2 → ℝ}
    (hcr : Crosses ![-(A / s), 0] ![A / s, 2 * (h / s)] i {v | L * s ≤ X1 v}) :
    Crosses ![-A, 0] ![A, 2 * h] i
      {u | L * crossScale d s ≤ fieldScale d s * X1 (s⁻¹ • u)} := by
  have hcs := crossScale_eq_fieldScale_mul hd hs
  have hfs := fieldScale_pos (d := d) hs
  have hstep : Crosses ![-(A / s), 0] ![A / s, 2 * (h / s)] i
      ((fun v => s • v) ⁻¹'
        {u | L * crossScale d s ≤ fieldScale d s * X1 (s⁻¹ • u)}) := by
    refine crosses_of_mem_on (fun v _ hv => ?_) hcr
    have hv' : L * s ≤ X1 v := hv
    show L * crossScale d s ≤ fieldScale d s * X1 (s⁻¹ • (s • v))
    rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul, hcs]
    nlinarith [mul_le_mul_of_nonneg_left hv' hfs.le]
  have hmain := crosses_scale hs hstep
  have hA : (fun k => s * (![-(A / s), (0 : ℝ)]) k) = ![-A, 0] := by
    funext k
    fin_cases k
    · show s * (-(A / s)) = -A
      field_simp
    · show s * (0 : ℝ) = 0
      ring
  have hB : (fun k => s * (![A / s, 2 * (h / s)]) k) = ![A, 2 * h] := by
    funext k
    fin_cases k
    · show s * (A / s) = A
      field_simp
    · show s * (2 * (h / s)) = 2 * h
      field_simp
  rwa [hA, hB] at hmain

end Sandpile.Support
