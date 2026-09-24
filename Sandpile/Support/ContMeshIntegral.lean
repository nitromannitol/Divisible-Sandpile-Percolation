/-
The Riemann sums in time of `prop:weighted-membrane-limit`
(`sandpile.tex:4724-4729`): "the local central limit theorem, followed by a
Riemann-sum argument".

The time sums of that proof run over the mesh `R^{-2}ℤ` inside `[0,T]`, and the
Riemann-sum argument is the statement that

  `∑_{a<N} g(a h) h ⟶ ∫_0^T g`  as `h → 0` with `N h → T`.

The proof here writes the Riemann sum as an honest integral: the step function
`r ↦ g(h⌊r/h⌋)` is constant on each mesh interval `[a h, (a+1) h)`, so its
integral over `[0, N h)` is exactly the Riemann sum, and it converges pointwise
to `g` with the uniform bound `‖g‖_∞`.  Dominated convergence then gives the
limit, with no Riemann-integration theory needed.

The mesh point `h⌊r/h⌋` is measurable for EVERY `g`, measurable or not, because
it factors through the floor, which lands in the discrete space `ℤ`; that is why
no measurability hypothesis appears in `integral_meshFloor_eq_sum`.
-/
import Mathlib

open MeasureTheory Filter Topology

namespace Sandpile.Support

/-- The left endpoint `h⌊r/h⌋` of the mesh interval of width `h` containing `r`. -/
noncomputable def meshFloor (h r : ℝ) : ℝ := h * ⌊r / h⌋

/-- The mesh point of `r` is within `h` of `r`. -/
theorem abs_meshFloor_sub_le {h : ℝ} (hh : 0 < h) (r : ℝ) :
    |meshFloor h r - r| ≤ h := by
  have hne : h ≠ 0 := ne_of_gt hh
  have h1 : ((⌊r / h⌋ : ℤ) : ℝ) ≤ r / h := Int.floor_le (r / h)
  have h2 : r / h - 1 < ((⌊r / h⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor (r / h)
  have key : meshFloor h r - r = h * (((⌊r / h⌋ : ℤ) : ℝ) - r / h) := by
    unfold meshFloor
    field_simp
  rw [key, abs_mul, abs_of_pos hh]
  have hb : |((⌊r / h⌋ : ℤ) : ℝ) - r / h| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith [abs_nonneg (((⌊r / h⌋ : ℤ) : ℝ) - r / h)]

/-- On the mesh interval `[a h, (a+1) h)` the mesh point is `a h`. -/
theorem meshFloor_eq_of_mem_Ico {h : ℝ} (hh : 0 < h) (a : ℕ) {r : ℝ}
    (hr : r ∈ Set.Ico ((a : ℝ) * h) (((a : ℝ) + 1) * h)) :
    meshFloor h r = (a : ℝ) * h := by
  obtain ⟨hlo, hhi⟩ := hr
  have hfloor : ⌊r / h⌋ = (a : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hh]
      push_cast
      linarith
    · rw [div_lt_iff₀ hh]
      push_cast
      linarith
  unfold meshFloor
  rw [hfloor]
  push_cast
  ring

/-- The mesh intervals of width `h` below `N h` cover `[0, N h)`. -/
theorem Ico_eq_biUnion_mesh {h : ℝ} (hh : 0 < h) (N : ℕ) :
    Set.Ico (0 : ℝ) ((N : ℝ) * h)
      = ⋃ a ∈ Finset.range N, Set.Ico ((a : ℝ) * h) (((a : ℝ) + 1) * h) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have h0 : (0 : ℝ) ≤ (N : ℝ) * h := by positivity
      have h1 : (N : ℝ) * h ≤ ((N : ℝ) + 1) * h := by nlinarith
      rw [Finset.range_add_one, Finset.set_biUnion_insert, ← ih]
      push_cast
      rw [Set.union_comm, Set.Ico_union_Ico_eq_Ico h0 h1]

/-- Reading any function at the mesh points is measurable: the mesh point
factors through the floor, which lands in a discrete space. -/
theorem measurable_meshFloor_comp (h : ℝ) (g : ℝ → ℝ) :
    Measurable (fun r : ℝ => g (meshFloor h r)) :=
  (Measurable.of_discrete (f := fun n : ℤ => g (h * (n : ℝ)))).comp
    (Int.measurable_floor.comp (measurable_id.div_const h))


/-- Distinct mesh intervals are disjoint. -/
theorem mesh_Ico_disjoint {h : ℝ} (hh : 0 < h) {a b : ℕ} (hab : a ≠ b) :
    Disjoint (Set.Ico ((a : ℝ) * h) (((a : ℝ) + 1) * h))
      (Set.Ico ((b : ℝ) * h) (((b : ℝ) + 1) * h)) := by
  rw [Set.Ico_disjoint_Ico]
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have h1 : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    have h2 : ((a : ℝ) + 1) * h ≤ (b : ℝ) * h := by nlinarith
    calc min (((a : ℝ) + 1) * h) (((b : ℝ) + 1) * h) ≤ ((a : ℝ) + 1) * h := min_le_left _ _
      _ ≤ (b : ℝ) * h := h2
      _ ≤ max ((a : ℝ) * h) ((b : ℝ) * h) := le_max_right _ _
  · have h1 : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    have h2 : ((b : ℝ) + 1) * h ≤ (a : ℝ) * h := by nlinarith
    calc min (((a : ℝ) + 1) * h) (((b : ℝ) + 1) * h) ≤ ((b : ℝ) + 1) * h := min_le_right _ _
      _ ≤ (a : ℝ) * h := h2
      _ ≤ max ((a : ℝ) * h) ((b : ℝ) * h) := le_max_left _ _

/-- The step function is integrable on each mesh interval, where it is
constant. -/
theorem integrableOn_meshFloor_Ico {h : ℝ} (hh : 0 < h) (a : ℕ) (g : ℝ → ℝ) :
    IntegrableOn (fun r => g (meshFloor h r))
      (Set.Ico ((a : ℝ) * h) (((a : ℝ) + 1) * h)) := by
  have hc : IntegrableOn (fun _ : ℝ => g ((a : ℝ) * h))
      (Set.Ico ((a : ℝ) * h) (((a : ℝ) + 1) * h)) :=
    integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  exact hc.congr_fun (fun r hr => by rw [meshFloor_eq_of_mem_Ico hh a hr]) measurableSet_Ico

/-- **The Riemann sum is an integral.**  The step function that reads `g` at the
mesh points integrates over `[0, N h)` to the Riemann sum `∑_{a<N} g(a h) h`. -/
theorem integral_meshFloor_eq_sum {h : ℝ} (hh : 0 < h) (N : ℕ) (g : ℝ → ℝ) :
    ∫ r in Set.Ico (0 : ℝ) ((N : ℝ) * h), g (meshFloor h r)
      = ∑ a ∈ Finset.range N, g ((a : ℝ) * h) * h := by
  classical
  rw [Ico_eq_biUnion_mesh hh N,
    MeasureTheory.integral_biUnion_finset (Finset.range N)
      (fun a _ => measurableSet_Ico)
      (fun a _ b _ hab => mesh_Ico_disjoint hh hab)
      (fun a _ => integrableOn_meshFloor_Ico hh a g)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hEq : ∫ r in Set.Ico ((a : ℝ) * h) (((a : ℝ) + 1) * h), g (meshFloor h r)
      = ∫ _r in Set.Ico ((a : ℝ) * h) (((a : ℝ) + 1) * h), g ((a : ℝ) * h) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ico
      (fun r hr => by rw [meshFloor_eq_of_mem_Ico hh a hr])
  have hle : (a : ℝ) * h ≤ ((a : ℝ) + 1) * h := by nlinarith
  rw [hEq, MeasureTheory.setIntegral_const, Real.volume_real_Ico_of_le hle, smul_eq_mul]
  ring


/-- **The Riemann sums of a bounded continuous function converge to its
integral.**  This is the analytic content of the Riemann-sum argument of
`sandpile.tex:4719-4724`, proved by dominated convergence. -/
theorem tendsto_integral_meshFloor {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (H : ι → ℝ) (hH0 : ∀ᶠ i in l, 0 < H i) (hH : Tendsto H l (𝓝 0))
    (T : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (M : ℝ) (hM : ∀ r, |g r| ≤ M) :
    Tendsto (fun i => ∫ r in Set.Ico (0 : ℝ) T, g (meshFloor (H i) r)) l
      (𝓝 (∫ r in Set.Ico (0 : ℝ) T, g r)) := by
  have hmesh : ∀ r : ℝ, Tendsto (fun i => meshFloor (H i) r) l (𝓝 r) := by
    intro r
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' ?_ hH
    filter_upwards [hH0] with i hi
    simpa using abs_meshFloor_sub_le hi r
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    (Filter.Eventually.of_forall fun i =>
      (measurable_meshFloor_comp (H i) g).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun i =>
      Filter.Eventually.of_forall fun r => by simpa using hM (meshFloor (H i) r))
    ?_ ?_
  · exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  · exact Filter.Eventually.of_forall fun r => (hg.tendsto r).comp (hmesh r)

/-! ### Two dimensions, and the change of endpoint -/

/-- Changing the right endpoint of the interval changes the integral of a
bounded measurable function by at most the change in length times the bound.
This is the error the horizon `⌊R^2T⌋/R^2` makes against `T`. -/
theorem abs_integral_Ico_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (F : ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hM : ∀ r, |F r| ≤ M) :
    |(∫ r in Set.Ico (0 : ℝ) b, F r) - ∫ r in Set.Ico (0 : ℝ) a, F r| ≤ M * (b - a) := by
  have hbdd : ∀ s : Set ℝ, volume s ≠ ⊤ → IntegrableOn F s volume := fun s hs =>
    MeasureTheory.Measure.integrableOn_of_bounded hs hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hM x)
  have hfin1 : volume (Set.Ico (0 : ℝ) a) ≠ ⊤ := by
    rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  have hfin2 : volume (Set.Ico a b) ≠ ⊤ := by
    rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  have hdisj : Disjoint (Set.Ico (0 : ℝ) a) (Set.Ico a b) := by
    rw [Set.Ico_disjoint_Ico]
    simp [min_eq_left hab]
  have hcover : Set.Ico (0 : ℝ) a ∪ Set.Ico a b = Set.Ico (0 : ℝ) b :=
    Set.Ico_union_Ico_eq_Ico ha hab
  rw [← hcover, MeasureTheory.setIntegral_union hdisj measurableSet_Ico (hbdd _ hfin1) (hbdd _ hfin2)]
  have hb := MeasureTheory.norm_setIntegral_le_of_norm_le_const (f := F)
    (s := Set.Ico a b) (μ := volume) (C := M) (lt_top_iff_ne_top.mpr hfin2)
    (fun x _ => by simpa using hM x)
  rw [Real.volume_real_Ico_of_le hab] at hb
  simpa using hb

/-- **The double Riemann sum is the double integral of the step function.**  The
inner integral depends on the outer variable only through its mesh point, so the
one-dimensional identity applies twice. -/
theorem integral2_meshFloor_eq_sum {h : ℝ} (hh : 0 < h) (N : ℕ) (f : ℝ → ℝ → ℝ) :
    ∫ u in Set.Ico (0 : ℝ) ((N : ℝ) * h),
        (∫ v in Set.Ico (0 : ℝ) ((N : ℝ) * h), f (meshFloor h u) (meshFloor h v))
      = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          f ((a : ℝ) * h) ((b : ℝ) * h) * h * h := by
  have hinner : ∀ s : ℝ,
      (∫ v in Set.Ico (0 : ℝ) ((N : ℝ) * h), f s (meshFloor h v))
        = ∑ b ∈ Finset.range N, f s ((b : ℝ) * h) * h :=
    fun s => integral_meshFloor_eq_sum hh N (fun w => f s w)
  have houter := integral_meshFloor_eq_sum hh N
    (fun s => ∫ v in Set.Ico (0 : ℝ) ((N : ℝ) * h), f s (meshFloor h v))
  rw [houter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hinner ((a : ℝ) * h), Finset.sum_mul]

/-! ### The bounded step function, and the two-dimensional limit -/

/-- The integral of a function bounded by `M` over `[0,T)` is at most `M T`. -/
theorem abs_setIntegral_Ico_le {T : ℝ} (hT : 0 ≤ T) (F : ℝ → ℝ)
    (M : ℝ) (hM : ∀ r, |F r| ≤ M) :
    |∫ r in Set.Ico (0 : ℝ) T, F r| ≤ M * T := by
  have hfin : volume (Set.Ico (0 : ℝ) T) < ⊤ := by
    rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top
  have hb := MeasureTheory.norm_setIntegral_le_of_norm_le_const (f := F)
    (s := Set.Ico (0 : ℝ) T) (μ := volume) (C := M) hfin
    (fun x _ => by simpa using hM x)
  rw [Real.volume_real_Ico_of_le hT, sub_zero] at hb
  simpa using hb

/-- A bounded measurable function is integrable on a bounded interval. -/
theorem integrableOn_Ico_of_bounded {T : ℝ} (F : ℝ → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : ∀ r, |F r| ≤ M) : IntegrableOn F (Set.Ico (0 : ℝ) T) volume :=
  MeasureTheory.Measure.integrableOn_of_bounded
    (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top) hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa using hM x)

/-- Two bounded measurable functions within `K` of each other have integrals over
`[0,T)` within `K T` of each other. -/
theorem abs_setIntegral_Ico_sub_le {T : ℝ} (hT : 0 ≤ T) (F G : ℝ → ℝ)
    (hF : Measurable F) (hG : Measurable G) (MF MG : ℝ)
    (hFb : ∀ r, |F r| ≤ MF) (hGb : ∀ r, |G r| ≤ MG)
    (K : ℝ) (hK : ∀ r, |F r - G r| ≤ K) :
    |(∫ r in Set.Ico (0 : ℝ) T, F r) - ∫ r in Set.Ico (0 : ℝ) T, G r| ≤ K * T := by
  rw [← MeasureTheory.integral_sub (integrableOn_Ico_of_bounded F hF MF hFb)
    (integrableOn_Ico_of_bounded G hG MG hGb)]
  exact abs_setIntegral_Ico_le hT (fun r => F r - G r) K hK

/-- **The double integral over the shorter square differs from the one over
`[0,T)^2` by at most `2 M T (T-A)`.**  This is the error the horizon
`⌊R^2T⌋/R^2` makes against `T` in both time variables. -/
theorem abs_integral2_Ico_sub_le {h : ℝ} {A T : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    (f : ℝ → ℝ → ℝ) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ u v, |f u v| ≤ M) :
    |(∫ u in Set.Ico (0 : ℝ) A, ∫ v in Set.Ico (0 : ℝ) A, f (meshFloor h u) (meshFloor h v))
        - ∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T,
            f (meshFloor h u) (meshFloor h v)|
      ≤ 2 * M * T * (T - A) := by
  set Phi : ℝ → ℝ → ℝ :=
    fun C u => ∫ v in Set.Ico (0 : ℝ) C, f (meshFloor h u) (meshFloor h v) with hPhi
  have hmeasPhi : ∀ C : ℝ, Measurable (Phi C) := fun C =>
    measurable_meshFloor_comp h (fun s => ∫ v in Set.Ico (0 : ℝ) C, f s (meshFloor h v))
  have hAT0 : (0 : ℝ) ≤ T := le_trans hA hAT
  have hboundPhi : ∀ C : ℝ, 0 ≤ C → C ≤ T → ∀ u, |Phi C u| ≤ M * T := by
    intro C hC hCT u
    have h1 : |Phi C u| ≤ M * C :=
      abs_setIntegral_Ico_le hC (fun v => f (meshFloor h u) (meshFloor h v)) M (fun v => hM _ _)
    nlinarith
  have hdiffPhi : ∀ u, |Phi A u - Phi T u| ≤ M * (T - A) := by
    intro u
    have h2 := abs_integral_Ico_sub_le hA hAT (fun v => f (meshFloor h u) (meshFloor h v))
      (measurable_meshFloor_comp h (fun w => f (meshFloor h u) w)) M (fun v => hM _ _)
    rw [abs_sub_comm] at h2
    exact h2
  have step1 : |(∫ u in Set.Ico (0 : ℝ) A, Phi A u) - ∫ u in Set.Ico (0 : ℝ) A, Phi T u|
      ≤ M * (T - A) * A :=
    abs_setIntegral_Ico_sub_le hA (Phi A) (Phi T) (hmeasPhi A) (hmeasPhi T) (M * T) (M * T)
      (hboundPhi A hA hAT) (hboundPhi T hAT0 le_rfl) (M * (T - A)) hdiffPhi
  have step2 : |(∫ u in Set.Ico (0 : ℝ) T, Phi T u) - ∫ u in Set.Ico (0 : ℝ) A, Phi T u|
      ≤ M * T * (T - A) :=
    abs_integral_Ico_sub_le hA hAT (Phi T) (hmeasPhi T) (M * T) (hboundPhi T hAT0 le_rfl)
  have hTA : (0 : ℝ) ≤ T - A := by linarith
  have htri : |(∫ u in Set.Ico (0 : ℝ) A, Phi A u) - ∫ u in Set.Ico (0 : ℝ) T, Phi T u|
      ≤ |(∫ u in Set.Ico (0 : ℝ) A, Phi A u) - ∫ u in Set.Ico (0 : ℝ) A, Phi T u|
        + |(∫ u in Set.Ico (0 : ℝ) T, Phi T u) - ∫ u in Set.Ico (0 : ℝ) A, Phi T u| := by
    have hid : (∫ u in Set.Ico (0 : ℝ) A, Phi A u) - ∫ u in Set.Ico (0 : ℝ) T, Phi T u
        = ((∫ u in Set.Ico (0 : ℝ) A, Phi A u) - ∫ u in Set.Ico (0 : ℝ) A, Phi T u)
          - ((∫ u in Set.Ico (0 : ℝ) T, Phi T u) - ∫ u in Set.Ico (0 : ℝ) A, Phi T u) := by
      ring
    rw [hid]
    exact abs_sub _ _
  calc |(∫ u in Set.Ico (0 : ℝ) A, Phi A u) - ∫ u in Set.Ico (0 : ℝ) T, Phi T u|
      ≤ M * (T - A) * A + M * T * (T - A) := le_trans htri (add_le_add step1 step2)
    _ ≤ 2 * M * T * (T - A) := by
        have hMT : M * (T - A) * A ≤ M * (T - A) * T :=
          mul_le_mul_of_nonneg_left hAT (mul_nonneg hM0 hTA)
        nlinarith

/-- **The double Riemann sums of a bounded jointly continuous function converge to
its double integral.** -/
theorem tendsto_integral2_meshFloor {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (H : ι → ℝ) (hH0 : ∀ᶠ i in l, 0 < H i) (hH : Tendsto H l (𝓝 0))
    {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2)
    (M : ℝ) (hM : ∀ u v, |f u v| ≤ M) :
    Tendsto (fun i => ∫ u in Set.Ico (0 : ℝ) T,
        ∫ v in Set.Ico (0 : ℝ) T, f (meshFloor (H i) u) (meshFloor (H i) v)) l
      (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) := by
  have hmesh : ∀ r : ℝ, Tendsto (fun i => meshFloor (H i) r) l (𝓝 r) := by
    intro r
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' ?_ hH
    filter_upwards [hH0] with i hi
    simpa using abs_meshFloor_sub_le hi r
  have hinner : ∀ u : ℝ, Tendsto (fun i =>
      ∫ v in Set.Ico (0 : ℝ) T, f (meshFloor (H i) u) (meshFloor (H i) v)) l
      (𝓝 (∫ v in Set.Ico (0 : ℝ) T, f u v)) := by
    intro u
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Filter.Eventually.of_forall fun i =>
        (measurable_meshFloor_comp (H i) (fun w => f (meshFloor (H i) u) w)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun i =>
        Filter.Eventually.of_forall fun v => by simpa using hM _ _)
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
      (Filter.Eventually.of_forall fun v => ?_)
    have hpair : Tendsto (fun i => ((meshFloor (H i) u, meshFloor (H i) v) : ℝ × ℝ)) l (𝓝 (u, v)) :=
      (hmesh u).prodMk_nhds (hmesh v)
    exact (hf.tendsto (u, v)).comp hpair
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => M * T)
    (Filter.Eventually.of_forall fun i => ?_)
    (Filter.Eventually.of_forall fun i =>
      Filter.Eventually.of_forall fun u => ?_)
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
    (Filter.Eventually.of_forall hinner)
  · exact (measurable_meshFloor_comp (H i)
      (fun s => ∫ v in Set.Ico (0 : ℝ) T, f s (meshFloor (H i) v))).aestronglyMeasurable
  · have hb := abs_setIntegral_Ico_le hT
      (fun v => f (meshFloor (H i) u) (meshFloor (H i) v)) M (fun v => hM _ _)
    simpa using hb

/-! ### The Riemann sums of `prop:weighted-membrane-limit` -/

/-- **The double Riemann sums in time converge to the double integral.**  With
`h = R^{-2}` and the horizon `N = ⌊R^2T⌋`, the double time sum of
`sandpile.tex:4719-4724`, normalized by `R^{-4}`, converges to the double time
integral of `generalWeightedMembraneCov`.  The horizon `N h` falls short of `T`
by at most `h`, and that error is absorbed by the bound `2 M T h`. -/
theorem tendsto_sum_mesh_two {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u v, |f u v| ≤ M) :
    Tendsto (fun R : ℝ => ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊,
        ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          f ((a : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      atTop (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) := by
  set H : ℝ → ℝ := fun R => (R ^ 2)⁻¹ with hHdef
  have hHpos : ∀ᶠ R : ℝ in atTop, 0 < H R := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simp only [hHdef]
    positivity
  have hHlim : Tendsto H atTop (𝓝 0) := by
    simp only [hHdef]
    exact Filter.Tendsto.inv_tendsto_atTop (tendsto_pow_atTop (by norm_num))
  set I : ℝ → ℝ := fun R => ∫ u in Set.Ico (0 : ℝ) T,
    ∫ v in Set.Ico (0 : ℝ) T, f (meshFloor (H R) u) (meshFloor (H R) v) with hIdef
  have hIlim : Tendsto I atTop
      (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) :=
    tendsto_integral2_meshFloor H hHpos hHlim hT f hf M hM
  set S : ℝ → ℝ := fun R => ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊,
    ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
      f ((a : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹ with hSdef
  have hdiff : Tendsto (fun R => S R - I R) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hHlim.const_mul (2 * M * T))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hHR : 0 < H R := by simp only [hHdef]; positivity
    have hTR : (0 : ℝ) ≤ R ^ 2 * T := by positivity
    have hA0 : (0 : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℝ)) * H R := by positivity
    have hfl : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le hTR
    have hfl2 : R ^ 2 * T < ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    have hAT : ((⌊R ^ 2 * T⌋₊ : ℝ)) * H R ≤ T := by
      rw [hHdef]
      rw [mul_inv_le_iff₀ hR2]
      nlinarith
    have hgap : T - ((⌊R ^ 2 * T⌋₊ : ℝ)) * H R ≤ H R := by
      have h1 : T - (⌊R ^ 2 * T⌋₊ : ℝ) * (R ^ 2)⁻¹ ≤ (R ^ 2)⁻¹ := by
        have h2 : (T - (⌊R ^ 2 * T⌋₊ : ℝ) * (R ^ 2)⁻¹) * R ^ 2 ≤ (R ^ 2)⁻¹ * R ^ 2 := by
          rw [sub_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt hR2), mul_one]
          nlinarith [hfl2]
        exact le_of_mul_le_mul_right h2 hR2
      simpa [hHdef] using h1
    have hSI : S R = ∫ u in Set.Ico (0 : ℝ) (((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * H R),
        ∫ v in Set.Ico (0 : ℝ) (((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * H R),
          f (meshFloor (H R) u) (meshFloor (H R) v) := by
      rw [integral2_meshFloor_eq_sum hHR ⌊R ^ 2 * T⌋₊ f]
    rw [hSI]
    have hb := abs_integral2_Ico_sub_le (h := H R) hA0 hAT f M hM0 hM
    have : 2 * M * T * (T - ((⌊R ^ 2 * T⌋₊ : ℝ)) * H R) ≤ 2 * M * T * H R := by
      have h2MT : (0 : ℝ) ≤ 2 * M * T := by nlinarith [le_trans hA0 hAT]
      exact mul_le_mul_of_nonneg_left hgap h2MT
    calc ‖(∫ u in Set.Ico (0 : ℝ) (((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * H R),
            ∫ v in Set.Ico (0 : ℝ) (((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * H R),
              f (meshFloor (H R) u) (meshFloor (H R) v)) - I R‖
        ≤ 2 * M * T * (T - ((⌊R ^ 2 * T⌋₊ : ℝ)) * H R) := by simpa [hIdef] using hb
      _ ≤ 2 * M * T * H R := this
  have := hdiff.add hIlim
  simpa using this

/-- **The double sums over a family of mesh-like maps converge to the double
integral.**  This is `tendsto_integral2_meshFloor` with the mesh point replaced
by any family of maps that converges uniformly to the identity and reads
measurably. -/
theorem tendsto_integral2_of_family {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (P : ι → ℝ → ℝ) (hPmeas : ∀ i, ∀ G : ℝ → ℝ, Measurable fun r => G (P i r))
    (δ : ι → ℝ) (hδ : Tendsto δ l (𝓝 0)) (hP : ∀ᶠ i in l, ∀ r, |P i r - r| ≤ δ i)
    {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2)
    (M : ℝ) (hM : ∀ u v, |f u v| ≤ M) :
    Tendsto (fun i => ∫ u in Set.Ico (0 : ℝ) T,
        ∫ v in Set.Ico (0 : ℝ) T, f (P i u) (P i v)) l
      (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) := by
  have hmesh : ∀ r : ℝ, Tendsto (fun i => P i r) l (𝓝 r) := by
    intro r
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' ?_ hδ
    filter_upwards [hP] with i hi
    simpa using hi r
  have hinner : ∀ u : ℝ, Tendsto (fun i =>
      ∫ v in Set.Ico (0 : ℝ) T, f (P i u) (P i v)) l
      (𝓝 (∫ v in Set.Ico (0 : ℝ) T, f u v)) := by
    intro u
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Filter.Eventually.of_forall fun i =>
        (hPmeas i (fun w => f (P i u) w)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun i =>
        Filter.Eventually.of_forall fun v => by simpa using hM _ _)
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
      (Filter.Eventually.of_forall fun v => ?_)
    have hpair : Tendsto (fun i => ((P i u, P i v) : ℝ × ℝ)) l (𝓝 (u, v)) :=
      (hmesh u).prodMk_nhds (hmesh v)
    exact (hf.tendsto (u, v)).comp hpair
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => M * T)
    (Filter.Eventually.of_forall fun i => ?_)
    (Filter.Eventually.of_forall fun i =>
      Filter.Eventually.of_forall fun u => ?_)
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
    (Filter.Eventually.of_forall hinner)
  · exact (hPmeas i (fun s => ∫ v in Set.Ico (0 : ℝ) T, f s (P i v))).aestronglyMeasurable
  · have hb := abs_setIntegral_Ico_le hT
      (fun v => f (P i u) (P i v)) M (fun v => hM _ _)
    simpa using hb

/-- **The double Riemann sums over an offset mesh converge to the double
integral.**  The mesh width `H R`, the offset `c R` and the horizon `N R` are
arbitrary, subject to the width and the offset going to zero and the horizon
`N R · H R` rising to `T` from below. -/
theorem tendsto_sum2_of_family {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u v, |f u v| ≤ M) (H c : ℝ → ℝ) (N : ℝ → ℕ)
    (hHpos : ∀ᶠ R : ℝ in atTop, 0 < H R) (hHlim : Tendsto H atTop (𝓝 0))
    (hclim : Tendsto c atTop (𝓝 0))
    (hAle : ∀ᶠ R : ℝ in atTop, 0 ≤ (N R : ℝ) * H R ∧ (N R : ℝ) * H R ≤ T)
    (hAgap : Tendsto (fun R : ℝ => T - (N R : ℝ) * H R) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => ∑ a ∈ Finset.range (N R), ∑ b ∈ Finset.range (N R),
        f ((a : ℝ) * H R + c R) ((b : ℝ) * H R + c R) * H R * H R)
      atTop (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) := by
  set P : ℝ → ℝ → ℝ := fun R r => meshFloor (H R) r + c R with hPdef
  have hPmeas : ∀ R : ℝ, ∀ G : ℝ → ℝ, Measurable fun r => G (P R r) := fun R G =>
    measurable_meshFloor_comp (H R) (fun s => G (s + c R))
  have hdelta : Tendsto (fun R : ℝ => H R + |c R|) atTop (𝓝 0) := by
    simpa using hHlim.add hclim.abs
  have hPbd : ∀ᶠ R : ℝ in atTop, ∀ r : ℝ, |P R r - r| ≤ H R + |c R| := by
    filter_upwards [hHpos] with R hR r
    have h1 : |meshFloor (H R) r - r| ≤ H R := abs_meshFloor_sub_le hR r
    have h2 : P R r - r = (meshFloor (H R) r - r) + c R := by simp only [hPdef]; ring
    rw [h2]
    have h3 : |(meshFloor (H R) r - r) + c R| ≤ |meshFloor (H R) r - r| + |c R| := by
      simpa using norm_add_le (meshFloor (H R) r - r) (c R)
    exact le_trans h3 (add_le_add h1 le_rfl)
  set I : ℝ → ℝ := fun R => ∫ u in Set.Ico (0 : ℝ) T,
    ∫ v in Set.Ico (0 : ℝ) T, f (P R u) (P R v) with hIdef
  have hIlim : Tendsto I atTop
      (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) :=
    tendsto_integral2_of_family P hPmeas (fun R => H R + |c R|) hdelta hPbd hT f hf M hM
  set S : ℝ → ℝ := fun R => ∑ a ∈ Finset.range (N R), ∑ b ∈ Finset.range (N R),
    f ((a : ℝ) * H R + c R) ((b : ℝ) * H R + c R) * H R * H R with hSdef
  have hdiff : Tendsto (fun R => S R - I R) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hAgap.const_mul (2 * M * T))
    filter_upwards [hHpos, hAle] with R hR hA
    have hSI : S R = ∫ u in Set.Ico (0 : ℝ) ((N R : ℝ) * H R),
        ∫ v in Set.Ico (0 : ℝ) ((N R : ℝ) * H R),
          (fun s t => f (s + c R) (t + c R)) (meshFloor (H R) u) (meshFloor (H R) v) := by
      rw [integral2_meshFloor_eq_sum hR (N R) (fun s t => f (s + c R) (t + c R))]
    have hb := abs_integral2_Ico_sub_le (h := H R) hA.1 hA.2
      (fun s t => f (s + c R) (t + c R)) M hM0 (fun u v => hM _ _)
    rw [hSI]
    simpa [hIdef, hPdef] using hb
  have hsum := hdiff.add hIlim
  simpa using hsum

/-- The two-sided form of the endpoint comparison: the horizon may overshoot `T`
as well as fall short of it, which is what the even and odd sublattices of the
time mesh do. -/
theorem abs_integral2_Ico_sub_le' {h : ℝ} {A T : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T)
    (f : ℝ → ℝ → ℝ) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ u v, |f u v| ≤ M) :
    |(∫ u in Set.Ico (0 : ℝ) A, ∫ v in Set.Ico (0 : ℝ) A, f (meshFloor h u) (meshFloor h v))
        - ∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T,
            f (meshFloor h u) (meshFloor h v)|
      ≤ 2 * M * (T + |A - T|) * |A - T| := by
  rcases le_total A T with hle | hle
  · have hb := abs_integral2_Ico_sub_le (h := h) hA hle f M hM0 hM
    have habs : |A - T| = T - A := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [habs]
    have h1 : (0 : ℝ) ≤ T - A := by linarith
    have hextra : (0 : ℝ) ≤ 2 * M * (T - A) * (T - A) :=
      mul_nonneg (mul_nonneg (by linarith) h1) h1
    have hid : 2 * M * (T + (T - A)) * (T - A)
        = 2 * M * T * (T - A) + 2 * M * (T - A) * (T - A) := by ring
    rw [hid]
    linarith
  · have hb := abs_integral2_Ico_sub_le (h := h) hT hle f M hM0 hM
    have habs : |A - T| = A - T := abs_of_nonneg (by linarith)
    rw [abs_sub_comm, habs]
    have hid2 : T + (A - T) = A := by ring
    rw [hid2]
    exact hb

/-- **The double Riemann sums over an offset mesh whose horizon approaches `T`
from either side.**  Taking the width `2h`, the offset `0` or `h` and the horizon
the number of even, respectively odd, indices below `⌊R^2T⌋` gives the two
sublattice sums whose sum is the parity-restricted time sum of
`sandpile.tex:1157-1161`. -/
theorem tendsto_sum2_of_family' {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u v, |f u v| ≤ M) (H c : ℝ → ℝ) (N : ℝ → ℕ)
    (hHpos : ∀ᶠ R : ℝ in atTop, 0 < H R) (hHlim : Tendsto H atTop (𝓝 0))
    (hclim : Tendsto c atTop (𝓝 0))
    (hAgap : Tendsto (fun R : ℝ => |(N R : ℝ) * H R - T|) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => ∑ a ∈ Finset.range (N R), ∑ b ∈ Finset.range (N R),
        f ((a : ℝ) * H R + c R) ((b : ℝ) * H R + c R) * H R * H R)
      atTop (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) := by
  set P : ℝ → ℝ → ℝ := fun R r => meshFloor (H R) r + c R with hPdef
  have hPmeas : ∀ R : ℝ, ∀ G : ℝ → ℝ, Measurable fun r => G (P R r) := fun R G =>
    measurable_meshFloor_comp (H R) (fun s => G (s + c R))
  have hdelta : Tendsto (fun R : ℝ => H R + |c R|) atTop (𝓝 0) := by
    simpa using hHlim.add hclim.abs
  have hPbd : ∀ᶠ R : ℝ in atTop, ∀ r : ℝ, |P R r - r| ≤ H R + |c R| := by
    filter_upwards [hHpos] with R hR r
    have h1 : |meshFloor (H R) r - r| ≤ H R := abs_meshFloor_sub_le hR r
    have h2 : P R r - r = (meshFloor (H R) r - r) + c R := by simp only [hPdef]; ring
    have h3 : |(meshFloor (H R) r - r) + c R| ≤ |meshFloor (H R) r - r| + |c R| := by
      simpa using norm_add_le (meshFloor (H R) r - r) (c R)
    rw [h2]
    exact le_trans h3 (add_le_add h1 le_rfl)
  set I : ℝ → ℝ := fun R => ∫ u in Set.Ico (0 : ℝ) T,
    ∫ v in Set.Ico (0 : ℝ) T, f (P R u) (P R v) with hIdef
  have hIlim : Tendsto I atTop
      (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) :=
    tendsto_integral2_of_family P hPmeas (fun R => H R + |c R|) hdelta hPbd hT f hf M hM
  set S : ℝ → ℝ := fun R => ∑ a ∈ Finset.range (N R), ∑ b ∈ Finset.range (N R),
    f ((a : ℝ) * H R + c R) ((b : ℝ) * H R + c R) * H R * H R with hSdef
  have hbound : Tendsto (fun R : ℝ => 2 * M * (T + |(N R : ℝ) * H R - T|) *
      |(N R : ℝ) * H R - T|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => 2 * M * (T + |(N R : ℝ) * H R - T|)) atTop
        (𝓝 (2 * M * (T + 0))) := by
      exact ((tendsto_const_nhds.add hAgap).const_mul (2 * M))
    simpa using h1.mul hAgap
  have hdiff : Tendsto (fun R => S R - I R) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hHpos] with R hR
    have hA0 : (0 : ℝ) ≤ (N R : ℝ) * H R := by positivity
    have hSI : S R = ∫ u in Set.Ico (0 : ℝ) ((N R : ℝ) * H R),
        ∫ v in Set.Ico (0 : ℝ) ((N R : ℝ) * H R),
          (fun s t => f (s + c R) (t + c R)) (meshFloor (H R) u) (meshFloor (H R) v) := by
      rw [integral2_meshFloor_eq_sum hR (N R) (fun s t => f (s + c R) (t + c R))]
    have hb := abs_integral2_Ico_sub_le' (h := H R) hA0 hT
      (fun s t => f (s + c R) (t + c R)) M hM0 (fun u v => hM _ _)
    rw [hSI]
    simpa [hIdef, hPdef] using hb
  have hsum := hdiff.add hIlim
  simpa using hsum

/-! ### The even and odd indices of the time mesh

The parity class of `sandpile.tex:1157-1161` restricts the double time sum to the
pairs `(a,b)` whose sum has a prescribed parity, and each of the four cases is a
sum over a sublattice of the time mesh: the even indices `a = 2k` run over the
mesh of width `2h`, and the odd indices `a = 2k+1` over the same mesh shifted by
`h`.  These two reindexings are what turns a parity-restricted sum into a
Riemann sum for the mesh of width `2h`. -/

theorem sum_range_filter_even (N : ℕ) (F : ℕ → ℝ) :
    ∑ a ∈ (Finset.range N).filter (fun a => Even a), F a
      = ∑ k ∈ Finset.range ((N + 1) / 2), F (2 * k) := by
  classical
  refine Finset.sum_nbij' (fun a => a / 2) (fun k => 2 * k) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    rw [Finset.mem_range]
    obtain ⟨hlt, hev⟩ := ha
    obtain ⟨m, hm⟩ := hev
    omega
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ⟨k, by omega⟩⟩
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨m, hm⟩ := ha.2
    omega
  · intro k hk
    omega
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨m, hm⟩ := ha.2
    congr 1
    omega

theorem sum_range_filter_odd (N : ℕ) (F : ℕ → ℝ) :
    ∑ a ∈ (Finset.range N).filter (fun a => ¬ Even a), F a
      = ∑ k ∈ Finset.range (N / 2), F (2 * k + 1) := by
  classical
  refine Finset.sum_nbij' (fun a => a / 2) (fun k => 2 * k + 1) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    rw [Finset.mem_range]
    obtain ⟨hlt, hodd⟩ := ha
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨m, hm⟩ := hodd
    omega
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_range, Nat.not_even_iff_odd]
    exact ⟨by omega, ⟨k, by omega⟩⟩
  · intro a ha
    rw [Finset.mem_filter, Nat.not_even_iff_odd] at ha
    obtain ⟨m, hm⟩ := ha.2
    omega
  · intro k hk
    omega
  · intro a ha
    rw [Finset.mem_filter, Nat.not_even_iff_odd] at ha
    obtain ⟨m, hm⟩ := ha.2
    congr 1
    omega

/-- **The pairs of times of even total split into the pairs of even indices and
the pairs of odd indices.**  Together with the two reindexings above this turns
the parity-restricted double time sum into two Riemann sums for the mesh of
width `2h`. -/
theorem sum_filter_even_sum_product (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ p ∈ ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p : ℕ × ℕ => Even (p.1 + p.2)),
        F p.1 p.2
      = (∑ a ∈ (Finset.range N).filter (fun a => Even a),
          ∑ b ∈ (Finset.range N).filter (fun b => Even b), F a b)
        + ∑ a ∈ (Finset.range N).filter (fun a => ¬ Even a),
            ∑ b ∈ (Finset.range N).filter (fun b => ¬ Even b), F a b := by
  classical
  rw [Finset.sum_filter, Finset.sum_product]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun a => Even a)
    (fun a => ∑ b ∈ Finset.range N, if Even (a + b) then F a b else 0)]
  congr 1
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb : Even (a + b) ↔ Even b := by
      rw [Nat.even_add]
      simp [ha.2]
    simp [hb]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb : Even (a + b) ↔ ¬ Even b := by
      rw [Nat.even_add]
      simp [ha.2]
    simp [hb]

/-- **The pairs of times of odd total split into the two mixed classes.** -/
theorem sum_filter_odd_sum_product (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ p ∈ ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p : ℕ × ℕ => ¬ Even (p.1 + p.2)),
        F p.1 p.2
      = (∑ a ∈ (Finset.range N).filter (fun a => Even a),
          ∑ b ∈ (Finset.range N).filter (fun b => ¬ Even b), F a b)
        + ∑ a ∈ (Finset.range N).filter (fun a => ¬ Even a),
            ∑ b ∈ (Finset.range N).filter (fun b => Even b), F a b := by
  classical
  rw [Finset.sum_filter, Finset.sum_product]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun a => Even a)
    (fun a => ∑ b ∈ Finset.range N, if ¬ Even (a + b) then F a b else 0)]
  congr 1
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb : ¬ Even (a + b) ↔ ¬ Even b := by
      rw [Nat.even_add]
      simp [ha.2]
    simp [hb]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb : ¬ Even (a + b) ↔ Even b := by
      rw [Nat.even_add]
      simp [ha.2]
    simp [hb]

/-! ### Two horizons and two offsets

The even indices below `⌊R^2T⌋` number `⌈⌊R^2T⌋/2⌉` and the odd ones `⌊⌊R^2T⌋/2⌋`,
so the two sublattices of a parity class carry different horizons; and the odd
sublattice is the even one shifted by the mesh width `h`.  The lemmas of this
section are the versions of the ones above that allow a different horizon and a
different offset in each of the two time variables. -/

/-- The double identity with a different horizon in each coordinate, which is what
the even and odd sublattices of the time mesh need. -/
theorem integral2_meshFloor_eq_sum_rect {h : ℝ} (hh : 0 < h) (N K : ℕ) (f : ℝ → ℝ → ℝ) :
    ∫ u in Set.Ico (0 : ℝ) ((N : ℝ) * h),
        (∫ v in Set.Ico (0 : ℝ) ((K : ℝ) * h), f (meshFloor h u) (meshFloor h v))
      = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range K,
          f ((a : ℝ) * h) ((b : ℝ) * h) * h * h := by
  have hinner : ∀ s : ℝ,
      (∫ v in Set.Ico (0 : ℝ) ((K : ℝ) * h), f s (meshFloor h v))
        = ∑ b ∈ Finset.range K, f s ((b : ℝ) * h) * h :=
    fun s => integral_meshFloor_eq_sum hh K (fun w => f s w)
  have houter := integral_meshFloor_eq_sum hh N
    (fun s => ∫ v in Set.Ico (0 : ℝ) ((K : ℝ) * h), f s (meshFloor h v))
  rw [houter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hinner ((a : ℝ) * h), Finset.sum_mul]

/-- The endpoint comparison with no sign on the change of endpoint. -/
theorem abs_integral_Ico_sub_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (F : ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hM : ∀ r, |F r| ≤ M) :
    |(∫ r in Set.Ico (0 : ℝ) b, F r) - ∫ r in Set.Ico (0 : ℝ) a, F r| ≤ M * |b - a| := by
  rcases le_total a b with hle | hle
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]
    exact abs_integral_Ico_sub_le ha hle F hF M hM
  · rw [abs_sub_comm, abs_of_nonpos (by linarith : b - a ≤ 0)]
    have h2 := abs_integral_Ico_sub_le hb hle F hF M hM
    simpa using h2

/-- The double endpoint comparison with a different horizon in each coordinate. -/
theorem abs_integral2_Ico_sub_le_rect {h : ℝ} {A B T : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ u v, |f u v| ≤ M) :
    |(∫ u in Set.Ico (0 : ℝ) A, ∫ v in Set.Ico (0 : ℝ) B, f (meshFloor h u) (meshFloor h v))
        - ∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T,
            f (meshFloor h u) (meshFloor h v)|
      ≤ 2 * M * (T + |A - T| + |B - T|) * (|A - T| + |B - T|) := by
  set Phi : ℝ → ℝ → ℝ :=
    fun C u => ∫ v in Set.Ico (0 : ℝ) C, f (meshFloor h u) (meshFloor h v) with hPhi
  have hmeasPhi : ∀ C : ℝ, Measurable (Phi C) := fun C =>
    measurable_meshFloor_comp h (fun s => ∫ v in Set.Ico (0 : ℝ) C, f s (meshFloor h v))
  have hboundPhi : ∀ C : ℝ, 0 ≤ C → ∀ u, |Phi C u| ≤ M * C := fun C hC u =>
    abs_setIntegral_Ico_le hC (fun v => f (meshFloor h u) (meshFloor h v)) M (fun v => hM _ _)
  have hdiffPhi : ∀ u, |Phi B u - Phi T u| ≤ M * |B - T| := by
    intro u
    exact abs_integral_Ico_sub_le' hT hB (fun v => f (meshFloor h u) (meshFloor h v))
      (measurable_meshFloor_comp h (fun w => f (meshFloor h u) w)) M (fun v => hM _ _)
  have hAT : (0 : ℝ) ≤ |A - T| := abs_nonneg _
  have hBT : (0 : ℝ) ≤ |B - T| := abs_nonneg _
  have hBle : B ≤ T + |B - T| := by
    have := le_abs_self (B - T); linarith
  have step1 : |(∫ u in Set.Ico (0 : ℝ) A, Phi B u) - ∫ u in Set.Ico (0 : ℝ) A, Phi T u|
      ≤ M * |B - T| * A :=
    abs_setIntegral_Ico_sub_le hA (Phi B) (Phi T) (hmeasPhi B) (hmeasPhi T) (M * B) (M * T)
      (hboundPhi B hB) (hboundPhi T hT) (M * |B - T|) hdiffPhi
  have step2 : |(∫ u in Set.Ico (0 : ℝ) A, Phi T u) - ∫ u in Set.Ico (0 : ℝ) T, Phi T u|
      ≤ (M * T) * |A - T| :=
    abs_integral_Ico_sub_le' hT hA (Phi T) (hmeasPhi T) (M * T) (hboundPhi T hT)
  have htri : |(∫ u in Set.Ico (0 : ℝ) A, Phi B u) - ∫ u in Set.Ico (0 : ℝ) T, Phi T u|
      ≤ |(∫ u in Set.Ico (0 : ℝ) A, Phi B u) - ∫ u in Set.Ico (0 : ℝ) A, Phi T u|
        + |(∫ u in Set.Ico (0 : ℝ) A, Phi T u) - ∫ u in Set.Ico (0 : ℝ) T, Phi T u| := by
    have hid : (∫ u in Set.Ico (0 : ℝ) A, Phi B u) - ∫ u in Set.Ico (0 : ℝ) T, Phi T u
        = ((∫ u in Set.Ico (0 : ℝ) A, Phi B u) - ∫ u in Set.Ico (0 : ℝ) A, Phi T u)
          + ((∫ u in Set.Ico (0 : ℝ) A, Phi T u) - ∫ u in Set.Ico (0 : ℝ) T, Phi T u) := by
      ring
    rw [hid]
    simpa using norm_add_le
      ((∫ u in Set.Ico (0 : ℝ) A, Phi B u) - ∫ u in Set.Ico (0 : ℝ) A, Phi T u)
      ((∫ u in Set.Ico (0 : ℝ) A, Phi T u) - ∫ u in Set.Ico (0 : ℝ) T, Phi T u)
  have hAle : A ≤ T + |A - T| := by
    have := le_abs_self (A - T); linarith
  calc |(∫ u in Set.Ico (0 : ℝ) A, Phi B u) - ∫ u in Set.Ico (0 : ℝ) T, Phi T u|
      ≤ M * |B - T| * A + (M * T) * |A - T| := le_trans htri (add_le_add step1 step2)
    _ ≤ 2 * M * (T + |A - T| + |B - T|) * (|A - T| + |B - T|) := by
        have hS : (0 : ℝ) ≤ T + |A - T| + |B - T| := by linarith
        have h1 : M * |B - T| * A ≤ M * (T + |A - T| + |B - T|) * |B - T| := by
          nlinarith [mul_nonneg hM0 hBT]
        have h2 : M * T * |A - T| ≤ M * (T + |A - T| + |B - T|) * |A - T| := by
          nlinarith [mul_nonneg hM0 hAT]
        nlinarith [mul_nonneg (mul_nonneg hM0 hS) (add_nonneg hAT hBT)]

/-- The double limit for two independent families of mesh-like maps, one in each
coordinate: the outer variable is read through `P` and the inner through `Q`. -/
theorem tendsto_integral2_of_family_pair {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (P Q : ι → ℝ → ℝ)
    (hPmeas : ∀ i, ∀ G : ℝ → ℝ, Measurable fun r => G (P i r))
    (hQmeas : ∀ i, ∀ G : ℝ → ℝ, Measurable fun r => G (Q i r))
    (δ : ι → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hP : ∀ᶠ i in l, ∀ r, |P i r - r| ≤ δ i)
    (hQ : ∀ᶠ i in l, ∀ r, |Q i r - r| ≤ δ i)
    {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2)
    (M : ℝ) (hM : ∀ u v, |f u v| ≤ M) :
    Tendsto (fun i => ∫ u in Set.Ico (0 : ℝ) T,
        ∫ v in Set.Ico (0 : ℝ) T, f (P i u) (Q i v)) l
      (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) := by
  have hmeshP : ∀ r : ℝ, Tendsto (fun i => P i r) l (𝓝 r) := by
    intro r
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' ?_ hδ
    filter_upwards [hP] with i hi
    simpa using hi r
  have hmeshQ : ∀ r : ℝ, Tendsto (fun i => Q i r) l (𝓝 r) := by
    intro r
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' ?_ hδ
    filter_upwards [hQ] with i hi
    simpa using hi r
  have hinner : ∀ u : ℝ, Tendsto (fun i =>
      ∫ v in Set.Ico (0 : ℝ) T, f (P i u) (Q i v)) l
      (𝓝 (∫ v in Set.Ico (0 : ℝ) T, f u v)) := by
    intro u
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Filter.Eventually.of_forall fun i =>
        (hQmeas i (fun w => f (P i u) w)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun i =>
        Filter.Eventually.of_forall fun v => by simpa using hM _ _)
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
      (Filter.Eventually.of_forall fun v => ?_)
    have hpair : Tendsto (fun i => ((P i u, Q i v) : ℝ × ℝ)) l (𝓝 (u, v)) :=
      (hmeshP u).prodMk_nhds (hmeshQ v)
    exact (hf.tendsto (u, v)).comp hpair
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => M * T)
    (Filter.Eventually.of_forall fun i => ?_)
    (Filter.Eventually.of_forall fun i =>
      Filter.Eventually.of_forall fun u => ?_)
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
    (Filter.Eventually.of_forall hinner)
  · exact (hPmeas i (fun s => ∫ v in Set.Ico (0 : ℝ) T, f s (Q i v))).aestronglyMeasurable
  · have hb := abs_setIntegral_Ico_le hT (fun v => f (P i u) (Q i v)) M (fun v => hM _ _)
    simpa using hb

/-- **The double Riemann sums with a different offset and horizon in each time
variable.**  With the width `2h`, the offsets `(0,0)`, `(h,h)`, `(0,h)`, `(h,0)`
and the horizons the numbers of even, respectively odd, indices below `⌊R^2T⌋`,
the four instances of this theorem are the four sublattice sums whose pairs make
up a parity class of `sandpile.tex:1157-1161`; each converges to a QUARTER of the
double time integral, so a parity class converges to a half of it. -/
theorem tendsto_sum2_of_family_pair {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u v, |f u v| ≤ M) (H c c' : ℝ → ℝ) (N K : ℝ → ℕ)
    (hHpos : ∀ᶠ R : ℝ in atTop, 0 < H R) (hHlim : Tendsto H atTop (𝓝 0))
    (hclim : Tendsto c atTop (𝓝 0)) (hclim' : Tendsto c' atTop (𝓝 0))
    (hAgap : Tendsto (fun R : ℝ => |(N R : ℝ) * H R - T|) atTop (𝓝 0))
    (hBgap : Tendsto (fun R : ℝ => |(K R : ℝ) * H R - T|) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => ∑ a ∈ Finset.range (N R), ∑ b ∈ Finset.range (K R),
        f ((a : ℝ) * H R + c R) ((b : ℝ) * H R + c' R) * H R * H R)
      atTop (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) := by
  set P : ℝ → ℝ → ℝ := fun R r => meshFloor (H R) r + c R with hPdef
  set Q : ℝ → ℝ → ℝ := fun R r => meshFloor (H R) r + c' R with hQdef
  have hPmeas : ∀ R : ℝ, ∀ G : ℝ → ℝ, Measurable fun r => G (P R r) := fun R G =>
    measurable_meshFloor_comp (H R) (fun s => G (s + c R))
  have hQmeas : ∀ R : ℝ, ∀ G : ℝ → ℝ, Measurable fun r => G (Q R r) := fun R G =>
    measurable_meshFloor_comp (H R) (fun s => G (s + c' R))
  have hdelta : Tendsto (fun R : ℝ => H R + (|c R| + |c' R|)) atTop (𝓝 0) := by
    simpa using hHlim.add (hclim.abs.add hclim'.abs)
  have hPbd : ∀ᶠ R : ℝ in atTop, ∀ r : ℝ, |P R r - r| ≤ H R + (|c R| + |c' R|) := by
    filter_upwards [hHpos] with R hR r
    have h1 : |meshFloor (H R) r - r| ≤ H R := abs_meshFloor_sub_le hR r
    have h2 : P R r - r = (meshFloor (H R) r - r) + c R := by simp only [hPdef]; ring
    have h3 : |(meshFloor (H R) r - r) + c R| ≤ |meshFloor (H R) r - r| + |c R| := by
      simpa using norm_add_le (meshFloor (H R) r - r) (c R)
    rw [h2]
    have h4 : |c' R| ≥ 0 := abs_nonneg _
    linarith [le_trans h3 (add_le_add h1 (le_refl |c R|))]
  have hQbd : ∀ᶠ R : ℝ in atTop, ∀ r : ℝ, |Q R r - r| ≤ H R + (|c R| + |c' R|) := by
    filter_upwards [hHpos] with R hR r
    have h1 : |meshFloor (H R) r - r| ≤ H R := abs_meshFloor_sub_le hR r
    have h2 : Q R r - r = (meshFloor (H R) r - r) + c' R := by simp only [hQdef]; ring
    have h3 : |(meshFloor (H R) r - r) + c' R| ≤ |meshFloor (H R) r - r| + |c' R| := by
      simpa using norm_add_le (meshFloor (H R) r - r) (c' R)
    rw [h2]
    have h4 : |c R| ≥ 0 := abs_nonneg _
    linarith [le_trans h3 (add_le_add h1 (le_refl |c' R|))]
  set I : ℝ → ℝ := fun R => ∫ u in Set.Ico (0 : ℝ) T,
    ∫ v in Set.Ico (0 : ℝ) T, f (P R u) (Q R v) with hIdef
  have hIlim : Tendsto I atTop
      (𝓝 (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v)) :=
    tendsto_integral2_of_family_pair P Q hPmeas hQmeas
      (fun R => H R + (|c R| + |c' R|)) hdelta hPbd hQbd hT f hf M hM
  set S : ℝ → ℝ := fun R => ∑ a ∈ Finset.range (N R), ∑ b ∈ Finset.range (K R),
    f ((a : ℝ) * H R + c R) ((b : ℝ) * H R + c' R) * H R * H R with hSdef
  have hbound : Tendsto (fun R : ℝ => 2 * M *
      (T + |(N R : ℝ) * H R - T| + |(K R : ℝ) * H R - T|) *
      (|(N R : ℝ) * H R - T| + |(K R : ℝ) * H R - T|)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => 2 * M *
        (T + |(N R : ℝ) * H R - T| + |(K R : ℝ) * H R - T|)) atTop (𝓝 (2 * M * (T + 0 + 0))) :=
      (((tendsto_const_nhds.add hAgap).add hBgap).const_mul (2 * M))
    have hsum0 : Tendsto (fun R : ℝ => |(N R : ℝ) * H R - T| + |(K R : ℝ) * H R - T|)
        atTop (𝓝 0) := by simpa using hAgap.add hBgap
    have h3 := h1.mul hsum0
    simp only [mul_zero, add_zero] at h3
    exact h3
  have hdiff : Tendsto (fun R => S R - I R) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hHpos] with R hR
    have hA0 : (0 : ℝ) ≤ (N R : ℝ) * H R := by positivity
    have hB0 : (0 : ℝ) ≤ (K R : ℝ) * H R := by positivity
    have hSI : S R = ∫ u in Set.Ico (0 : ℝ) ((N R : ℝ) * H R),
        ∫ v in Set.Ico (0 : ℝ) ((K R : ℝ) * H R),
          (fun s t => f (s + c R) (t + c' R)) (meshFloor (H R) u) (meshFloor (H R) v) := by
      rw [integral2_meshFloor_eq_sum_rect hR (N R) (K R)
        (fun s t => f (s + c R) (t + c' R))]
    have hb := abs_integral2_Ico_sub_le_rect (h := H R) hA0 hB0 hT
      (fun s t => f (s + c R) (t + c' R)) M hM0 (fun u v => hM _ _)
    rw [hSI]
    simpa [hIdef, hPdef, hQdef] using hb
  have hsum := hdiff.add hIlim
  simpa using hsum

/-! ### The horizons of the two sublattices

`⌊R^2T⌋` indices split into `⌈⌊R^2T⌋/2⌉` even ones and `⌊⌊R^2T⌋/2⌋` odd ones, and
each sublattice has mesh width `2R^{-2}`, so its horizon is within one mesh step
of `T` on either side. -/

/-- A horizon within a bounded number of mesh steps of `R^2 T` gives a mesh
horizon converging to `T`. -/
theorem tendsto_abs_horizon {T : ℝ} (m : ℝ → ℕ) (C : ℝ)
    (hm : ∀ᶠ R : ℝ in atTop, |(m R : ℝ) - R ^ 2 * T| ≤ C) :
    Tendsto (fun R : ℝ => |(m R : ℝ) * (R ^ 2)⁻¹ - T|) atTop (𝓝 0) := by
  have hlim : Tendsto (fun R : ℝ => C * (R ^ 2)⁻¹) atTop (𝓝 0) := by
    have h2 : Tendsto (fun R : ℝ => (R ^ 2)⁻¹) atTop (𝓝 0) :=
      Filter.Tendsto.inv_tendsto_atTop (tendsto_pow_atTop (by norm_num))
    simpa using h2.const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hm, eventually_gt_atTop (0 : ℝ)] with R hR hRpos
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hid : (m R : ℝ) * (R ^ 2)⁻¹ - T = ((m R : ℝ) - R ^ 2 * T) * (R ^ 2)⁻¹ := by
    field_simp
  rw [Real.norm_eq_abs, abs_abs, hid, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (R ^ 2)⁻¹)]
  exact mul_le_mul_of_nonneg_right hR (by positivity)

variable {T : ℝ}

/-- The even-index horizon of the time mesh. -/
noncomputable def evenHorizon (T : ℝ) (R : ℝ) : ℕ := (⌊R ^ 2 * T⌋₊ + 1) / 2

/-- The odd-index horizon of the time mesh. -/
noncomputable def oddHorizon (T : ℝ) (R : ℝ) : ℕ := ⌊R ^ 2 * T⌋₊ / 2

theorem tendsto_evenHorizon (hT : 0 ≤ T) :
    Tendsto (fun R : ℝ => |(evenHorizon T R : ℝ) * (2 * (R ^ 2)⁻¹) - T|) atTop (𝓝 0) := by
  have hconv : ∀ R : ℝ, (evenHorizon T R : ℝ) * (2 * (R ^ 2)⁻¹)
      = ((2 * evenHorizon T R : ℕ) : ℝ) * (R ^ 2)⁻¹ := by
    intro R; push_cast; ring
  simp only [hconv]
  refine tendsto_abs_horizon (fun R => 2 * evenHorizon T R) 2 ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hTR : (0 : ℝ) ≤ R ^ 2 * T := by positivity
  have h1 : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le hTR
  have h2 : R ^ 2 * T < ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcase : 2 * evenHorizon T R = ⌊R ^ 2 * T⌋₊ ∨ 2 * evenHorizon T R = ⌊R ^ 2 * T⌋₊ + 1 := by
    unfold evenHorizon; omega
  rcases hcase with hc | hc <;> rw [hc] <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

theorem tendsto_oddHorizon (hT : 0 ≤ T) :
    Tendsto (fun R : ℝ => |(oddHorizon T R : ℝ) * (2 * (R ^ 2)⁻¹) - T|) atTop (𝓝 0) := by
  have hconv : ∀ R : ℝ, (oddHorizon T R : ℝ) * (2 * (R ^ 2)⁻¹)
      = ((2 * oddHorizon T R : ℕ) : ℝ) * (R ^ 2)⁻¹ := by
    intro R; push_cast; ring
  simp only [hconv]
  refine tendsto_abs_horizon (fun R => 2 * oddHorizon T R) 2 ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hTR : (0 : ℝ) ≤ R ^ 2 * T := by positivity
  have h1 : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le hTR
  have h2 : R ^ 2 * T < ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcase : 2 * oddHorizon T R = ⌊R ^ 2 * T⌋₊ ∨ 2 * oddHorizon T R + 1 = ⌊R ^ 2 * T⌋₊ := by
    unfold oddHorizon; omega
  rcases hcase with hc | hc
  · rw [hc]; rw [abs_le]; constructor <;> linarith
  · have hcr : ((2 * oddHorizon T R : ℕ) : ℝ) = ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - 1 := by
      have h3 := congrArg (fun n : ℕ => (n : ℝ)) hc
      push_cast at h3 ⊢
      linarith
    rw [hcr, abs_le]
    constructor <;> linarith

/-! ### The parity-restricted double time sums

This is the "density `1/2`" of `sandpile.tex:1157-1161`, proved rather than
assumed: restricting the double time sum to the pairs `(a,b)` whose total has a
prescribed parity halves the limit.  Together with the factor `2` of the local
central limit theorem quoted there, the two cancel. -/

/-- **The double time sum over the pairs of even total converges to half the
double time integral.** -/
theorem tendsto_sum2_even_parity {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u v, |f u v| ≤ M) :
    Tendsto (fun R : ℝ =>
        ∑ p ∈ ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
          (fun p : ℕ × ℕ => Even (p.1 + p.2)),
          f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      atTop (𝓝 ((∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 2)) := by
  have hHpos : ∀ᶠ R : ℝ in atTop, 0 < 2 * (R ^ 2)⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    positivity
  have hinv : Tendsto (fun R : ℝ => (R ^ 2)⁻¹) atTop (𝓝 0) :=
    Filter.Tendsto.inv_tendsto_atTop (tendsto_pow_atTop (by norm_num))
  have hHlim : Tendsto (fun R : ℝ => 2 * (R ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul 2
  have hEE := tendsto_sum2_of_family_pair hT f hf M hM0 hM
    (fun R : ℝ => 2 * (R ^ 2)⁻¹) (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
    (evenHorizon T) (evenHorizon T) hHpos hHlim tendsto_const_nhds tendsto_const_nhds
    (tendsto_evenHorizon hT) (tendsto_evenHorizon hT)
  have hOO := tendsto_sum2_of_family_pair hT f hf M hM0 hM
    (fun R : ℝ => 2 * (R ^ 2)⁻¹) (fun R : ℝ => (R ^ 2)⁻¹) (fun R : ℝ => (R ^ 2)⁻¹)
    (oddHorizon T) (oddHorizon T) hHpos hHlim hinv hinv
    (tendsto_oddHorizon hT) (tendsto_oddHorizon hT)
  have hrw : ∀ R : ℝ,
      (∑ p ∈ ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
          (fun p : ℕ × ℕ => Even (p.1 + p.2)),
          f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      = (∑ a ∈ Finset.range (evenHorizon T R), ∑ b ∈ Finset.range (evenHorizon T R),
            f ((a : ℝ) * (2 * (R ^ 2)⁻¹) + 0) ((b : ℝ) * (2 * (R ^ 2)⁻¹) + 0)
              * (2 * (R ^ 2)⁻¹) * (2 * (R ^ 2)⁻¹)) / 4
        + (∑ a ∈ Finset.range (oddHorizon T R), ∑ b ∈ Finset.range (oddHorizon T R),
            f ((a : ℝ) * (2 * (R ^ 2)⁻¹) + (R ^ 2)⁻¹) ((b : ℝ) * (2 * (R ^ 2)⁻¹) + (R ^ 2)⁻¹)
              * (2 * (R ^ 2)⁻¹) * (2 * (R ^ 2)⁻¹)) / 4 := by
    intro R
    classical
    rw [sum_filter_even_sum_product ⌊R ^ 2 * T⌋₊
      (fun a b => f ((a : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)]
    congr 1
    · rw [sum_range_filter_even ⌊R ^ 2 * T⌋₊
        (fun a => ∑ b ∈ (Finset.range ⌊R ^ 2 * T⌋₊).filter (fun b => Even b),
          f ((a : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sum_range_filter_even ⌊R ^ 2 * T⌋₊
        (fun b => f (((2 * k : ℕ) : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      push_cast
      ring_nf
    · rw [sum_range_filter_odd ⌊R ^ 2 * T⌋₊
        (fun a => ∑ b ∈ (Finset.range ⌊R ^ 2 * T⌋₊).filter (fun b => ¬ Even b),
          f ((a : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sum_range_filter_odd ⌊R ^ 2 * T⌋₊
        (fun b => f (((2 * k + 1 : ℕ) : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹)
          * (R ^ 2)⁻¹ * (R ^ 2)⁻¹),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      push_cast
      ring_nf
  simp only [hrw]
  have hsum := (hEE.div_const 4).add (hOO.div_const 4)
  have hval : (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 4
      + (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 4
      = (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 2 := by ring
  rw [← hval]
  exact hsum

/-- **The double time sum over the pairs of odd total converges to half the
double time integral.** -/
theorem tendsto_sum2_odd_parity {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u v, |f u v| ≤ M) :
    Tendsto (fun R : ℝ =>
        ∑ p ∈ ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
          (fun p : ℕ × ℕ => ¬ Even (p.1 + p.2)),
          f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      atTop (𝓝 ((∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 2)) := by
  have hHpos : ∀ᶠ R : ℝ in atTop, 0 < 2 * (R ^ 2)⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    positivity
  have hinv : Tendsto (fun R : ℝ => (R ^ 2)⁻¹) atTop (𝓝 0) :=
    Filter.Tendsto.inv_tendsto_atTop (tendsto_pow_atTop (by norm_num))
  have hHlim : Tendsto (fun R : ℝ => 2 * (R ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul 2
  have hEE := tendsto_sum2_of_family_pair hT f hf M hM0 hM
    (fun R : ℝ => 2 * (R ^ 2)⁻¹) (fun _ : ℝ => (0 : ℝ)) (fun R : ℝ => (R ^ 2)⁻¹)
    (evenHorizon T) (oddHorizon T) hHpos hHlim tendsto_const_nhds hinv
    (tendsto_evenHorizon hT) (tendsto_oddHorizon hT)
  have hOO := tendsto_sum2_of_family_pair hT f hf M hM0 hM
    (fun R : ℝ => 2 * (R ^ 2)⁻¹) (fun R : ℝ => (R ^ 2)⁻¹) (fun _ : ℝ => (0 : ℝ))
    (oddHorizon T) (evenHorizon T) hHpos hHlim hinv tendsto_const_nhds
    (tendsto_oddHorizon hT) (tendsto_evenHorizon hT)
  have hrw : ∀ R : ℝ,
      (∑ p ∈ ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
          (fun p : ℕ × ℕ => ¬ Even (p.1 + p.2)),
          f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      = (∑ a ∈ Finset.range (evenHorizon T R), ∑ b ∈ Finset.range (oddHorizon T R),
            f ((a : ℝ) * (2 * (R ^ 2)⁻¹) + 0) ((b : ℝ) * (2 * (R ^ 2)⁻¹) + (R ^ 2)⁻¹)
              * (2 * (R ^ 2)⁻¹) * (2 * (R ^ 2)⁻¹)) / 4
        + (∑ a ∈ Finset.range (oddHorizon T R), ∑ b ∈ Finset.range (evenHorizon T R),
            f ((a : ℝ) * (2 * (R ^ 2)⁻¹) + (R ^ 2)⁻¹) ((b : ℝ) * (2 * (R ^ 2)⁻¹) + 0)
              * (2 * (R ^ 2)⁻¹) * (2 * (R ^ 2)⁻¹)) / 4 := by
    intro R
    classical
    rw [sum_filter_odd_sum_product ⌊R ^ 2 * T⌋₊
      (fun a b => f ((a : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)]
    congr 1
    · rw [sum_range_filter_even ⌊R ^ 2 * T⌋₊
        (fun a => ∑ b ∈ (Finset.range ⌊R ^ 2 * T⌋₊).filter (fun b => ¬ Even b),
          f ((a : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sum_range_filter_odd ⌊R ^ 2 * T⌋₊
        (fun b => f (((2 * k : ℕ) : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      push_cast
      ring_nf
    · rw [sum_range_filter_odd ⌊R ^ 2 * T⌋₊
        (fun a => ∑ b ∈ (Finset.range ⌊R ^ 2 * T⌋₊).filter (fun b => Even b),
          f ((a : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sum_range_filter_even ⌊R ^ 2 * T⌋₊
        (fun b => f (((2 * k + 1 : ℕ) : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹)
          * (R ^ 2)⁻¹ * (R ^ 2)⁻¹),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      push_cast
      ring_nf
  simp only [hrw]
  have hsum := (hEE.div_const 4).add (hOO.div_const 4)
  have hval : (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 4
      + (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 4
      = (∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 2 := by ring
  rw [← hval]
  exact hsum

/-- **A double Riemann sum is stable under a uniform perturbation of its
integrand.**  The integrand of the paper's time sum depends on `R` through the
local central limit theorem, and this is what reduces it to a FIXED integrand:
two integrands within `η` of each other have Riemann sums within
`(N H)² η` of each other, and `N H` is the horizon, which stays bounded. -/
theorem abs_sum2_sub_le {N : ℕ} {H η : ℝ} (hH : 0 ≤ H)
    (F G : ℕ → ℕ → ℝ) (h : ∀ a b, |F a b - G a b| ≤ η) :
    |(∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, F a b * H * H)
        - ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, G a b * H * H|
      ≤ ((N : ℝ) * H) ^ 2 * η := by
  have hid : (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, F a b * H * H)
      - ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, G a b * H * H
      = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, (F a b - G a b) * H * H := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hid]
  calc |∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, (F a b - G a b) * H * H|
      ≤ ∑ a ∈ Finset.range N, |∑ b ∈ Finset.range N, (F a b - G a b) * H * H| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.range N, (N : ℝ) * (η * H * H) := by
        refine Finset.sum_le_sum fun a _ => ?_
        calc |∑ b ∈ Finset.range N, (F a b - G a b) * H * H|
            ≤ ∑ b ∈ Finset.range N, |(F a b - G a b) * H * H| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _b ∈ Finset.range N, η * H * H := by
              refine Finset.sum_le_sum fun b _ => ?_
              rw [abs_mul, abs_mul, abs_of_nonneg hH]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (h a b) hH) hH
          _ = (N : ℝ) * (η * H * H) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((N : ℝ) * H) ^ 2 * η := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

end Sandpile.Support
