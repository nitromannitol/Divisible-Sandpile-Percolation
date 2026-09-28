import Sandpile.Support.D4SmoothGradient
import Sandpile.Support.BlockIncrement

/-!
# The second moment of a smoothed increment

The second moment of a smoothed increment, for the first display of Step 2 of
`prop:d4-superdiffusive-limit` (`sandpile.tex:3374-3380`). Step 2 compares
`F_R = P^{n_R}E_{t_R-n_R}` with the constant `C_R` of its own parity class. The smoothing operator
has finite range, so the increment `F_R(x) - F_R(b)` is a FINITE linear combination
`∑_z(p_n(x,z)-p_n(b,z))E(z)` of the values of the error field
(`smoothing_increment_eq_finsetSum`), and Minkowski in `L²` bounds its second moment
(`integral_sq_smoothing_increment_le`, `integrable_sq_smoothing_increment`) by the square of the
`ℓ¹` gradient of the smoothing kernel times the uniform second moment of the field. With
`eq:rw-tv-gradient` squared (`Sandpile.exists_heatKernel_gradient_sq_four`) this is the paper's
`C(1+\log\log t_R)R^2/n_R` (`exists_integral_sq_smoothing_increment_four`). The parity-class
cancellation (`sum_parity_const_mul`) is what turns the second display of Step 2 into an estimate
on the imbalance between the two parity classes of the mesh.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- **A smoothed increment is a finite linear combination of the field.**  The
smoothing operator has range `n`, so `P^nX(x)-P^nX(b)` reads off the values of
`X` on the union of the two boxes. -/
theorem smoothing_increment_eq_finsetSum (X : Site d → ℝ) (n : ℕ) (x b : Site d) :
    (avg^[n] X) x - (avg^[n] X) b
      = ∑ z ∈ boxFinset x n ∪ boxFinset b n,
          (heatKernel d n x z - heatKernel d n b z) * X z := by
  classical
  have hsubx : boxFinset x n ⊆ boxFinset x n ∪ boxFinset b n := Finset.subset_union_left
  have hsubb : boxFinset b n ⊆ boxFinset x n ∪ boxFinset b n := Finset.subset_union_right
  have hx : (avg^[n] X) x = ∑ z ∈ boxFinset x n ∪ boxFinset b n, heatKernel d n x z * X z := by
    rw [avg_iterate_eq_finsetSum]
    refine Finset.sum_subset hsubx ?_
    intro z _ hz
    have h1 : heatKernel d n x z = 0 := by
      by_contra hne; exact hz (mem_boxFinset (heatKernel_support n x hne))
    simp [h1]
  have hb : (avg^[n] X) b = ∑ z ∈ boxFinset x n ∪ boxFinset b n, heatKernel d n b z * X z := by
    rw [avg_iterate_eq_finsetSum]
    refine Finset.sum_subset hsubb ?_
    intro z _ hz
    have h1 : heatKernel d n b z = 0 := by
      by_contra hne; exact hz (mem_boxFinset (heatKernel_support n b hne))
    simp [h1]
  rw [hx, hb, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun z _ => by ring

/-- **A smoothed increment has an integrable square** as soon as every value of
the field has one: the increment is a finite combination of those values. -/
theorem integrable_sq_smoothing_increment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Site d → ℝ) (n : ℕ) (x b : Site d)
    (hmeas : ∀ z : Site d, AEStronglyMeasurable (fun ω => X ω z) P)
    (hint : ∀ z : Site d, Integrable (fun ω => (X ω z) ^ 2) P) :
    Integrable (fun ω => ((avg^[n] (X ω)) x - (avg^[n] (X ω)) b) ^ 2) P := by
  classical
  set S : Finset (Site d) := boxFinset x n ∪ boxFinset b n with hS
  set c : Site d → ℝ := fun z => heatKernel d n x z - heatKernel d n b z with hc
  have hrep : ∀ ω : Ω, (avg^[n] (X ω)) x - (avg^[n] (X ω)) b = ∑ z ∈ S, c z * X ω z :=
    fun ω => smoothing_increment_eq_finsetSum (X ω) n x b
  have hmeasS : AEStronglyMeasurable (fun ω => ∑ z ∈ S, c z * X ω z) P := by
    have h := Finset.aestronglyMeasurable_sum (μ := P)
      (f := fun (z : Site d) (ω : Ω) => c z * X ω z) S (fun z _ => (hmeas z).const_mul (c z))
    have hfun : (∑ z ∈ S, fun ω : Ω => c z * X ω z) = fun ω : Ω => ∑ z ∈ S, c z * X ω z := by
      funext ω
      simp [Finset.sum_apply]
    rwa [hfun] at h
  have hmaj : Integrable (fun ω => (∑ z ∈ S, |c z|) * ∑ z ∈ S, |c z| * (X ω z) ^ 2) P :=
    (integrable_finsetSum S fun z _ => (hint z).const_mul _).const_mul _
  refine Integrable.mono' hmaj ((hmeasS.congr (Filter.Eventually.of_forall
    fun ω => (hrep ω).symm)).pow 2) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hrep ω]
  exact sq_finset_sum_mul_le S c (X ω)

/-- **The second moment of a smoothed increment.**  If every value of the field
has second moment at most `V`, then
`E(P^nX(x) - P^nX(b))² ≤ (∑_z|p_n(x,z)-p_n(b,z)|)²V`. -/
theorem integral_sq_smoothing_increment_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Site d → ℝ) (n : ℕ) (x b : Site d) (V : ℝ)
    (hint : ∀ z : Site d, Integrable (fun ω => (X ω z) ^ 2) P)
    (hV : ∀ z : Site d, ∫ ω, (X ω z) ^ 2 ∂P ≤ V) :
    ∫ ω, ((avg^[n] (X ω)) x - (avg^[n] (X ω)) b) ^ 2 ∂P ≤
      (∑' y : Site d, |heatKernel d n x y - heatKernel d n b y|) ^ 2 * V := by
  classical
  set S : Finset (Site d) := boxFinset x n ∪ boxFinset b n with hS_def
  set c : Site d → ℝ := fun z => heatKernel d n x z - heatKernel d n b z with hc_def
  have hsubx : boxFinset x n ⊆ S := Finset.subset_union_left
  have hsubb : boxFinset b n ⊆ S := Finset.subset_union_right
  have hzero : ∀ z : Site d, z ∉ S → c z = 0 := by
    intro z hz
    rw [Finset.mem_union, not_or] at hz
    have h1 : heatKernel d n x z = 0 := by
      by_contra hne; exact hz.1 (mem_boxFinset (heatKernel_support n x hne))
    have h2 : heatKernel d n b z = 0 := by
      by_contra hne; exact hz.2 (mem_boxFinset (heatKernel_support n b hne))
    simp [hc_def, h1, h2]
  have hrep : ∀ ω : Ω, (avg^[n] (X ω)) x - (avg^[n] (X ω)) b = ∑ z ∈ S, c z * X ω z := by
    intro ω
    have hx : (avg^[n] (X ω)) x = ∑ z ∈ S, heatKernel d n x z * X ω z := by
      rw [avg_iterate_eq_finsetSum]
      refine Finset.sum_subset hsubx ?_
      intro z _ hz
      have h1 : heatKernel d n x z = 0 := by
        by_contra hne; exact hz (mem_boxFinset (heatKernel_support n x hne))
      simp [h1]
    have hb : (avg^[n] (X ω)) b = ∑ z ∈ S, heatKernel d n b z * X ω z := by
      rw [avg_iterate_eq_finsetSum]
      refine Finset.sum_subset hsubb ?_
      intro z _ hz
      have h1 : heatKernel d n b z = 0 := by
        by_contra hne; exact hz (mem_boxFinset (heatKernel_support n b hne))
      simp [h1]
    rw [hx, hb, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by rw [hc_def]; ring
  have hcsum : ∑' y : Site d, |c y| = ∑ z ∈ S, |c z| := by
    refine tsum_eq_sum fun z hz => ?_
    rw [hzero z hz, abs_zero]
  have hcnn : (0 : ℝ) ≤ ∑ z ∈ S, |c z| := Finset.sum_nonneg fun z _ => abs_nonneg _
  have hV0 : (0 : ℝ) ≤ V := by
    refine le_trans ?_ (hV x)
    exact integral_nonneg fun ω => sq_nonneg _
  have hRint : Integrable (fun ω => (∑ z ∈ S, |c z|) * ∑ z ∈ S, |c z| * (X ω z) ^ 2) P :=
    (integrable_finsetSum S fun z _ => (hint z).const_mul _).const_mul _
  have hstep : ∫ ω, ((avg^[n] (X ω)) x - (avg^[n] (X ω)) b) ^ 2 ∂P ≤
      ∫ ω, ((∑ z ∈ S, |c z|) * ∑ z ∈ S, |c z| * (X ω z) ^ 2) ∂P := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) hRint
      (Filter.Eventually.of_forall fun ω => ?_)
    show ((avg^[n] (X ω)) x - (avg^[n] (X ω)) b) ^ 2 ≤
      (∑ z ∈ S, |c z|) * ∑ z ∈ S, |c z| * (X ω z) ^ 2
    rw [hrep ω]
    exact sq_finset_sum_mul_le S c (X ω)
  refine hstep.trans ?_
  rw [integral_const_mul, integral_finsetSum S fun z _ => (hint z).const_mul _]
  have hinner : ∑ z ∈ S, ∫ ω, |c z| * (X ω z) ^ 2 ∂P ≤ (∑ z ∈ S, |c z|) * V := by
    have hterm : ∀ z ∈ S, ∫ ω, |c z| * (X ω z) ^ 2 ∂P ≤ |c z| * V := by
      intro z _
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hV z) (abs_nonneg _)
    calc ∑ z ∈ S, ∫ ω, |c z| * (X ω z) ^ 2 ∂P ≤ ∑ z ∈ S, |c z| * V :=
          Finset.sum_le_sum hterm
      _ = (∑ z ∈ S, |c z|) * V := by rw [← Finset.sum_mul]
  calc (∑ z ∈ S, |c z|) * ∑ z ∈ S, ∫ ω, |c z| * (X ω z) ^ 2 ∂P
      ≤ (∑ z ∈ S, |c z|) * ((∑ z ∈ S, |c z|) * V) :=
        mul_le_mul_of_nonneg_left hinner hcnn
    _ = (∑' y : Site d, |c y|) ^ 2 * V := by rw [hcsum]; ring

/-- **Step 2's first display, at a single site.**  For two sites of equal parity,
`E(P^nX(x) - P^nX(b))² ≤ C|x-b|²V/n`.  On the box of radius `CR` that the
rescaled domain meets, and with `V = C(1+\log\log t_R)` from
`prop:d4-pointwise-linearization`, this is the paper's `C(1+\log\log t_R)R²/n_R`
(`sandpile.tex:3374-3380`). -/
theorem exists_integral_sq_smoothing_increment_four
    (hHK : Sandpile.External.HeatKernelBounds) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (X : Ω → Site 4 → ℝ) (V : ℝ),
      (∀ z : Site 4, Integrable (fun ω => (X ω z) ^ 2) P) →
      (∀ z : Site 4, ∫ ω, (X ω z) ^ 2 ∂P ≤ V) →
      ∀ n : ℕ, 1 ≤ n → ∀ x b : Site 4, Sandpile.External.SameParity x b →
        ∫ ω, ((avg^[n] (X ω)) x - (avg^[n] (X ω)) b) ^ 2 ∂P ≤
          C * Sandpile.External.latticeDist x b ^ 2 / (n : ℝ) * V := by
  obtain ⟨C, hC, hgrad⟩ := exists_heatKernel_gradient_sq_four hHK
  refine ⟨C, hC, fun P X V hint hV n hn x b hpar => ?_⟩
  have hV0 : (0 : ℝ) ≤ V := le_trans (integral_nonneg fun ω => sq_nonneg _) (hV x)
  refine le_trans (integral_sq_smoothing_increment_le P X n x b V hint hV) ?_
  exact mul_le_mul_of_nonneg_right (hgrad n hn x b hpar) hV0

/-- **The parity-class cancellation of Step 2** (`sandpile.tex:3374-3377`).  A
field that is constant on each parity class pairs against weights of TOTAL mass
zero through the difference of the two constants and the mass of ONE class
alone: `∑_x C(x)m(x) = (c₀-c₁)∑_{x even}m(x)`.  This is what turns the second
display of Step 2 into an estimate on the imbalance between the two parity
classes of the mesh, the `ω`-shift having already made the total mass zero. -/
theorem sum_parity_const_mul (s : Finset (Site d)) (C m : Site d → ℝ)
    (c₀ c₁ : ℝ)
    [DecidablePred fun x : Site d => Sandpile.External.SameParity x 0]
    (hC₀ : ∀ x : Site d, Sandpile.External.SameParity x 0 → C x = c₀)
    (hC₁ : ∀ x : Site d, ¬ Sandpile.External.SameParity x 0 → C x = c₁)
    (hm : ∑ x ∈ s, m x = 0) :
    ∑ x ∈ s, C x * m x =
      (c₀ - c₁) * ∑ x ∈ s.filter (fun x => Sandpile.External.SameParity x 0), m x := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun x : Site d => Sandpile.External.SameParity x 0) (fun x => C x * m x)
  have heven : ∑ x ∈ s.filter (fun x => Sandpile.External.SameParity x 0), C x * m x =
      c₀ * ∑ x ∈ s.filter (fun x => Sandpile.External.SameParity x 0), m x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hC₀ x (Finset.mem_filter.mp hx).2]
  have hodd : ∑ x ∈ s.filter (fun x => ¬ Sandpile.External.SameParity x 0), C x * m x =
      c₁ * ∑ x ∈ s.filter (fun x => ¬ Sandpile.External.SameParity x 0), m x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hC₁ x (Finset.mem_filter.mp hx).2]
  have hmass := Finset.sum_filter_add_sum_filter_not s
    (fun x : Site d => Sandpile.External.SameParity x 0) m
  rw [hm] at hmass
  rw [← hsplit, heven, hodd]
  have : ∑ x ∈ s.filter (fun x => ¬ Sandpile.External.SameParity x 0), m x =
      -∑ x ∈ s.filter (fun x => Sandpile.External.SameParity x 0), m x := by linarith
  rw [this]
  ring

end Sandpile
