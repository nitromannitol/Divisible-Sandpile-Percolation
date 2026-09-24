/-
The Gaussian Green field of `eq:dgt4-infinite-green-field` as an isonormal
process.

In the Gaussian case (a) of `sandpile.tex:5454-5455` the scenery is a centred
Gaussian field of variance `v`, and `V_∞(x) = ∑_z G(x,z)ζ(z)` is the limit of
its partial sums over the boxes.  Here that limit is identified: the boxes
exhaust `ℤ^d`, the square tails of the Green function decay like `1/n`
(`Support/LinGreenTail.lean`), and the general convergence theorem of
`Support/LinGaussIso.lean` therefore identifies the box limit, almost surely,
with the isonormal image of the coefficient family `z ↦ G(x,z)`.  That is what
makes `infiniteGreenField` a genuine Gaussian field rather than the junk value
of a divergent series, and it is what the proof of `lem:dgt4-path-survival`
uses when it applies the normal comparison inequality to `(J(x))_{x∈Λ}`.
-/
import LatticeProb.Gauss.IsonormalSum
import Sandpile.Support.LinGreenTail

open LatticeProb.Isonormal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The Green function at a site, as a square-summable family of coefficients. -/
noncomputable def greenLp (d : ℕ) (hd : 5 ≤ d) (x : Site d) : lp (fun _ : Site d => ℝ) 2 :=
  ⟨fun z => green d x z, by
    refine (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).2 ?_
    refine (summable_green_sq hd x).congr fun z => ?_
    rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]⟩

theorem coeFn_greenLp (hd : 5 ≤ d) (x : Site d) :
    ((greenLp d hd x : lp (fun _ : Site d => ℝ) 2) : Site d → ℝ) = fun z => green d x z := rfl

/-- The boxes of `eq:dgt4-infinite-green-field` are the boxes of the supremum
distance. -/
theorem greenFieldBox_toFinset (d n : ℕ) :
    (greenFieldBox d n).toFinset = boxFinset (0 : Site d) n := by
  ext z
  simp only [Set.mem_toFinset, mem_greenFieldBox_iff, mem_boxFinset_iff]

/-- The partial sums of the Green field over the boxes converge almost surely to
the isonormal image of the Green coefficients. -/
theorem ae_tendsto_greenPartialSum (hd : 5 ≤ d) (x : Site d) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      Tendsto (fun n => ∑ z ∈ boxFinset (0 : Site d) n, green d x z * ω z) atTop
        (𝓝 (⇑(LatticeProb.gaussIso (greenLp d hd x)) ω)) := by
  obtain ⟨C, hC, hCtail⟩ := exists_green_tail_sq_le hd x
  refine ae_tendsto_partialSum (greenLp d hd x) (fun n => boxFinset (0 : Site d) n) C hC ?_
  intro n
  have hset : ((boxFinset (0 : Site d) n : Finset (Site d)) : Set (Site d))
      = greenFieldBox d n := by
    ext z
    simp only [Finset.mem_coe, mem_boxFinset_iff, mem_greenFieldBox_iff]
  rw [hset]
  exact hCtail n

/-- **The Gaussian Green field is the isonormal image of the Green
coefficients.**  For a centred Gaussian scenery of any scale the box limit of
`eq:dgt4-infinite-green-field` exists almost surely and equals that image. -/
theorem ae_infiniteGreenField_eq (hd : 5 ≤ d) (x : Site d) (c : ℝ) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      infiniteGreenField (fun z => c * ω z) x
        = c * ⇑(LatticeProb.gaussIso (greenLp d hd x)) ω := by
  filter_upwards [ae_tendsto_greenPartialSum hd x] with ω hω
  have hpart : ∀ n : ℕ, infiniteGreenFieldPartial n (fun z => c * ω z) x
      = c * ∑ z ∈ boxFinset (0 : Site d) n, green d x z * ω z := by
    intro n
    rw [infiniteGreenFieldPartial,
      Finset.sum_set_coe (f := fun z : Site d => green d x z * (c * ω z)) (greenFieldBox d n),
      greenFieldBox_toFinset, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  have htend : Tendsto (fun n => infiniteGreenFieldPartial n (fun z => c * ω z) x) atTop
      (𝓝 (c * ⇑(LatticeProb.gaussIso (greenLp d hd x)) ω)) := by
    simp only [hpart]
    exact hω.const_mul c
  have hex : ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n (fun z => c * ω z) x) atTop (𝓝 L) :=
    ⟨_, htend⟩
  rw [infiniteGreenField, dif_pos hex]
  exact tendsto_nhds_unique (Classical.choose_spec hex) htend

/-- The box of radius `n - |y|_∞` around the origin sits inside the box of radius
`n` around `y`. -/
theorem boxFinset_zero_subset (y : Site d) (n : ℕ) (hn : boxDist 0 y ≤ n) :
    boxFinset (0 : Site d) (n - boxDist 0 y) ⊆ boxFinset y n := by
  intro z hz
  rw [mem_boxFinset_iff] at hz ⊢
  have h1 : boxDist y z ≤ boxDist y 0 + boxDist 0 z := boxDist_trans y 0 z
  have h2 : boxDist y 0 = boxDist 0 y := boxDist_comm y 0
  omega

/-- The partial sums of the Green field over the boxes centred at any site
converge to the same isonormal image. -/
theorem ae_tendsto_greenPartialSum_shift (hd : 5 ≤ d) (x y : Site d) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      Tendsto (fun n => ∑ z ∈ boxFinset y n, green d x z * ω z) atTop
        (𝓝 (⇑(LatticeProb.gaussIso (greenLp d hd x)) ω)) := by
  obtain ⟨C, hC, hCtail⟩ := exists_green_tail_sq_le_of_boxSubset hd x
    (fun n => boxFinset y n) (boxDist 0 y) (fun n hn => boxFinset_zero_subset y n hn)
  exact ae_tendsto_partialSum (greenLp d hd x) (fun n => boxFinset y n) C hC hCtail

/-- **Translation equivariance of the box limit.**  Shifting the scenery by `y`
moves the field of `eq:dgt4-infinite-green-field` from `x` to `x + y`.  The boxes
of the definition are centred at the origin, so the two limits are taken along
different exhaustions; they agree because the tails of the Green function over
the boxes centred at `y` decay at the same rate. -/
theorem ae_infiniteGreenField_shift (hd : 5 ≤ d) (x y : Site d) (c : ℝ) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      infiniteGreenField (fun z => c * ω (z + y)) x
        = infiniteGreenField (fun z => c * ω z) (x + y) := by
  filter_upwards [ae_tendsto_greenPartialSum_shift hd (x + y) y,
    ae_infiniteGreenField_eq hd (x + y) c] with ω hω hval
  have hbox : ∀ n : ℕ, boxFinset y n
      = (boxFinset (0 : Site d) n).map ⟨fun z => z + y, add_left_injective y⟩ := by
    intro n
    ext w
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, mem_boxFinset_iff]
    constructor
    · intro hw
      refine ⟨w - y, ?_, by ring⟩
      rw [← boxDist_sub y w]
      exact hw
    · rintro ⟨z, hz, rfl⟩
      rw [boxDist_sub y (z + y)]
      simpa using hz
  have hgreen : ∀ z : Site d, green d x z = green d (x + y) (z + y) := by
    intro z
    rw [green_shift x z, green_shift (x + y) (z + y)]
    congr 1
    abel
  have hpart : ∀ n : ℕ, infiniteGreenFieldPartial n (fun z => c * ω (z + y)) x
      = c * ∑ w ∈ boxFinset y n, green d (x + y) w * ω w := by
    intro n
    rw [infiniteGreenFieldPartial,
      Finset.sum_set_coe (f := fun z : Site d => green d x z * (c * ω (z + y)))
        (greenFieldBox d n),
      greenFieldBox_toFinset, hbox n, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [Function.Embedding.coeFn_mk]
    rw [hgreen z]
    ring
  have htend : Tendsto (fun n => infiniteGreenFieldPartial n (fun z => c * ω (z + y)) x) atTop
      (𝓝 (c * ⇑(LatticeProb.gaussIso (greenLp d hd (x + y))) ω)) := by
    simp only [hpart]
    exact hω.const_mul c
  have hex : ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n (fun z => c * ω (z + y)) x) atTop (𝓝 L) :=
    ⟨_, htend⟩
  rw [infiniteGreenField, dif_pos hex, hval]
  exact tendsto_nhds_unique (Classical.choose_spec hex) htend

/-- The i.i.d. Gaussian scenery of variance `v` is the standard Gaussian product
law scaled by `√v`. -/
theorem iidLaw_gaussianReal_eq_map (d : ℕ) (v : ℝ≥0) :
    LatticeProb.iidLaw d (gaussianReal 0 v)
      = (LatticeProb.gaussLaw (Site d)).map (fun ω z => Real.sqrt (v : ℝ) * ω z) := by
  unfold LatticeProb.iidLaw LatticeProb.gaussLaw
  rw [Measure.infinitePi_map_pi (fun _ : Site d => gaussianReal 0 1)
    (f := fun _ : Site d => fun x : ℝ => Real.sqrt (v : ℝ) * x) (fun _ => by fun_prop)]
  refine congrArg _ ?_
  funext i
  rw [ProbabilityTheory.gaussianReal_map_const_mul]
  congr 1
  · simp
  · rw [mul_one]
    ext
    simp [Real.sq_sqrt v.coe_nonneg]

/-- The inner product of two Green coefficient families is the Green covariance
`∑_z G(x,z)G(y,z)` of `eq:dgt4-intersection-first-moment`. -/
theorem inner_greenLp (hd : 5 ≤ d) (x y : Site d) :
    (inner ℝ (greenLp d hd x) (greenLp d hd y) : ℝ)
      = ∑' z : Site d, green d x z * green d y z := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun z => ?_
  simp only [coeFn_greenLp, RCLike.inner_apply, conj_trivial]
  ring

/-- **The finite-dimensional laws of the Gaussian Green field.**  Under a centred
Gaussian scenery of variance `v` the vector `(V_∞(x))_{x∈Λ}` of
`eq:dgt4-infinite-green-field` is a centred Gaussian vector whose covariance is
`Var(ζ(0)) ∑_z G(x,z)G(y,z)`, the matrix that `sandpile.tex:5450-5452` feeds to
the normal comparison inequality. -/
theorem map_infiniteGreenField_vector (hd : 5 ≤ d) (v : ℝ≥0) {m : ℕ} (xs : Fin m → Site d) :
    (LatticeProb.gaussLaw (Site d)).map
        (fun ω => (WithLp.toLp 2
            (fun i => infiniteGreenField (fun z => Real.sqrt (v : ℝ) * ω z) (xs i)) :
          EuclideanSpace ℝ (Fin m)))
      = multivariateGaussian 0
          (Matrix.of fun i j =>
            (v : ℝ) * ∑' z : Site d, green d (xs i) z * green d (xs j) z) := by
  classical
  have hvn : (0 : ℝ) ≤ (v : ℝ) := v.coe_nonneg
  have hcsq : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) := Real.mul_self_sqrt hvn
  have h1 : ∀ i : Fin m, ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      infiniteGreenField (fun z => Real.sqrt (v : ℝ) * ω z) (xs i)
        = ⇑(LatticeProb.gaussIso (Real.sqrt (v : ℝ) • greenLp d hd (xs i))) ω := by
    intro i
    filter_upwards [ae_infiniteGreenField_eq hd (xs i) (Real.sqrt (v : ℝ)),
      Lp.coeFn_smul (Real.sqrt (v : ℝ))
        (LatticeProb.gaussIso (greenLp d hd (xs i)))] with ω hω hsm
    rw [hω, map_smul, hsm]
    simp
  have hae : (fun ω : Site d → ℝ => (WithLp.toLp 2
        (fun i => infiniteGreenField (fun z => Real.sqrt (v : ℝ) * ω z) (xs i)) :
        EuclideanSpace ℝ (Fin m)))
      =ᵐ[LatticeProb.gaussLaw (Site d)]
        fun ω => (WithLp.toLp 2 (fun i =>
          ⇑(LatticeProb.gaussIso (Real.sqrt (v : ℝ) • greenLp d hd (xs i))) ω) :
          EuclideanSpace ℝ (Fin m)) := by
    filter_upwards [ae_all_iff.2 h1] with ω hω
    congr 1
    funext i
    exact hω i
  rw [Measure.map_congr hae,
    map_gaussIso_vector (fun i => Real.sqrt (v : ℝ) • greenLp d hd (xs i))]
  congr 1
  ext i j
  simp only [gramMatrix, Matrix.of_apply]
  rw [real_inner_smul_left, real_inner_smul_right, inner_greenLp, ← mul_assoc, hcsq]

end Sandpile
