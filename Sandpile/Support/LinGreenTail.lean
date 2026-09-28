import Sandpile.Support.InfiniteGreenField
import Sandpile.Support.Kernel
import Sandpile.External.GreenBoundsHighProved
import Sandpile.Support.LinAnnular

/-! # Green Function Square Tail

The square tail of the Green function outside a box.

The Gaussian branch of `lem:dgt4-path-survival` reads the field
`V_∞(x) = ∑_z G(x,z)ζ(z)` of `eq:dgt4-infinite-green-field` as the limit of its
partial sums over the boxes, and the rate at which those partial sums settle is
governed by the sum of `G(x,z)^2` over the complement of the box.  The `d ≥ 5`
tail estimate `eq:dgt4-green-tail` of `ssec:green-estimates`,
`∑_{|z| ≥ r} G(0,z)^2 ≤ C r^{4-d}`, is stated for the Euclidean norm and for the
origin; here it is moved to the supremum-norm boxes centred at the origin and to
an arbitrary site `x`, and its exponent `4-d ≤ -1` is read as the decay `1/(n+1)`
that the Borel-Cantelli argument of `Support/LinGaussField.lean` uses.
-/

namespace Sandpile

variable {d : ℕ}

/-- The Green function of the simple random walk depends on the difference of
its arguments. -/
theorem green_shift (x z : Site d) : green d x z = green d 0 (z - x) := by
  rw [Sandpile.External.green_eq_srwGreenInf, Sandpile.External.green_eq_srwGreenInf, sub_zero]

/-- The boxes of `eq:dgt4-infinite-green-field` are the balls of the supremum
distance. -/
theorem mem_greenFieldBox_iff {n : ℕ} {z : Site d} :
    z ∈ greenFieldBox d n ↔ boxDist 0 z ≤ n := by
  simp only [greenFieldBox, Set.mem_setOf_eq, boxDist, Finset.sup_le_iff, Finset.mem_univ,
    forall_const]
  constructor
  · intro hz i
    have h := hz i
    rw [Int.abs_eq_natAbs] at h
    have h2 : ((0 : Site d) i - z i).natAbs = (z i).natAbs := by simp
    rw [h2]
    exact_mod_cast h
  · intro hz i
    have h := hz i
    have h2 : ((0 : Site d) i - z i).natAbs = (z i).natAbs := by simp
    rw [h2] at h
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h

/-- The Green function is square summable in dimensions five and up. -/
theorem summable_green_sq (hd : 5 ≤ d) (x : Site d) :
    Summable (fun z : Site d => green d x z ^ 2) := by
  obtain ⟨-, hsum, -, -, -⟩ := Sandpile.External.greenBoundsHigh d hd
  have hgoal : (fun z : Site d => green d x z ^ 2)
      = (fun z : Site d => green d 0 z ^ 2) ∘ (Equiv.subRight x) := by
    funext z
    simp only [Function.comp_apply, Equiv.subRight_apply]
    rw [green_shift x z]
  rw [hgoal]
  exact ((Equiv.subRight x).summable_iff (f := fun z : Site d => green d 0 z ^ 2)).mpr hsum

/-- The box distance to a site is the box distance of the difference to the
origin. -/
theorem boxDist_sub (x z : Site d) : boxDist x z = boxDist 0 (z - x) := by
  refine Finset.sup_congr rfl fun i _ => ?_
  simp only [Pi.zero_apply, Pi.sub_apply, zero_sub, Int.natAbs_neg]
  omega

/-- The box distance is symmetric. -/
theorem boxDist_comm (x y : Site d) : boxDist x y = boxDist y x := by
  refine Finset.sup_congr rfl fun i _ => ?_
  omega

/-- The complement of the box of radius `n` around the origin sits inside the
complement of the Euclidean ball of radius `n + 1 - |x|_∞` around `x`. -/
theorem green_tail_sq_le_ball_tail (hd : 5 ≤ d) (x : Site d) (n : ℕ) (hn : boxDist 0 x ≤ n) :
    ∑' z : {z : Site d // z ∉ greenFieldBox d n}, green d x z ^ 2
      ≤ ∑' w : {w : Site d //
            ((n + 1 - boxDist 0 x : ℕ) : ℝ) ≤ Sandpile.External.latticeNorm w},
          green d 0 (w : Site d) ^ 2 := by
  set k := boxDist 0 x with hk
  set r := n + 1 - k with hr
  have hmem : ∀ z : Site d, z ∉ greenFieldBox d n →
      ((r : ℕ) : ℝ) ≤ Sandpile.External.latticeNorm (z - x) := by
    intro z hz
    have h1 : ¬ (boxDist 0 z ≤ n) := fun h => hz (mem_greenFieldBox_iff.mpr h)
    have h2 : boxDist 0 z ≤ boxDist 0 x + boxDist x z := boxDist_trans 0 x z
    have h3 : boxDist x z = boxDist 0 (z - x) := boxDist_sub x z
    have h4 : r ≤ boxDist 0 (z - x) := by omega
    have h5 := boxDist_le_latticeNorm (d := d) (by omega) (z - x)
    calc ((r : ℕ) : ℝ) ≤ ((boxDist 0 (z - x) : ℕ) : ℝ) := by exact_mod_cast h4
      _ ≤ Sandpile.External.latticeNorm (z - x) := h5
  have hinj : Function.Injective (fun z : {z : Site d // z ∉ greenFieldBox d n} =>
      (⟨(z : Site d) - x, hmem (z : Site d) z.2⟩ :
        {w : Site d // ((r : ℕ) : ℝ) ≤ Sandpile.External.latticeNorm w})) := by
    intro a b hab
    have h : (a : Site d) - x = (b : Site d) - x := congrArg Subtype.val hab
    exact Subtype.ext (sub_left_injective h)
  have hsum : Summable (fun w : {w : Site d //
      ((r : ℕ) : ℝ) ≤ Sandpile.External.latticeNorm w} => green d 0 (w : Site d) ^ 2) :=
    (summable_green_sq hd 0).subtype _
  have hcomp := tsum_comp_le_tsum_of_inj hsum (fun w => sq_nonneg _) hinj
  refine le_trans (le_of_eq ?_) hcomp
  exact tsum_congr fun z => by rw [green_shift x (z : Site d)]; rfl

/-- **The square tail outside a box.**  For every site the sum of `G(x,z)^2`
over the complement of the box of radius `n` decays at least like `1/(n+1)`. -/
theorem exists_green_tail_sq_le (hd : 5 ≤ d) (x : Site d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∑' z : {z : Site d // z ∉ greenFieldBox d n}, green d x z ^ 2 ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C₀, hC₀, htail⟩ := (Sandpile.External.greenBoundsHigh d hd).1
  have hMsum : Summable (fun z : Site d => green d x z ^ 2) := summable_green_sq hd x
  have hM0 : (0 : ℝ) ≤ ∑' z : Site d, green d x z ^ 2 := tsum_nonneg fun z => sq_nonneg _
  have hknn : (0 : ℝ) ≤ ((boxDist 0 x : ℕ) : ℝ) := Nat.cast_nonneg _
  have hprod : (0 : ℝ) ≤ (2 * ((boxDist 0 x : ℕ) : ℝ) + 1) * (∑' z : Site d, green d x z ^ 2) :=
    mul_nonneg (by linarith) hM0
  refine ⟨2 * C₀ + (2 * ((boxDist 0 x : ℕ) : ℝ) + 1) * (∑' z : Site d, green d x z ^ 2) + 1,
    by linarith, fun n => ?_⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle_M : (∑' z : {z : Site d // z ∉ greenFieldBox d n}, green d x z ^ 2)
      ≤ ∑' z : Site d, green d x z ^ 2 :=
    Summable.tsum_subtype_le (fun z : Site d => green d x z ^ 2) ((greenFieldBox d n)ᶜ)
      (fun z => sq_nonneg _) hMsum
  by_cases hcase : 2 * boxDist 0 x + 1 ≤ n
  · have hr1 : 1 ≤ n + 1 - boxDist 0 x := by omega
    have hcomp := green_tail_sq_le_ball_tail hd x n (by omega)
    have hext := (htail (n + 1 - boxDist 0 x) hr1).2.1
    have hrR : (1 : ℝ) ≤ ((n + 1 - boxDist 0 x : ℕ) : ℝ) := by exact_mod_cast hr1
    have hrpos : (0 : ℝ) < ((n + 1 - boxDist 0 x : ℕ) : ℝ) := by linarith
    have hexp : ((n + 1 - boxDist 0 x : ℕ) : ℝ) ^ (4 - (d : ℝ))
        ≤ (((n + 1 - boxDist 0 x : ℕ) : ℝ))⁻¹ := by
      have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have h1 := Real.rpow_le_rpow_of_exponent_le hrR
        (show (4 : ℝ) - (d : ℝ) ≤ -1 by linarith)
      rwa [Real.rpow_neg hrpos.le, Real.rpow_one] at h1
    have hgeo : (((n + 1 - boxDist 0 x : ℕ) : ℝ))⁻¹ ≤ 2 / ((n : ℝ) + 1) := by
      have h2 : (n : ℝ) + 1 ≤ 2 * ((n + 1 - boxDist 0 x : ℕ) : ℝ) := by
        have h3 : n + 1 ≤ 2 * (n + 1 - boxDist 0 x) := by omega
        exact_mod_cast h3
      rw [inv_eq_one_div, div_le_div_iff₀ hrpos hn1]
      linarith
    have hnum : C₀ * 2 ≤ 2 * C₀
        + (2 * ((boxDist 0 x : ℕ) : ℝ) + 1) * (∑' z : Site d, green d x z ^ 2) + 1 := by
      linarith
    calc (∑' z : {z : Site d // z ∉ greenFieldBox d n}, green d x z ^ 2)
        ≤ ∑' w : {w : Site d //
            ((n + 1 - boxDist 0 x : ℕ) : ℝ) ≤ Sandpile.External.latticeNorm w},
            green d 0 (w : Site d) ^ 2 := hcomp
      _ ≤ C₀ * ((n + 1 - boxDist 0 x : ℕ) : ℝ) ^ (4 - (d : ℝ)) := hext
      _ ≤ C₀ * (2 / ((n : ℝ) + 1)) := by nlinarith [le_trans hexp hgeo, hC₀.le]
      _ = C₀ * 2 / ((n : ℝ) + 1) := by ring
      _ ≤ (2 * C₀ + (2 * ((boxDist 0 x : ℕ) : ℝ) + 1)
            * (∑' z : Site d, green d x z ^ 2) + 1) / ((n : ℝ) + 1) := by
          rw [div_le_div_iff₀ hn1 hn1]
          nlinarith
  · refine le_trans hle_M ?_
    rw [le_div_iff₀ hn1]
    have hnk : (n : ℝ) + 1 ≤ 2 * ((boxDist 0 x : ℕ) : ℝ) + 1 := by
      have h3 : n ≤ 2 * boxDist 0 x := by omega
      have h4 := (Nat.cast_le (α := ℝ)).mpr h3
      push_cast at h4
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hnk hM0, hC₀.le]

/-- The tail of a summable series of nonnegative terms decreases when the set
removed grows. -/
theorem tsum_compl_mono {ι : Type*} {f : ι → ℝ} (hf : Summable f) (hnn : ∀ i, 0 ≤ f i)
    {A B : Set ι} (hAB : A ⊆ B) :
    ∑' z : {z : ι // z ∉ B}, f (z : ι) ≤ ∑' z : {z : ι // z ∉ A}, f (z : ι) := by
  have hsumA : Summable (fun z : {z : ι // z ∉ A} => f (z : ι)) := hf.subtype _
  have hinj : Function.Injective
      (fun z : {z : ι // z ∉ B} => (⟨(z : ι), fun hz => z.2 (hAB hz)⟩ : {z : ι // z ∉ A})) := by
    intro a b hab
    have h : (a : ι) = (b : ι) := by simpa using hab
    exact Subtype.ext h
  exact tsum_comp_le_tsum_of_inj hsumA (fun z => hnn (z : ι)) hinj

/-- **The square tail outside any set that contains a box.**  If the sets of a
sequence contain, from `n = m` on, the boxes of radius `n - m`, the square tails
of the Green function outside them still decay like `1/(n+1)`. -/
theorem exists_green_tail_sq_le_of_boxSubset (hd : 5 ≤ d) (x : Site d)
    (s : ℕ → Finset (Site d)) (m : ℕ)
    (hsub : ∀ n : ℕ, m ≤ n → boxFinset (0 : Site d) (n - m) ⊆ s n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∑' z : {z : Site d // z ∉ (s n : Set (Site d))}, green d x z ^ 2 ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C₀, hC₀, hC₀tail⟩ := exists_green_tail_sq_le hd x
  have hMsum : Summable (fun z : Site d => green d x z ^ 2) := summable_green_sq hd x
  have hM0 : (0 : ℝ) ≤ ∑' z : Site d, green d x z ^ 2 := tsum_nonneg fun z => sq_nonneg _
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine ⟨(C₀ + ∑' z : Site d, green d x z ^ 2) * ((m : ℝ) + 1), by nlinarith, fun n => ?_⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  by_cases hcase : m ≤ n
  · have hsubset : ((boxFinset (0 : Site d) (n - m) : Finset (Site d)) : Set (Site d))
        ⊆ ((s n : Finset (Site d)) : Set (Site d)) := by
      intro z hz
      exact Finset.mem_coe.mpr (hsub n hcase (Finset.mem_coe.mp hz))
    have hbox : ((boxFinset (0 : Site d) (n - m) : Finset (Site d)) : Set (Site d))
        = greenFieldBox d (n - m) := by
      ext z
      simp only [Finset.mem_coe, mem_boxFinset_iff, mem_greenFieldBox_iff]
    have hstep : (∑' z : {z : Site d // z ∉ ((s n : Finset (Site d)) : Set (Site d))},
          green d x z ^ 2)
        ≤ ∑' z : {z : Site d // z ∉ greenFieldBox d (n - m)}, green d x z ^ 2 := by
      rw [← hbox]
      exact tsum_compl_mono hMsum (fun z => sq_nonneg _) hsubset
    have hle := hC₀tail (n - m)
    have harith : C₀ / (((n - m : ℕ) : ℝ) + 1)
        ≤ (C₀ + ∑' z : Site d, green d x z ^ 2) * ((m : ℝ) + 1) / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) hn1]
      have hnm : ((n : ℝ) + 1) ≤ ((m : ℝ) + 1) * (((n - m : ℕ) : ℝ) + 1) := by
        have h1 : n + 1 ≤ (m + 1) * ((n - m) + 1) := by
          nlinarith [Nat.sub_add_cancel hcase]
        exact_mod_cast h1
      have hpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) + 1 := by positivity
      nlinarith [hC₀.le, hM0]
    exact le_trans hstep (le_trans hle harith)
  · have hle_M : (∑' z : {z : Site d // z ∉ ((s n : Finset (Site d)) : Set (Site d))},
        green d x z ^ 2) ≤ ∑' z : Site d, green d x z ^ 2 :=
      Summable.tsum_subtype_le (fun z : Site d => green d x z ^ 2)
        (((s n : Finset (Site d)) : Set (Site d))ᶜ) (fun z => sq_nonneg _) hMsum
    refine le_trans hle_M ?_
    rw [le_div_iff₀ hn1]
    have hnm : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have h1 : n + 1 ≤ m + 1 := by omega
      exact_mod_cast h1
    nlinarith [hC₀.le, hM0]

end Sandpile
