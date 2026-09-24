/-
The correlation gap `eq:dgt4-gaussian-correlation-gap` (`sandpile.tex:5160-5162`):

  "For each $z\ne0$, the Gaussians $V_\infty(z)$ and $V_\infty(0)$ are not
   proportional, so the Cauchy--Schwarz inequality is strict:
   $|\Cov(V_\infty(z),V_\infty(0))|<\Sigma^2$.  Moreover
   \eqref{eq:dgt4-intersection-first-moment} sends
   $|\Cov(V_\infty(z),V_\infty(0))|/\Sigma^2$ to zero as $|z|\to\infty$.  Hence
   $\sup_{z\ne0}|\Cov(V_\infty(z),V_\infty(0))|/\Sigma^2<1$."

This is the one input that Step 1 of `lem:dgt4-path-survival` still needed: the
near pairs of `sandpile.tex:5519` are the pairs at distance at most
`(\log R)^{2/(d-4)}`, and what makes their contribution vanish is exactly a bound
`ρ_* < 1` on the correlation that is uniform over all of them.

In the vocabulary of `Support/LinGaussFactor.lean` the correlation of the
Gaussian threshold field at two sites is
`greenGram d v xs i j / (v * greenSqSum d) = (∑_z G(x,z)G(y,z)) / greenSqSum d`,
so the statement proved here is

  `∃ ρ < 1, ∀ x ≠ y, ∑_z G(x,z)G(y,z) ≤ ρ * greenSqSum d`.

The strictness is proved without the equality case of the Cauchy-Schwarz
inequality.  Pointwise `ab ≤ (a²+b²)/2`, and the two square sums are equal by
translation invariance, so the product sum is at most `greenSqSum d` with
equality only if the two Green rows agree everywhere.  They cannot: if
`G(0,·) = G(u,·) = G(0,· - u)` with `u ≠ 0`, then `G(0,·)` is periodic with
period `u`, hence equal to `G(0,0) ≥ 1` along the infinite progression `-k u`,
contradicting `∑_z G(0,z)^2 < ∞`.

The passage from the strict inequality at each `u ≠ 0` to a uniform gap is the
paper's own: the covariance decay of `eq:dgt4-intersection-first-moment` makes
the ratio at most `1/2` outside a box, the box holds finitely many sites, and a
maximum over a finite set of numbers each below one is below one.
-/
import Sandpile.Support.LinGaussFactor
import Sandpile.Support.LinPairSum
import Sandpile.Support.LinLastVisit

open Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The Green product sum depends only on the difference of the two sites. -/
theorem tsum_green_mul_shift (x y : Site d) :
    (∑' z : Site d, green d x z * green d y z)
      = ∑' z : Site d, green d 0 z * green d (y - x) z := by
  have hF : ∀ z : Site d, green d x z * green d y z
      = (fun w : Site d => green d 0 w * green d (y - x) w) (Equiv.subRight x z) := by
    intro z
    have harg : z - x - (y - x) = z - y := by abel
    simp only [Equiv.subRight_apply]
    rw [green_shift x z, green_shift y z, green_shift (y - x) (z - x), harg]
  rw [tsum_congr hF]
  exact (Equiv.subRight x).tsum_eq (fun w : Site d => green d 0 w * green d (y - x) w)

/-- **The Green rows at two distinct sites are distinct.**  Were they equal, the
Green function would be periodic, hence constant along an infinite progression,
contradicting its square summability in dimensions five and up. -/
theorem exists_green_ne (hd : 5 ≤ d) (u : Site d) (hu : u ≠ 0) :
    ∃ z : Site d, green d 0 z ≠ green d u z := by
  classical
  by_contra hcon
  push Not at hcon
  have hstep : ∀ z : Site d, green d 0 z = green d 0 (z - u) := by
    intro z
    rw [hcon z, green_shift u z]
  have hiter : ∀ k : ℕ, green d 0 (-((k : ℤ) • u)) = green d 0 0 := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
        have h1 : -(((n : ℤ) + 1) • u) = -((n : ℤ) • u) - u := by
          rw [add_smul, one_smul]; abel
        have h2 : ((n + 1 : ℕ) : ℤ) = ((n : ℤ) + 1) := by push_cast; ring
        rw [h2, h1, ← hstep]
        exact ih
  obtain ⟨j, hj⟩ : ∃ j : Fin d, u j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hu (funext hall)
  have hinj : Function.Injective (fun k : ℕ => -((k : ℤ) • u)) := by
    intro a b hab
    have hj2 := congrFun hab j
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_inj] at hj2
    have hcancel : (a : ℤ) = (b : ℤ) := mul_right_cancel₀ hj hj2
    exact_mod_cast hcancel
  have hsum : Summable (fun k : ℕ => green d 0 (-((k : ℤ) • u)) ^ 2) := by
    exact (summable_green_sq hd 0).comp_injective hinj
  have hconst : (fun k : ℕ => green d 0 (-((k : ℤ) • u)) ^ 2)
      = (fun _ : ℕ => green d 0 0 ^ 2) := by
    funext k
    rw [hiter k]
  rw [hconst] at hsum
  have hzero : green d 0 0 ^ 2 = 0 := tendsto_const_nhds_iff.mp hsum.tendsto_atTop_zero
  have h1 : (1 : ℝ) ≤ green d 0 0 := one_le_green (by omega)
  nlinarith [hzero, h1]

/-- The square sum of the Green function is the same at every site. -/
theorem tsum_green_sq_shift (u : Site d) :
    (∑' z : Site d, green d u z ^ 2) = greenSqSum d := by
  show (∑' z : Site d, green d u z ^ 2) = ∑' z : Site d, green d 0 z ^ 2
  have hF : ∀ z : Site d, green d u z ^ 2
      = (fun w : Site d => green d 0 w ^ 2) (Equiv.subRight u z) := by
    intro z
    simp only [Equiv.subRight_apply]
    rw [green_shift u z]
  rw [tsum_congr hF]
  exact (Equiv.subRight u).tsum_eq (fun w : Site d => green d 0 w ^ 2)

/-- **Strict Cauchy-Schwarz for the Green rows.**  At two distinct sites the Green
product sum is strictly below the common square sum. -/
theorem tsum_green_mul_origin_lt (hd : 5 ≤ d) (u : Site d)
    (hne : ∃ z : Site d, green d 0 z ≠ green d u z)
    (hshift : (∑' z : Site d, green d u z ^ 2) = greenSqSum d) :
    (∑' z : Site d, green d 0 z * green d u z) < greenSqSum d := by
  obtain ⟨z0, hz0⟩ := hne
  have hs0 : Summable (fun z : Site d => green d 0 z ^ 2) := summable_green_sq hd 0
  have hsu : Summable (fun z : Site d => green d u z ^ 2) := summable_green_sq hd u
  have hsmul : Summable (fun z : Site d => green d 0 z * green d u z) := by
    obtain ⟨-, -, -, ⟨C, hC, hxy⟩, -⟩ := Sandpile.External.greenBoundsHigh d hd
    exact (hxy 0 u).1
  have havg : Summable (fun z : Site d => (green d 0 z ^ 2 + green d u z ^ 2) / 2) := by
    simpa [add_div] using (hs0.div_const 2).add (hsu.div_const 2)
  have hle : ∀ z : Site d, green d 0 z * green d u z
      ≤ (green d 0 z ^ 2 + green d u z ^ 2) / 2 := by
    intro z
    nlinarith [sq_nonneg (green d 0 z - green d u z)]
  have hlt : green d 0 z0 * green d u z0
      < (green d 0 z0 ^ 2 + green d u z0 ^ 2) / 2 := by
    have h1 : green d 0 z0 - green d u z0 ≠ 0 := sub_ne_zero.mpr hz0
    nlinarith [pow_two_pos_of_ne_zero h1]
  have hmain : (∑' z : Site d, green d 0 z * green d u z)
      < ∑' z : Site d, (green d 0 z ^ 2 + green d u z ^ 2) / 2 :=
    Summable.tsum_lt_tsum (i := z0) (Pi.le_def.mpr hle) hlt hsmul havg
  have hval : (∑' z : Site d, (green d 0 z ^ 2 + green d u z ^ 2) / 2) = greenSqSum d := by
    rw [tsum_div_const, hs0.tsum_add hsu, hshift]
    show (greenSqSum d + greenSqSum d) / 2 = greenSqSum d
    ring
  rw [hval] at hmain
  exact hmain

/-- **The covariance decay of `eq:dgt4-intersection-first-moment`, in the form the gap
uses.**  The Green product sum is uniformly small at large separation. -/
theorem exists_far_green_mul_le (hd : 5 ≤ d) (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℝ, ∀ x y : Site d, M ≤ External.latticeNorm (x - y) →
      (∑' z : Site d, green d x z * green d y z) ≤ eps := by
  obtain ⟨-, -, -, ⟨C, hC, hxy⟩, -⟩ := Sandpile.External.greenBoundsHigh d hd
  have hdR : (5:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hp : (0:ℝ) < (d:ℝ) - 4 := by linarith
  have h1 : Filter.Tendsto (fun t : ℝ => 1 + t) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left Filter.atTop 1 Filter.tendsto_id
  have h2 : Filter.Tendsto (fun s : ℝ => s ^ (4 - (d:ℝ))) Filter.atTop (nhds 0) := by
    have h3 := tendsto_rpow_neg_atTop hp
    have h4 : (fun x : ℝ => x ^ (-((d:ℝ) - 4))) = fun x : ℝ => x ^ (4 - (d:ℝ)) := by
      funext x
      rw [neg_sub]
    rwa [h4] at h3
  have htend : Filter.Tendsto (fun t : ℝ => C * (1 + t) ^ (4 - (d:ℝ))) Filter.atTop (nhds 0) := by
    have h5 := (h2.comp h1).const_mul C
    simpa using h5
  have hev : ∀ᶠ t : ℝ in Filter.atTop, C * (1 + t) ^ (4 - (d:ℝ)) < eps :=
    htend.eventually (eventually_lt_nhds heps)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
  refine ⟨M, ?_⟩
  intro x y hxyM
  exact le_trans (hxy x y).2 (le_of_lt (hM _ hxyM))

open Classical in
/-- A site of Euclidean norm at most `M` lies in the integer box of radius `⌊M⌋`. -/
theorem mem_box_of_latticeNorm_le (M : ℝ) (u : Site d)
    (hu : External.latticeNorm u ≤ M) :
    u ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-⌊M⌋) ⌊M⌋) := by
  rw [Fintype.mem_piFinset]
  intro i
  have hterm : (((u i : ℤ) : ℝ)) ^ 2 ≤ ∑ j : Fin d, (((u j : ℤ) : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin d => (((u j : ℤ) : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have habs : |(((u i : ℤ) : ℝ))| ≤ M := by
    rw [← Real.sqrt_sq_eq_abs]
    refine le_trans (Real.sqrt_le_sqrt hterm) ?_
    exact hu
  rw [abs_le] at habs
  rw [Finset.mem_Icc]
  have hup : u i ≤ ⌊M⌋ := Int.le_floor.mpr (by exact habs.2)
  have hlo : -(u i) ≤ ⌊M⌋ := Int.le_floor.mpr (by push_cast; linarith [habs.1])
  omega

/-- A function below `1/2` off a finite set and below `1` on it has a uniform bound
strictly below `1`. -/
theorem exists_gap_of_finset {iota : Type*} (G : iota → ℝ) (T : Finset iota)
    (hcover : ∀ u : iota, G u ≤ 1 / 2 ∨ u ∈ T) (hlt : ∀ u ∈ T, G u < 1) :
    ∃ rho : ℝ, rho < 1 ∧ ∀ u : iota, G u ≤ rho := by
  refine ⟨Finset.fold max (1/2) G T, ?_, ?_⟩
  · rw [Finset.fold_max_lt]
    exact ⟨by norm_num, hlt⟩
  · intro u
    rcases hcover u with h | h
    · exact (Finset.le_fold_max (G u)).mpr (Or.inl h)
    · exact (Finset.le_fold_max (G u)).mpr (Or.inr ⟨u, h, le_rfl⟩)

/-- **The correlation gap `eq:dgt4-gaussian-correlation-gap`.** -/
theorem exists_correlation_gap (hd : 5 ≤ d) :
    ∃ rho : ℝ, 0 ≤ rho ∧ rho < 1 ∧ ∀ x y : Site d, x ≠ y →
      (∑' z : Site d, green d x z * green d y z) ≤ rho * greenSqSum d := by
  classical
  have hgs1 : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  have hgs : (0 : ℝ) < greenSqSum d := lt_of_lt_of_le zero_lt_one hgs1
  have hlt : ∀ u : Site d, u ≠ 0 →
      (∑' z : Site d, green d 0 z * green d u z) / greenSqSum d < 1 := by
    intro u hu
    exact (div_lt_one hgs).mpr
      (tsum_green_mul_origin_lt hd u (exists_green_ne hd u hu) (tsum_green_sq_shift u))
  obtain ⟨M, hM⟩ := exists_far_green_mul_le hd (greenSqSum d / 2) (by positivity)
  have hcover : ∀ u : Site d,
      (if u = 0 then (0:ℝ) else (∑' z : Site d, green d 0 z * green d u z) / greenSqSum d) ≤ 1 / 2
        ∨ u ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-⌊M⌋) ⌊M⌋) := by
    intro u
    by_cases hu : u = 0
    · left
      simp [hu]
    by_cases hnear : Sandpile.External.latticeNorm u ≤ M
    · right
      exact mem_box_of_latticeNorm_le M u hnear
    · left
      have hfar : M ≤ Sandpile.External.latticeNorm (u - 0) := by
        rw [sub_zero]
        exact le_of_lt (not_le.mp hnear)
      have h1 := hM u 0 hfar
      have h2 : (∑' z : Site d, green d 0 z * green d u z)
          = ∑' z : Site d, green d u z * green d 0 z := tsum_congr fun z => mul_comm _ _
      have h3 : (∑' z : Site d, green d 0 z * green d u z) ≤ greenSqSum d / 2 := by
        rw [h2]
        exact h1
      simp only [hu, if_false]
      rw [div_le_iff₀ hgs]
      linarith
  have hltT : ∀ u ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-⌊M⌋) ⌊M⌋),
      (if u = 0 then (0:ℝ) else (∑' z : Site d, green d 0 z * green d u z) / greenSqSum d) < 1 := by
    intro u _
    by_cases hu : u = 0
    · simp [hu]
    · simp only [hu, if_false]
      exact hlt u hu
  obtain ⟨rho, hrho1, hrhoG⟩ :=
    exists_gap_of_finset
      (fun u : Site d =>
        if u = 0 then (0:ℝ) else (∑' z : Site d, green d 0 z * green d u z) / greenSqSum d)
      (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-⌊M⌋) ⌊M⌋)) hcover hltT
  have hrho0 : 0 ≤ rho := by
    have h0 := hrhoG 0
    simpa using h0
  refine ⟨rho, hrho0, hrho1, ?_⟩
  intro x y hxy
  have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hval := hrhoG (y - x)
  simp only [hne, if_false] at hval
  rw [div_le_iff₀ hgs] at hval
  rw [tsum_green_mul_shift x y]
  exact hval


end Sandpile
