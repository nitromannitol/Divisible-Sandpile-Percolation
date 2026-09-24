/-
The space sum of the log-Laplace transform in the proof of
`lem:dgt4-stretched-green-scenery-tail` (`sandpile.tex:4361-4410`).

Writing `ψ(μ)` for `log E e^{-μζ(0)}` and `ℓ_y` for `g_m(0,y)`, the proof needs

  `∑_y ψ(λ ℓ_y) ≤ C λ^{β/(β-1)}`  for every `λ ≥ 1`,

where `β = min(γ, d/2)`.  The regime bounds `ψ(μ) ≤ C μ²` for `μ ≤ 1` and
`ψ(μ) ≤ C μ^q` for `μ ≥ 1`, with `q = γ/(γ-1)`, are `LatticeProb.Prob.LaplaceTransform`.  This
file carries out the summation, in the two regions the exponent `q` separates:

- `q > d/(d-2)`, the case `γ < d/2` of the paper.  No split of space is needed:
  `ψ(λ ℓ) ≤ C λ^q (ℓ² + ℓ^q)` at every site, and both `∑_y G(0,y)²` and
  `∑_y G(0,y)^q` converge.  The exponent of `λ` is `q`.
- `q < d/(d-2)`, the case `γ > d/2`.  Space is split at the radius
  `ρ = (λ A)^{1/(d-2)}` of the paper.  Inside, `q ≤ 2` makes the
  large-parameter bound valid at every site and the weighted volume of the ball
  gives `λ^q ρ^{d-(d-2)q}`; outside, `λ ℓ ≤ 1` by the choice of `ρ` and the
  square tail `∑_{|y| ≥ r} G(0,y)² ≤ C r^{4-d}` gives `λ² ρ^{4-d}`.  Both are of
  order `λ^{d/(d-2)}`.

In both cases the exponent is `max(q, d/(d-2))`, which is `β/(β-1)`.
-/
import Sandpile.Support.GreenHigh
import Sandpile.Support.SceneryTail

open LatticeProb

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### Elementary comparisons of real powers -/

/-- Two real powers of a base in `[0,1]`: the larger exponent gives the smaller
value.  Both exponents are positive, so the base zero is covered. -/
theorem rpow_le_rpow_of_le_one_base (u p q : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hq : 0 < q) (hpq : q ≤ p) : u ^ p ≤ u ^ q := by
  rcases hu.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
  · exact Real.rpow_le_rpow_of_exponent_ge h hu1 hpq

/-- The large-argument branch of the log-Laplace bound. -/
theorem psi_large_arg (lam ell q : ℝ) (hlam : 0 ≤ lam) (hell : 0 ≤ ell) :
    (lam * ell) ^ q ≤ lam ^ q * (ell ^ (2 : ℝ) + ell ^ q) := by
  rw [Real.mul_rpow hlam hell]
  have h1 : (0 : ℝ) ≤ ell ^ (2 : ℝ) := Real.rpow_nonneg hell _
  have h2 : (0 : ℝ) ≤ lam ^ q := Real.rpow_nonneg hlam _
  have h3 : (0 : ℝ) ≤ ell ^ q := Real.rpow_nonneg hell _
  exact mul_le_mul_of_nonneg_left (by linarith) h2

/-- The small-argument branch. -/
theorem psi_small_arg (lam ell q : ℝ) (hq1 : 1 < q) (hlam : 1 ≤ lam) (hell : 0 ≤ ell)
    (h : lam * ell ≤ 1) :
    (lam * ell) ^ (2 : ℝ) ≤ lam ^ q * (ell ^ (2 : ℝ) + ell ^ q) := by
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  rcases le_or_gt q 2 with hq | hq
  · exact le_trans (rpow_le_rpow_of_le_one_base (lam * ell) 2 q (by positivity) h
      (by linarith) hq) (psi_large_arg lam ell q hlam0 hell)
  · rw [Real.mul_rpow hlam0 hell]
    have h1 : lam ^ (2 : ℝ) ≤ lam ^ q := Real.rpow_le_rpow_of_exponent_le hlam (by linarith)
    have h2 : (0 : ℝ) ≤ ell ^ (2 : ℝ) := Real.rpow_nonneg hell _
    have h3 : (0 : ℝ) ≤ ell ^ q := Real.rpow_nonneg hell _
    have h4 : (0 : ℝ) ≤ lam ^ q := Real.rpow_nonneg hlam0 _
    calc lam ^ (2 : ℝ) * ell ^ (2 : ℝ) ≤ lam ^ q * ell ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ lam ^ q * (ell ^ (2 : ℝ) + ell ^ q) :=
          mul_le_mul_of_nonneg_left (by linarith) h4

/-- A product of nonnegative reals each below an exponential is below the
exponential of a bound on the sum of the exponents. -/
theorem prod_le_exp_of_sum_le {α : Type*} (s : Finset α) (f g : α → ℝ)
    (hf0 : ∀ a ∈ s, 0 ≤ f a) (hf : ∀ a ∈ s, f a ≤ Real.exp (g a))
    (M : ℝ) (hM : ∑ a ∈ s, g a ≤ M) :
    ∏ a ∈ s, f a ≤ Real.exp M := by
  calc ∏ a ∈ s, f a ≤ ∏ a ∈ s, Real.exp (g a) := Finset.prod_le_prod hf0 hf
    _ = Real.exp (∑ a ∈ s, g a) := (Real.exp_sum s g).symm
    _ ≤ Real.exp M := Real.exp_le_exp.mpr hM

/-! ### Sums over a finset compared with a sum over a subtype -/

/-- A finite sum of a nonnegative family over sites satisfying a predicate is at
most the sum over the subtype cut out by that predicate. -/
theorem finset_sum_le_tsum_subtype {P : Site d → Prop}
    (f : Site d → ℝ) (hf : ∀ y, 0 ≤ f y)
    (hsum : Summable fun z : {z : Site d // P z} => f (z : Site d))
    (s : Finset (Site d)) (hs : ∀ y ∈ s, P y) :
    ∑ y ∈ s, f y ≤ ∑' z : {z : Site d // P z}, f (z : Site d) := by
  classical
  set e : {x : Site d // x ∈ s} → {z : Site d // P z} :=
    fun y => ⟨y.1, hs y.1 y.2⟩ with he
  have hinj : ∀ x ∈ s.attach, ∀ y ∈ s.attach, e x = e y → x = y := by
    intro a _ b _ hab
    have hv : (a : Site d) = (b : Site d) :=
      congrArg (fun z : {z : Site d // P z} => (z : Site d)) hab
    exact Subtype.ext hv
  have hsum_eq : ∑ z ∈ s.attach.image e, f (z : Site d) = ∑ y ∈ s, f y := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_attach s f
  calc ∑ y ∈ s, f y = ∑ z ∈ s.attach.image e, f (z : Site d) := hsum_eq.symm
    _ ≤ ∑' z : {z : Site d // P z}, f (z : Site d) :=
        hsum.sum_le_tsum _ (fun z _ => hf _)

/-! ### The space sum above the critical exponent -/

/-- The real square is the natural square. -/
theorem rpow_two_eq_sq (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **No split of space.**  When `q` lies above `d/(d-2)`, both `∑_y G(0,y)²`
and `∑_y G(0,y)^q` converge, and the two regime bounds of `LatticeProb.Prob.LaplaceTransform`
combine into `ψ(λ g_m(0,y)) ≤ C λ^q (G(0,y)² + G(0,y)^q)` at every site.  This
is the case `γ < d/2` of `sandpile.tex:4377-4386`. -/
theorem exists_space_sum_high (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (q : ℝ) (hq1 : 1 < q) (hq : (d : ℝ) / ((d : ℝ) - 2) < q) (Cψ : ℝ) (hCψ : 0 ≤ Cψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (lam : ℝ), 1 ≤ lam → ∀ w : Site d → ℝ,
      (∀ y, lam * greenTime d m 0 y ≤ 1 →
        w y ≤ Cψ * (lam * greenTime d m 0 y) ^ (2 : ℝ)) →
      (∀ y, 1 ≤ lam * greenTime d m 0 y →
        w y ≤ Cψ * (lam * greenTime d m 0 y) ^ q) →
      ∑ y ∈ boxFinset (0 : Site d) m, w y ≤ C * lam ^ q := by
  have hG : ∀ y : Site d, 0 ≤ green d 0 y := fun y =>
    tsum_nonneg fun k => heatKernel_nonneg _ _ _
  obtain ⟨-, hl2, -, -, -⟩ := hGH d hd
  have hs2 : Summable fun y : Site d => green d 0 y ^ (2 : ℝ) :=
    hl2.congr fun y => (rpow_two_eq_sq _).symm
  have hsq : Summable fun y : Site d => green d 0 y ^ q := summable_green_rpow hGH hd q hq
  set S2 : ℝ := ∑' y : Site d, green d 0 y ^ (2 : ℝ) with hS2def
  set Sq : ℝ := ∑' y : Site d, green d 0 y ^ q with hSqdef
  have hS2 : 0 ≤ S2 := tsum_nonneg fun y => Real.rpow_nonneg (hG y) _
  have hSq : 0 ≤ Sq := tsum_nonneg fun y => Real.rpow_nonneg (hG y) _
  refine ⟨Cψ * (S2 + Sq) + 1, by positivity, fun m lam hlam w hsmall hlarge => ?_⟩
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  have hlamq : (0 : ℝ) ≤ lam ^ q := Real.rpow_nonneg hlam0 _
  have hstep : ∀ y : Site d,
      w y ≤ Cψ * lam ^ q * (green d 0 y ^ (2 : ℝ) + green d 0 y ^ q) := by
    intro y
    have hl0 : 0 ≤ greenTime d m 0 y := greenTime_nonneg _ _ _
    have hlG : greenTime d m 0 y ≤ green d 0 y := greenTime_le_green hGH hd m y
    have hmono : greenTime d m 0 y ^ (2 : ℝ) + greenTime d m 0 y ^ q
        ≤ green d 0 y ^ (2 : ℝ) + green d 0 y ^ q :=
      add_le_add (Real.rpow_le_rpow hl0 hlG (by norm_num))
        (Real.rpow_le_rpow hl0 hlG (by linarith))
    have hkey : (if lam * greenTime d m 0 y ≤ 1 then
          (lam * greenTime d m 0 y) ^ (2 : ℝ) else (lam * greenTime d m 0 y) ^ q)
        ≤ lam ^ q * (greenTime d m 0 y ^ (2 : ℝ) + greenTime d m 0 y ^ q) := by
      split_ifs with hc
      · exact psi_small_arg lam _ q hq1 hlam hl0 hc
      · exact psi_large_arg lam _ q hlam0 hl0
    have hw : w y ≤ Cψ * (if lam * greenTime d m 0 y ≤ 1 then
        (lam * greenTime d m 0 y) ^ (2 : ℝ) else (lam * greenTime d m 0 y) ^ q) := by
      split_ifs with hc
      · exact hsmall y hc
      · exact hlarge y (not_le.mp hc |>.le)
    calc w y ≤ Cψ * (if lam * greenTime d m 0 y ≤ 1 then
            (lam * greenTime d m 0 y) ^ (2 : ℝ) else (lam * greenTime d m 0 y) ^ q) := hw
      _ ≤ Cψ * (lam ^ q * (greenTime d m 0 y ^ (2 : ℝ) + greenTime d m 0 y ^ q)) :=
          mul_le_mul_of_nonneg_left hkey hCψ
      _ ≤ Cψ * (lam ^ q * (green d 0 y ^ (2 : ℝ) + green d 0 y ^ q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hlamq) hCψ
      _ = Cψ * lam ^ q * (green d 0 y ^ (2 : ℝ) + green d 0 y ^ q) := by ring
  have hbox : ∑ y ∈ boxFinset (0 : Site d) m,
      (green d 0 y ^ (2 : ℝ) + green d 0 y ^ q) ≤ S2 + Sq := by
    rw [Finset.sum_add_distrib]
    exact add_le_add (hs2.sum_le_tsum _ fun y _ => Real.rpow_nonneg (hG y) _)
      (hsq.sum_le_tsum _ fun y _ => Real.rpow_nonneg (hG y) _)
  calc ∑ y ∈ boxFinset (0 : Site d) m, w y
      ≤ ∑ y ∈ boxFinset (0 : Site d) m,
          Cψ * lam ^ q * (green d 0 y ^ (2 : ℝ) + green d 0 y ^ q) :=
        Finset.sum_le_sum fun y _ => hstep y
    _ = Cψ * lam ^ q * ∑ y ∈ boxFinset (0 : Site d) m,
          (green d 0 y ^ (2 : ℝ) + green d 0 y ^ q) := by rw [Finset.mul_sum]
    _ ≤ Cψ * lam ^ q * (S2 + Sq) :=
        mul_le_mul_of_nonneg_left hbox (by positivity)
    _ ≤ (Cψ * (S2 + Sq) + 1) * lam ^ q := by nlinarith

/-! ### The space sum below the critical exponent -/

/-- **Splitting space.**  When `q` lies below `d/(d-2)` — the case `γ > d/2` of
`sandpile.tex:4387-4397` — space is split at the radius `ρ = (λ A)^{1/(d-2)}`.
Inside, `q < 2` makes the large-parameter bound valid at every site and the
weighted volume of the ball gives `λ^q ρ^{d-(d-2)q}`; outside, `λ g_m(0,y) ≤ 1`
by the choice of `ρ`, and the square tail gives `λ² ρ^{4-d}`.  Both are of order
`λ^{d/(d-2)}`. -/
theorem exists_space_sum_low (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (q : ℝ) (hq1 : 1 < q) (hq : q < (d : ℝ) / ((d : ℝ) - 2)) (Cψ : ℝ) (hCψ : 0 ≤ Cψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (lam : ℝ), 1 ≤ lam → ∀ w : Site d → ℝ,
      (∀ y, lam * greenTime d m 0 y ≤ 1 →
        w y ≤ Cψ * (lam * greenTime d m 0 y) ^ (2 : ℝ)) →
      (∀ y, 1 ≤ lam * greenTime d m 0 y →
        w y ≤ Cψ * (lam * greenTime d m 0 y) ^ q) →
      ∑ y ∈ boxFinset (0 : Site d) m, w y ≤ C * lam ^ ((d : ℝ) / ((d : ℝ) - 2)) := by
  classical
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  set p : ℝ := (d : ℝ) / ((d : ℝ) - 2) with hpdef
  have hp1 : 1 < p := by rw [hpdef, lt_div_iff₀ hd2]; linarith
  have hp2 : p ≤ 2 := by rw [hpdef, div_le_iff₀ hd2]; linarith
  have hq2 : q < 2 := lt_of_lt_of_le hq hp2
  have hq0 : (0 : ℝ) < q := by linarith
  have hG : ∀ y : Site d, 0 ≤ green d 0 y := fun y =>
    tsum_nonneg fun k => heatKernel_nonneg _ _ _
  obtain ⟨CG, hCG0, hGbd⟩ := exists_green_pointwise hGH hd
  obtain ⟨⟨C1, hC1, htail⟩, -, -, -, -⟩ := hGH d hd
  set A : ℝ := max CG 1 with hAdef
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hA0 : (0 : ℝ) < A := by linarith
  have hCGA : CG ≤ A := le_max_left _ _
  set a : ℝ := ((d : ℝ) - 2) * q with hadef
  have ha0 : (0 : ℝ) ≤ a := by rw [hadef]; positivity
  have had : a < (d : ℝ) := by
    rw [hadef]
    rw [lt_div_iff₀ hd2] at hq
    linarith
  obtain ⟨Cbox, hCbox0, hbox⟩ := exists_sum_box_rpow_bound d (by omega) a ha0 had
  have hCGq : (0 : ℝ) < CG ^ q := Real.rpow_pos_of_pos hCG0 _
  have hAp : (0 : ℝ) < A ^ p := Real.rpow_pos_of_pos hA0 _
  refine ⟨Cψ * CG ^ q * Cbox * (3 : ℝ) ^ (d : ℕ) * A ^ p + Cψ * C1 + 1, by positivity,
    fun m lam hlam w hsmall hlarge => ?_⟩
  have hlam0 : (0 : ℝ) < lam := by linarith
  set ρ : ℝ := (lam * A) ^ (1 / ((d : ℝ) - 2)) with hρdef
  have hlamA : (1 : ℝ) ≤ lam * A := by nlinarith
  have hlamA0 : (0 : ℝ) < lam * A := by linarith
  have hρ1 : (1 : ℝ) ≤ ρ := Real.one_le_rpow hlamA (by positivity)
  have hρ0 : (0 : ℝ) < ρ := by linarith
  set R : ℕ := ⌈ρ⌉₊ with hRdef
  have hRρ : ρ ≤ (R : ℝ) := Nat.le_ceil ρ
  have hR1 : 1 ≤ R := by
    by_contra hcon
    have : R = 0 := by omega
    rw [this] at hRρ
    simp at hRρ
    linarith
  have hR1R : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hRle : (R : ℝ) ≤ ρ + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  -- the three power identities at the splitting radius
  have hρpow : ρ ^ (2 - (d : ℝ)) = (lam * A)⁻¹ := by
    rw [hρdef, ← Real.rpow_mul hlamA0.le,
      show 1 / ((d : ℝ) - 2) * (2 - (d : ℝ)) = -1 by field_simp; ring, Real.rpow_neg_one]
  have hρin : ρ ^ ((d : ℝ) - a) = lam ^ (p - q) * A ^ (p - q) := by
    rw [hρdef, ← Real.rpow_mul hlamA0.le,
      show 1 / ((d : ℝ) - 2) * ((d : ℝ) - a) = p - q by
        rw [hadef, hpdef]; field_simp,
      Real.mul_rpow hlam0.le hA0.le]
  have hρout : ρ ^ (4 - (d : ℝ)) = lam ^ (p - 2) * A ^ (p - 2) := by
    rw [hρdef, ← Real.rpow_mul hlamA0.le,
      show 1 / ((d : ℝ) - 2) * (4 - (d : ℝ)) = p - 2 by
        rw [hpdef]; field_simp; ring,
      Real.mul_rpow hlam0.le hA0.le]
  -- the split of the box at the radius `R`
  have hsplit : ∑ y ∈ (boxFinset (0 : Site d) m).filter
        (fun y => Sandpile.External.latticeNorm y < (R : ℝ)), w y +
      ∑ y ∈ (boxFinset (0 : Site d) m).filter
        (fun y => ¬ Sandpile.External.latticeNorm y < (R : ℝ)), w y =
      ∑ y ∈ boxFinset (0 : Site d) m, w y :=
    Finset.sum_filter_add_sum_filter_not _ _ w
  have hlamp : (0 : ℝ) ≤ lam ^ p := (Real.rpow_pos_of_pos hlam0 _).le
  -- inside the splitting radius
  have hinner : ∑ y ∈ (boxFinset (0 : Site d) m).filter
      (fun y => Sandpile.External.latticeNorm y < (R : ℝ)), w y ≤
      Cψ * CG ^ q * Cbox * (3 : ℝ) ^ (d : ℕ) * A ^ p * lam ^ p := by
    have hterm : ∀ y ∈ (boxFinset (0 : Site d) m).filter
        (fun y => Sandpile.External.latticeNorm y < (R : ℝ)),
        w y ≤ Cψ * lam ^ q * CG ^ q * (1 + (LatticeProb.supNorm y : ℝ)) ^ (-a) := by
      intro y _
      have hl0 : 0 ≤ greenTime d m 0 y := greenTime_nonneg _ _ _
      have hlG : greenTime d m 0 y ≤ green d 0 y := greenTime_le_green hGH hd m y
      have hwq : w y ≤ Cψ * (lam * greenTime d m 0 y) ^ q := by
        rcases le_or_gt (lam * greenTime d m 0 y) 1 with hc | hc
        · refine le_trans (hsmall y hc) (mul_le_mul_of_nonneg_left ?_ hCψ)
          exact rpow_le_rpow_of_le_one_base _ 2 q (by positivity) hc hq0 hq2.le
        · exact hlarge y hc.le
      have hnorm : Sandpile.External.latticeNorm y = LatticeProb.euclidNorm y := rfl
      have hbase : (0 : ℝ) < 1 + LatticeProb.euclidNorm y := by
        have := LatticeProb.euclidNorm_nonneg y; linarith
      have hstep1 : (lam * greenTime d m 0 y) ^ q
          ≤ lam ^ q * (CG * (1 + LatticeProb.euclidNorm y) ^ (2 - (d : ℝ))) ^ q := by
        rw [Real.mul_rpow hlam0.le hl0]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hlam0.le _)
        refine Real.rpow_le_rpow hl0 (le_trans hlG ?_) hq0.le
        have := hGbd y; rwa [hnorm] at this
      have hstep2 : (CG * (1 + LatticeProb.euclidNorm y) ^ (2 - (d : ℝ))) ^ q
          = CG ^ q * (1 + LatticeProb.euclidNorm y) ^ (-a) := by
        rw [Real.mul_rpow hCG0.le (Real.rpow_nonneg hbase.le _), ← Real.rpow_mul hbase.le,
          show (2 - (d : ℝ)) * q = -a by rw [hadef]; ring]
      have hstep3 : (1 + LatticeProb.euclidNorm y) ^ (-a)
          ≤ (1 + (LatticeProb.supNorm y : ℝ)) ^ (-a) := by
        refine Real.rpow_le_rpow_of_nonpos ?_ ?_ (by linarith)
        · have := Nat.cast_nonneg (α := ℝ) (LatticeProb.supNorm y); linarith
        · have := LatticeProb.supNorm_le_euclidNorm y; linarith
      calc w y ≤ Cψ * (lam * greenTime d m 0 y) ^ q := hwq
        _ ≤ Cψ * (lam ^ q * (CG * (1 + LatticeProb.euclidNorm y) ^ (2 - (d : ℝ))) ^ q) :=
            mul_le_mul_of_nonneg_left hstep1 hCψ
        _ = Cψ * lam ^ q * (CG ^ q * (1 + LatticeProb.euclidNorm y) ^ (-a)) := by
            rw [hstep2]; ring
        _ ≤ Cψ * lam ^ q * (CG ^ q * (1 + (LatticeProb.supNorm y : ℝ)) ^ (-a)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 hCGq.le) ?_
            positivity
        _ = Cψ * lam ^ q * CG ^ q * (1 + (LatticeProb.supNorm y : ℝ)) ^ (-a) := by ring
    have hsub : (boxFinset (0 : Site d) m).filter
        (fun y => Sandpile.External.latticeNorm y < (R : ℝ)) ⊆
        LatticeProb.boxFinset (0 : Site d) R := by
      intro y hy
      have hlt : Sandpile.External.latticeNorm y < (R : ℝ) := (Finset.mem_filter.mp hy).2
      have hsn : (LatticeProb.supNorm y : ℝ) ≤ LatticeProb.euclidNorm y :=
        LatticeProb.supNorm_le_euclidNorm y
      have hnorm : Sandpile.External.latticeNorm y = LatticeProb.euclidNorm y := rfl
      rw [hnorm] at hlt
      have hnat : LatticeProb.supNorm y ≤ R := by
        have : (LatticeProb.supNorm y : ℝ) ≤ (R : ℝ) := le_trans hsn hlt.le
        exact_mod_cast this
      exact LatticeProb.mem_boxFinset_zero_iff.mpr hnat
    have hvol : ∑ y ∈ LatticeProb.boxFinset (0 : Site d) R,
        (1 + (LatticeProb.supNorm y : ℝ)) ^ (-a) ≤ Cbox * (1 + (R : ℝ)) ^ ((d : ℝ) - a) :=
      hbox R
    have hR3 : (1 : ℝ) + (R : ℝ) ≤ 3 * ρ := by linarith
    have hpow : (1 + (R : ℝ)) ^ ((d : ℝ) - a) ≤ (3 : ℝ) ^ (d : ℕ) * (lam ^ (p - q) * A ^ (p - q)) := by
      have h1 : (1 + (R : ℝ)) ^ ((d : ℝ) - a) ≤ (3 * ρ) ^ ((d : ℝ) - a) :=
        Real.rpow_le_rpow (by linarith) hR3 (by linarith)
      have h2 : (3 * ρ) ^ ((d : ℝ) - a) = (3 : ℝ) ^ ((d : ℝ) - a) * ρ ^ ((d : ℝ) - a) :=
        Real.mul_rpow (by norm_num) hρ0.le
      have h3 : (3 : ℝ) ^ ((d : ℝ) - a) ≤ (3 : ℝ) ^ ((d : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h4 : (3 : ℝ) ^ ((d : ℝ)) = (3 : ℝ) ^ (d : ℕ) := by
        rw [show ((d : ℝ)) = ((d : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [h2, hρin] at h1
      refine le_trans h1 ?_
      rw [← h4]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    have hApq : A ^ (p - q) ≤ A ^ p :=
      Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
    calc ∑ y ∈ (boxFinset (0 : Site d) m).filter
          (fun y => Sandpile.External.latticeNorm y < (R : ℝ)), w y
        ≤ ∑ y ∈ (boxFinset (0 : Site d) m).filter
            (fun y => Sandpile.External.latticeNorm y < (R : ℝ)),
            Cψ * lam ^ q * CG ^ q * (1 + (LatticeProb.supNorm y : ℝ)) ^ (-a) :=
          Finset.sum_le_sum hterm
      _ = Cψ * lam ^ q * CG ^ q * ∑ y ∈ (boxFinset (0 : Site d) m).filter
            (fun y => Sandpile.External.latticeNorm y < (R : ℝ)),
            (1 + (LatticeProb.supNorm y : ℝ)) ^ (-a) := by rw [Finset.mul_sum]
      _ ≤ Cψ * lam ^ q * CG ^ q * ∑ y ∈ LatticeProb.boxFinset (0 : Site d) R,
            (1 + (LatticeProb.supNorm y : ℝ)) ^ (-a) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
            fun y _ _ => by positivity) ?_
          have : (0 : ℝ) ≤ lam ^ q := Real.rpow_nonneg hlam0.le _
          positivity
      _ ≤ Cψ * lam ^ q * CG ^ q * (Cbox * (1 + (R : ℝ)) ^ ((d : ℝ) - a)) := by
          refine mul_le_mul_of_nonneg_left hvol ?_
          have : (0 : ℝ) ≤ lam ^ q := Real.rpow_nonneg hlam0.le _
          positivity
      _ ≤ Cψ * lam ^ q * CG ^ q *
            (Cbox * ((3 : ℝ) ^ (d : ℕ) * (lam ^ (p - q) * A ^ p))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCbox0.le) ?_
          · refine le_trans hpow ?_
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hApq ?_) (by positivity)
            exact Real.rpow_nonneg hlam0.le _
          · have : (0 : ℝ) ≤ lam ^ q := Real.rpow_nonneg hlam0.le _
            positivity
      _ = Cψ * CG ^ q * Cbox * (3 : ℝ) ^ (d : ℕ) * A ^ p * (lam ^ q * lam ^ (p - q)) := by ring
      _ = Cψ * CG ^ q * Cbox * (3 : ℝ) ^ (d : ℕ) * A ^ p * lam ^ p := by
          rw [← Real.rpow_add hlam0]
          ring_nf
  -- outside the splitting radius
  have houter : ∑ y ∈ (boxFinset (0 : Site d) m).filter
      (fun y => ¬ Sandpile.External.latticeNorm y < (R : ℝ)), w y ≤ Cψ * C1 * lam ^ p := by
    have hterm : ∀ y ∈ (boxFinset (0 : Site d) m).filter
        (fun y => ¬ Sandpile.External.latticeNorm y < (R : ℝ)),
        w y ≤ Cψ * lam ^ (2 : ℝ) * green d 0 y ^ 2 := by
      intro y hy
      have hy' : (R : ℝ) ≤ Sandpile.External.latticeNorm y := by
        have h := (Finset.mem_filter.mp hy).2
        simp only [not_lt] at h
        exact h
      have hl0 : 0 ≤ greenTime d m 0 y := greenTime_nonneg _ _ _
      have hlG : greenTime d m 0 y ≤ green d 0 y := greenTime_le_green hGH hd m y
      have hρle : ρ ≤ 1 + Sandpile.External.latticeNorm y := by linarith
      have h3 : (1 + Sandpile.External.latticeNorm y) ^ (2 - (d : ℝ)) ≤ ρ ^ (2 - (d : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hρ0 hρle (by linarith)
      have h4 : green d 0 y ≤ CG * ρ ^ (2 - (d : ℝ)) :=
        le_trans (hGbd y) (mul_le_mul_of_nonneg_left h3 hCG0.le)
      have hsmallarg : lam * greenTime d m 0 y ≤ 1 := by
        have hle : lam * greenTime d m 0 y ≤ lam * (CG * ρ ^ (2 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left (le_trans hlG h4) hlam0.le
        rw [hρpow] at hle
        have heq : lam * (CG * (lam * A)⁻¹) = CG / A := by field_simp
        rw [heq] at hle
        exact le_trans hle ((div_le_one hA0).mpr hCGA)
      have hsq : green d 0 y ^ (2 : ℝ) = green d 0 y ^ 2 := rpow_two_eq_sq _
      calc w y ≤ Cψ * (lam * greenTime d m 0 y) ^ (2 : ℝ) := hsmall y hsmallarg
        _ = Cψ * (lam ^ (2 : ℝ) * greenTime d m 0 y ^ (2 : ℝ)) := by
            rw [Real.mul_rpow hlam0.le hl0]
        _ ≤ Cψ * (lam ^ (2 : ℝ) * green d 0 y ^ (2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ?_) hCψ
            · exact Real.rpow_le_rpow hl0 hlG (by norm_num)
            · exact Real.rpow_nonneg hlam0.le _
        _ = Cψ * lam ^ (2 : ℝ) * green d 0 y ^ 2 := by rw [hsq]; ring
    obtain ⟨hsummable, htsum, -⟩ := htail R hR1
    have hsubsum : ∑ y ∈ (boxFinset (0 : Site d) m).filter
        (fun y => ¬ Sandpile.External.latticeNorm y < (R : ℝ)), green d 0 y ^ 2 ≤
        ∑' z : {z : Site d // (R : ℝ) ≤ Sandpile.External.latticeNorm z},
          green d 0 (z : Site d) ^ 2 := by
      refine finset_sum_le_tsum_subtype (fun y => green d 0 y ^ 2) (fun y => sq_nonneg _)
        hsummable _ fun y hy => ?_
      have h := (Finset.mem_filter.mp hy).2
      simp only [not_lt] at h
      exact h
    have hlam2 : (0 : ℝ) ≤ lam ^ (2 : ℝ) := Real.rpow_nonneg hlam0.le _
    have hfin : lam ^ (2 : ℝ) * ((R : ℝ) ^ (4 - (d : ℝ))) ≤ lam ^ p := by
      have h1 : (R : ℝ) ^ (4 - (d : ℝ)) ≤ ρ ^ (4 - (d : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hρ0 hRρ (by linarith)
      have h2 : A ^ (p - 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hA1 (by linarith)
      have h3 : lam ^ (2 : ℝ) * (lam ^ (p - 2) * A ^ (p - 2)) ≤ lam ^ p := by
        have h4 : lam ^ (2 : ℝ) * lam ^ (p - 2) = lam ^ p := by
          rw [← Real.rpow_add hlam0]; ring_nf
        calc lam ^ (2 : ℝ) * (lam ^ (p - 2) * A ^ (p - 2))
            = (lam ^ (2 : ℝ) * lam ^ (p - 2)) * A ^ (p - 2) := by ring
          _ ≤ (lam ^ (2 : ℝ) * lam ^ (p - 2)) * 1 := by
              refine mul_le_mul_of_nonneg_left h2 ?_
              positivity
          _ = lam ^ p := by rw [mul_one, h4]
      calc lam ^ (2 : ℝ) * ((R : ℝ) ^ (4 - (d : ℝ)))
          ≤ lam ^ (2 : ℝ) * ρ ^ (4 - (d : ℝ)) := mul_le_mul_of_nonneg_left h1 hlam2
        _ = lam ^ (2 : ℝ) * (lam ^ (p - 2) * A ^ (p - 2)) := by rw [hρout]
        _ ≤ lam ^ p := h3
    calc ∑ y ∈ (boxFinset (0 : Site d) m).filter
          (fun y => ¬ Sandpile.External.latticeNorm y < (R : ℝ)), w y
        ≤ ∑ y ∈ (boxFinset (0 : Site d) m).filter
            (fun y => ¬ Sandpile.External.latticeNorm y < (R : ℝ)),
            Cψ * lam ^ (2 : ℝ) * green d 0 y ^ 2 := Finset.sum_le_sum hterm
      _ = Cψ * lam ^ (2 : ℝ) * ∑ y ∈ (boxFinset (0 : Site d) m).filter
            (fun y => ¬ Sandpile.External.latticeNorm y < (R : ℝ)), green d 0 y ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ Cψ * lam ^ (2 : ℝ) * ∑' z : {z : Site d // (R : ℝ) ≤ Sandpile.External.latticeNorm z},
            green d 0 (z : Site d) ^ 2 := by
          refine mul_le_mul_of_nonneg_left hsubsum ?_; positivity
      _ ≤ Cψ * lam ^ (2 : ℝ) * (C1 * (R : ℝ) ^ (4 - (d : ℝ))) := by
          refine mul_le_mul_of_nonneg_left htsum ?_; positivity
      _ = Cψ * C1 * (lam ^ (2 : ℝ) * ((R : ℝ) ^ (4 - (d : ℝ)))) := by ring
      _ ≤ Cψ * C1 * lam ^ p := by
          refine mul_le_mul_of_nonneg_left hfin ?_; positivity
  calc ∑ y ∈ boxFinset (0 : Site d) m, w y
      = ∑ y ∈ (boxFinset (0 : Site d) m).filter
          (fun y => Sandpile.External.latticeNorm y < (R : ℝ)), w y +
        ∑ y ∈ (boxFinset (0 : Site d) m).filter
          (fun y => ¬ Sandpile.External.latticeNorm y < (R : ℝ)), w y := hsplit.symm
    _ ≤ Cψ * CG ^ q * Cbox * (3 : ℝ) ^ (d : ℕ) * A ^ p * lam ^ p + Cψ * C1 * lam ^ p :=
        add_le_add hinner houter
    _ ≤ (Cψ * CG ^ q * Cbox * (3 : ℝ) ^ (d : ℕ) * A ^ p + Cψ * C1 + 1) * lam ^ p := by
        nlinarith

/-! ### Optimizing the Chernoff parameter -/

/-- **The Chernoff optimum.**  From an exponent `-λ s + C λ^{β/(β-1)}` the choice
`λ = b s^{β-1}` with `b` small gives a stretched exponential of order `β`
(`sandpile.tex:4398-4404`). -/
theorem exists_chernoff_optimum (bt C : ℝ) (hbt : 1 < bt) (hC : 0 < C) :
    ∃ b c s₁ : ℝ, 0 < b ∧ 0 < c ∧ 1 ≤ s₁ ∧ ∀ s : ℝ, s₁ ≤ s →
      1 ≤ b * s ^ (bt - 1) ∧
        C * (b * s ^ (bt - 1)) ^ (bt / (bt - 1)) - b * s ^ (bt - 1) * s ≤ -(c * s ^ bt) := by
  have hbt1 : (0 : ℝ) < bt - 1 := by linarith
  set r : ℝ := bt / (bt - 1) with hrdef
  have hr1 : 1 < r := by rw [hrdef, lt_div_iff₀ hbt1]; linarith
  have hr10 : (0 : ℝ) < r - 1 := by linarith
  set b : ℝ := min 1 ((1 / (2 * C)) ^ (1 / (r - 1))) with hbdef
  have hbpos : 0 < b := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbsmall : b ≤ (1 / (2 * C)) ^ (1 / (r - 1)) := min_le_right _ _
  have hCbr : C * b ^ r ≤ b / 2 := by
    have h1 : b ^ (r - 1) ≤ ((1 / (2 * C)) ^ (1 / (r - 1))) ^ (r - 1) :=
      Real.rpow_le_rpow hbpos.le hbsmall hr10.le
    have h2 : ((1 / (2 * C)) ^ (1 / (r - 1))) ^ (r - 1) = 1 / (2 * C) := by
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hr10), Real.rpow_one]
    rw [h2] at h1
    have h3 : b ^ r = b ^ (r - 1) * b := by
      have hadd := Real.rpow_add hbpos (r - 1) 1
      rw [Real.rpow_one, show r - 1 + 1 = r by ring] at hadd
      exact hadd
    rw [h3]
    calc C * (b ^ (r - 1) * b) ≤ C * (1 / (2 * C) * b) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hbpos.le) hC.le
      _ = b / 2 := by field_simp
  set s₁ : ℝ := max 1 ((1 / b) ^ (1 / (bt - 1))) with hs₁def
  have hs₁1 : 1 ≤ s₁ := le_max_left _ _
  refine ⟨b, b / 2, s₁, hbpos, by linarith, hs₁1, fun s hs => ?_⟩
  have hs1 : (1 : ℝ) ≤ s := le_trans hs₁1 hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hlow : 1 ≤ b * s ^ (bt - 1) := by
    have h1 : ((1 / b) ^ (1 / (bt - 1)) : ℝ) ≤ s := le_trans (le_max_right _ _) hs
    have h2 : ((1 / b) ^ (1 / (bt - 1)) : ℝ) ^ (bt - 1) ≤ s ^ (bt - 1) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h1 hbt1.le
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hbt1), Real.rpow_one] at h2
    have h3 : b * (1 / b) ≤ b * s ^ (bt - 1) := mul_le_mul_of_nonneg_left h2 hbpos.le
    rwa [mul_one_div_cancel (ne_of_gt hbpos)] at h3
  refine ⟨hlow, ?_⟩
  have hpow1 : (b * s ^ (bt - 1)) ^ r = b ^ r * s ^ bt := by
    rw [Real.mul_rpow hbpos.le (Real.rpow_nonneg hs0.le _), ← Real.rpow_mul hs0.le]
    congr 2
    rw [hrdef]
    field_simp
  have hpow2 : b * s ^ (bt - 1) * s = b * s ^ bt := by
    have hadd := Real.rpow_add hs0 (bt - 1) 1
    rw [Real.rpow_one, show bt - 1 + 1 = bt by ring] at hadd
    rw [mul_assoc, ← hadd]
  have hsbt : (0 : ℝ) < s ^ bt := Real.rpow_pos_of_pos hs0 _
  rw [hpow1, hpow2]
  nlinarith

/-! ### The tail bound below the threshold -/

/-- A tail bound valid beyond a threshold extends to every `s ≥ 1` after the
constant is enlarged, since a probability is at most one. -/
theorem tail_bound_extend {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : ℝ → Set Ω) (c C s₁ β : ℝ)
    (hc : 0 < c) (hC : 0 < C) (_hs₁ : 1 ≤ s₁) (hβ : 0 ≤ β)
    (h : ∀ s : ℝ, s₁ ≤ s → μ (E s) ≤ ENNReal.ofReal (C * Real.exp (-(c * s ^ β)))) :
    ∀ s : ℝ, 1 ≤ s → μ (E s) ≤
      ENNReal.ofReal ((C + Real.exp (c * s₁ ^ β)) * Real.exp (-(c * s ^ β))) := by
  intro s hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hex : (0 : ℝ) < Real.exp (-(c * s ^ β)) := Real.exp_pos _
  rcases le_or_gt s₁ s with hcase | hcase
  · refine le_trans (h s hcase) (ENNReal.ofReal_le_ofReal ?_)
    have : (0 : ℝ) < Real.exp (c * s₁ ^ β) := Real.exp_pos _
    nlinarith
  · refine le_trans prob_le_one ?_
    have hmono : s ^ β ≤ s₁ ^ β := Real.rpow_le_rpow hs0.le hcase.le hβ
    have hge : Real.exp (-(c * s₁ ^ β)) ≤ Real.exp (-(c * s ^ β)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hone : (1 : ℝ) ≤ (C + Real.exp (c * s₁ ^ β)) * Real.exp (-(c * s ^ β)) := by
      have hkey : Real.exp (c * s₁ ^ β) * Real.exp (-(c * s₁ ^ β)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (c * s₁ ^ β), Real.exp_pos (-(c * s₁ ^ β))]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal ((C + Real.exp (c * s₁ ^ β)) * Real.exp (-(c * s ^ β))) :=
          ENNReal.ofReal_le_ofReal hone

/-! ### The lower tail of the Green average of the scenery -/

/-- **The case `γ = 1` of `lem:dgt4-stretched-green-scenery-tail`**
(`sandpile.tex:4361-4369`).  Only the exponential moment is used: a fixed small
parameter, of size the reciprocal of the largest Green value, gives a purely
exponential tail. -/
theorem exists_scenery_tail_linear (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) (hmean : ∫ z, z ∂ν = 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ s : ℝ, 1 ≤ s →
      LatticeProb.iidLaw d ν
          {ζ : Site d → ℝ | ∑' y : Site d, greenTime d m 0 y * ζ y ≤ -s} ≤
        ENNReal.ofReal (C * Real.exp (-(c * s))) := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hG : ∀ y : Site d, 0 ≤ green d 0 y := fun y =>
    tsum_nonneg fun k => heatKernel_nonneg _ _ _
  obtain ⟨CG, hCG0, hGbd⟩ := exists_green_pointwise hGH hd
  obtain ⟨-, hl2, -, -, -⟩ := hGH d hd
  have hid : Integrable id ν := integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hK₀ : (1 : ℝ) ≤ K₀ := by
    have h1 : ∫ _ : ℝ, (1 : ℝ) ∂ν ≤ ∫ z, Real.exp (θ₀ * |z|) ∂ν := by
      refine integral_mono (integrable_const 1) hexpint fun z => ?_
      have : (0 : ℝ) ≤ θ₀ * |z| := by positivity
      simpa using Real.one_le_exp this
    have huniv : ν.real Set.univ = 1 := by simp
    simp only [integral_const, smul_eq_mul, huniv, mul_one] at h1
    linarith
  have hSG := subGaussianOn_of_exp_moment ν θ₀ K₀ hθ₀ hexpint hexp hid hmean
  set cSG : ℝ := 16 / θ₀ ^ 2 * K₀ with hcSGdef
  have hcSG0 : 0 < cSG := by rw [hcSGdef]; positivity
  set A : ℝ := max CG 1 with hAdef
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hA0 : (0 : ℝ) < A := by linarith
  have hCGA : CG ≤ A := le_max_left _ _
  set lam : ℝ := θ₀ / (2 * A) with hlamdef
  have hlam0 : (0 : ℝ) < lam := by rw [hlamdef]; positivity
  have hlamA : lam * A = θ₀ / 2 := by rw [hlamdef]; field_simp
  set S2 : ℝ := ∑' y : Site d, green d 0 y ^ 2 with hS2def
  have hS2 : 0 ≤ S2 := tsum_nonneg fun y => sq_nonneg _
  set Mb : ℝ := cSG * lam ^ 2 * S2 with hMbdef
  have hGle : ∀ y : Site d, green d 0 y ≤ CG := by
    intro y
    refine le_trans (hGbd y) ?_
    have h1 : (1 + Sandpile.External.latticeNorm y) ^ (2 - (d : ℝ)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
      have : (0 : ℝ) ≤ Sandpile.External.latticeNorm y := Real.sqrt_nonneg _
      linarith
    nlinarith
  refine ⟨lam, Real.exp Mb, hlam0, Real.exp_pos _, fun m hm s hs => ?_⟩
  have hrange : ∀ y : Site d, |(-(lam * greenTime d m 0 y))| ≤ θ₀ / 2 := by
    intro y
    have h0 : 0 ≤ greenTime d m 0 y := greenTime_nonneg _ _ _
    have h1 : greenTime d m 0 y ≤ green d 0 y := greenTime_le_green hGH hd m y
    have h2 : lam * greenTime d m 0 y ≤ lam * A := by
      refine mul_le_mul_of_nonneg_left ?_ hlam0.le
      exact le_trans h1 (le_trans (hGle y) hCGA)
    rw [abs_neg, abs_of_nonneg (by positivity)]
    linarith [hlamA ▸ h2]
  have hSGy : ∀ y : Site d,
      Integrable (fun z => Real.exp (-(lam * greenTime d m 0 y) * z)) ν ∧
        ∫ z, Real.exp (-(lam * greenTime d m 0 y) * z) ∂ν
          ≤ Real.exp (cSG * (lam * greenTime d m 0 y) ^ 2) := by
    intro y
    obtain ⟨h1, h2⟩ := hSG (-(lam * greenTime d m 0 y)) (hrange y)
    simp only [id_eq] at h1 h2
    refine ⟨h1, le_trans h2 (le_of_eq ?_)⟩
    congr 1
    ring
  have hM : ∏ z ∈ boxFinset (0 : Site d) m,
      (∫ w, Real.exp (-(lam * greenTime d m 0 z) * w) ∂ν) ≤ Real.exp Mb := by
    refine prod_le_exp_of_sum_le _ _ (fun z => cSG * (lam * greenTime d m 0 z) ^ 2)
      (fun z _ => integral_nonneg fun w => (Real.exp_pos _).le)
      (fun z _ => (hSGy z).2) Mb ?_
    have hstep1 : ∑ z ∈ boxFinset (0 : Site d) m, cSG * (lam * greenTime d m 0 z) ^ 2
        = cSG * lam ^ 2 * ∑ z ∈ boxFinset (0 : Site d) m, greenTime d m 0 z ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    have hstep2 : ∑ z ∈ boxFinset (0 : Site d) m, greenTime d m 0 z ^ 2 ≤ S2 := by
      refine le_trans (Finset.sum_le_sum fun z _ => ?_)
        (hl2.sum_le_tsum (boxFinset (0 : Site d) m) fun z _ => sq_nonneg _)
      exact pow_le_pow_left₀ (greenTime_nonneg _ _ _) (greenTime_le_green hGH hd m z) 2
    rw [hstep1, hMbdef]
    exact mul_le_mul_of_nonneg_left hstep2 (by positivity)
  refine le_trans (iidLaw_greenTime_tail_le ν m lam hlam0.le
    (fun y => (hSGy y).1) Mb s hM) (le_of_eq ?_)
  congr 1
  rw [← Real.exp_add]
  ring_nf

/-- **The case `1 < γ` of `lem:dgt4-stretched-green-scenery-tail`.**  The two
regime bounds on the Laplace transform are summed over space by the two lemmas
above, and the Chernoff parameter is optimized at `λ = b s^{β-1}`. -/
theorem exists_scenery_tail_stretched (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) (hmean : ∫ z, z ∂ν = 0)
    (γ c₁ C₁ s₀ : ℝ) (hγ : 1 < γ) (hγd : γ ≠ (d : ℝ) / 2)
    (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hs₀ : 0 < s₀)
    (htail : ∀ s : ℝ, s₀ ≤ s →
      ν (Set.Iic (-s)) ≤ ENNReal.ofReal (C₁ * Real.exp (-(c₁ * s ^ γ)))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ s : ℝ, 1 ≤ s →
      LatticeProb.iidLaw d ν
          {ζ : Site d → ℝ | ∑' y : Site d, greenTime d m 0 y * ζ y ≤ -s} ≤
        ENNReal.ofReal (C * Real.exp (-(c * s ^ min γ ((d : ℝ) / 2)))) := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  have hγ1 : (0 : ℝ) < γ - 1 := by linarith
  obtain ⟨Cψ, hCψ0, hmgf⟩ :=
    exists_mgf_neg_bounds ν θ₀ K₀ hθ₀ hexpint hexp hmean γ c₁ C₁ s₀ hγ hc₁ hC₁ hs₀ htail
  have hq1 : 1 < γ / (γ - 1) := by rw [lt_div_iff₀ hγ1]; linarith
  have hβ1 : 1 < min γ ((d : ℝ) / 2) := lt_min hγ (by linarith)
  have hβ10 : (0 : ℝ) < min γ ((d : ℝ) / 2) - 1 := by linarith
  -- the space sum, in the two regions the exponent separates
  have hspace : ∃ CS : ℝ, 0 < CS ∧ ∀ (m : ℕ) (lam : ℝ), 1 ≤ lam → ∀ w : Site d → ℝ,
      (∀ y, lam * greenTime d m 0 y ≤ 1 →
        w y ≤ Cψ * (lam * greenTime d m 0 y) ^ (2 : ℝ)) →
      (∀ y, 1 ≤ lam * greenTime d m 0 y →
        w y ≤ Cψ * (lam * greenTime d m 0 y) ^ (γ / (γ - 1))) →
      ∑ y ∈ boxFinset (0 : Site d) m, w y ≤ CS *
        lam ^ (min γ ((d : ℝ) / 2) / (min γ ((d : ℝ) / 2) - 1)) := by
    rcases lt_or_gt_of_ne hγd with hcase | hcase
    · have hβ : min γ ((d : ℝ) / 2) = γ := min_eq_left hcase.le
      have hP : min γ ((d : ℝ) / 2) / (min γ ((d : ℝ) / 2) - 1) = γ / (γ - 1) := by rw [hβ]
      rw [hP]
      refine exists_space_sum_high hGH hd (γ / (γ - 1)) hq1 ?_ Cψ hCψ0.le
      rw [div_lt_div_iff₀ hd2 hγ1]
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)] at hcase
      nlinarith
    · have hβ : min γ ((d : ℝ) / 2) = (d : ℝ) / 2 := min_eq_right hcase.le
      have hP : min γ ((d : ℝ) / 2) / (min γ ((d : ℝ) / 2) - 1) = (d : ℝ) / ((d : ℝ) - 2) := by
        rw [hβ]; field_simp
      rw [hP]
      refine exists_space_sum_low hGH hd (γ / (γ - 1)) hq1 ?_ Cψ hCψ0.le
      rw [div_lt_div_iff₀ hγ1 hd2]
      rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)] at hcase
      nlinarith
  obtain ⟨CS, hCS0, hsum⟩ := hspace
  obtain ⟨b, cc, s₁, hb0, hcc0, hs₁1, hopt⟩ :=
    exists_chernoff_optimum (min γ ((d : ℝ) / 2)) CS hβ1 hCS0
  have hbase : ∀ m : ℕ, 1 ≤ m → ∀ s : ℝ, s₁ ≤ s →
      LatticeProb.iidLaw d ν
          {ζ : Site d → ℝ | ∑' y : Site d, greenTime d m 0 y * ζ y ≤ -s} ≤
        ENNReal.ofReal (1 * Real.exp (-(cc * s ^ min γ ((d : ℝ) / 2)))) := by
    intro m hm s hs
    obtain ⟨hlow, hexpo⟩ := hopt s hs
    set lam : ℝ := b * s ^ (min γ ((d : ℝ) / 2) - 1) with hlamdef
    have hlam0 : (0 : ℝ) < lam := by linarith
    set w : Site d → ℝ := fun z =>
      if lam * greenTime d m 0 z ≤ 1 then Cψ * (lam * greenTime d m 0 z) ^ (2 : ℝ)
      else Cψ * (lam * greenTime d m 0 z) ^ (γ / (γ - 1)) with hwdef
    have hmu : ∀ z : Site d, 0 ≤ lam * greenTime d m 0 z := fun z => by
      have := greenTime_nonneg (d := d) m 0 z; positivity
    have hfz : ∀ z : Site d,
        Integrable (fun x => Real.exp (-(lam * greenTime d m 0 z) * x)) ν ∧
          ∫ x, Real.exp (-(lam * greenTime d m 0 z) * x) ∂ν ≤ Real.exp (w z) := by
      intro z
      obtain ⟨hint, hsmallb, hlargeb⟩ := hmgf (lam * greenTime d m 0 z) (hmu z)
      have hcongr : ∀ x : ℝ, Real.exp (-(lam * greenTime d m 0 z) * x)
          = Real.exp (-((lam * greenTime d m 0 z) * x)) := fun x => by rw [neg_mul]
      have hint' : Integrable (fun x => Real.exp (-(lam * greenTime d m 0 z) * x)) ν :=
        hint.congr (Filter.Eventually.of_forall fun x => (hcongr x).symm)
      have heq : ∫ x, Real.exp (-(lam * greenTime d m 0 z) * x) ∂ν
          = ∫ x, Real.exp (-((lam * greenTime d m 0 z) * x)) ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hcongr)
      refine ⟨hint', ?_⟩
      rw [heq]
      simp only [hwdef]
      split_ifs with hc
      · refine le_trans (hsmallb hc) (Real.exp_le_exp.mpr (le_of_eq ?_))
        rw [rpow_two_eq_sq]
      · exact le_trans (hlargeb (not_le.mp hc).le) (Real.exp_le_exp.mpr le_rfl)
    have hsmallw : ∀ y : Site d, lam * greenTime d m 0 y ≤ 1 →
        w y ≤ Cψ * (lam * greenTime d m 0 y) ^ (2 : ℝ) := by
      intro y hy
      simp only [hwdef, hy, if_true]
      exact le_rfl
    have hlargew : ∀ y : Site d, 1 ≤ lam * greenTime d m 0 y →
        w y ≤ Cψ * (lam * greenTime d m 0 y) ^ (γ / (γ - 1)) := by
      intro y hy
      simp only [hwdef]
      split_ifs with hc
      · have hone : lam * greenTime d m 0 y = 1 := le_antisymm hc hy
        rw [hone, Real.one_rpow, Real.one_rpow]
      · exact le_rfl
    have hMb := hsum m lam hlow w hsmallw hlargew
    have hprod : ∏ z ∈ boxFinset (0 : Site d) m,
        (∫ x, Real.exp (-(lam * greenTime d m 0 z) * x) ∂ν)
          ≤ Real.exp (CS * lam ^ (min γ ((d : ℝ) / 2) / (min γ ((d : ℝ) / 2) - 1))) :=
      prod_le_exp_of_sum_le _ _ w (fun z _ => integral_nonneg fun x => (Real.exp_pos _).le)
        (fun z _ => (hfz z).2) _ hMb
    refine le_trans (iidLaw_greenTime_tail_le ν m lam hlam0.le
      (fun y => (hfz y).1) _ s hprod) (ENNReal.ofReal_le_ofReal ?_)
    rw [one_mul]
    exact Real.exp_le_exp.mpr (by linarith [hexpo])
  refine ⟨cc, 1 + Real.exp (cc * s₁ ^ min γ ((d : ℝ) / 2)), hcc0, by positivity,
    fun m hm s hs => ?_⟩
  exact tail_bound_extend (LatticeProb.iidLaw d ν)
    (fun s => {ζ : Site d → ℝ | ∑' y : Site d, greenTime d m 0 y * ζ y ≤ -s})
    cc 1 s₁ (min γ ((d : ℝ) / 2)) hcc0 one_pos hs₁1 (by linarith)
    (hbase m hm) s hs

end Sandpile
