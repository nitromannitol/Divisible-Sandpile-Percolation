/-
The arithmetic that closes Step 1 of `lem:dgt4-path-survival` (`sandpile.tex:5516-5527`).

`Support/LinPairSum.lean` proves the one-term bound `pair_term_le`, the near/far split of a
finite sum `sum_split_card_le`, and the two limits `tendsto_near_bound`, `tendsto_far_bound`.
What is added here is the three pieces that connect them to the paper's data:

* `pair_sum_split_le` applies the split to the normal-comparison pair sum itself, so that the
  whole sum is bounded by `|T| ρ_* e^{-B/(1+ρ_*)} + |S| C_f e^{-B/(1+C_f)}` with `T` the near
  pairs and `S` all pairs;
* `greenGram_div_le` turns the correlation gap of `Support/LinCorrGap.lean` into the bound
  `ρ_{ij} ≤ ρ_*` on the correlations of the Gaussian threshold field that the comparison
  inequality produces;
* `rpow_near_radius_pow` and `rpow_far_exponent_le` are the two computations with the near
  radius `L = (\log R)^{2/(d-4)}`: the near-pair count carries `L^d = (\log R)^{2d/(d-4)}`,
  and the far-pair correlation carries `(1+L)^{4-d} ≤ (\log R)^{-2}`, which is the paper's
  `|ρ_{xy}| ≤ C/(\log R)^2`.
-/
import Sandpile.Support.LinCorrGap

open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- **The near/far split of the normal-comparison pair sum.**  This is the inequality of
`sandpile.tex:5512-5522` with the two counts left as `T.card` and `S.card`. -/
theorem pair_sum_split_le {iota : Type*} (S T : Finset iota) (v B rs Cf : ℝ) (hv : 0 < v)
    (hrs : 0 ≤ rs) (hCf : 0 ≤ Cf)
    (rho : iota → ℝ) (bi bj : iota → ℝ)
    (hrho0 : ∀ p, 0 ≤ rho p)
    (hnear : ∀ p ∈ S, p ∈ T → rho p ≤ rs)
    (hfar : ∀ p ∈ S, p ∉ T → rho p ≤ Cf)
    (hbi : ∀ p ∈ S, B ≤ bi p ^ 2 / v) (hbj : ∀ p ∈ S, B ≤ bj p ^ 2 / v) :
    ∑ p ∈ S, rho p * Real.exp (-(bi p ^ 2 + bj p ^ 2) / (2 * v * (1 + rho p)))
      ≤ (T.card : ℝ) * (rs * Real.exp (-B / (1 + rs)))
        + (S.card : ℝ) * (Cf * Real.exp (-B / (1 + Cf))) := by
  refine sum_split_card_le S
    (fun p => rho p * Real.exp (-(bi p ^ 2 + bj p ^ 2) / (2 * v * (1 + rho p)))) T
    (rs * Real.exp (-B / (1 + rs))) (Cf * Real.exp (-B / (1 + Cf)))
    (by positivity) (by positivity) ?_ ?_
  · intro p hp hpT
    exact pair_term_le v B (rho p) rs (bi p) (bj p) hv (hrho0 p) (hnear p hp hpT)
      (hbi p hp) (hbj p hp)
  · intro p hp hpT
    exact pair_term_le v B (rho p) Cf (bi p) (bj p) hv (hrho0 p) (hfar p hp hpT)
      (hbi p hp) (hbj p hp)

/-- The correlation of the Gaussian threshold field is bounded by the correlation gap. -/
theorem greenGram_div_le (hd : 5 ≤ d) (v : ℝ≥0) (hv : 0 < (v : ℝ)) (rho : ℝ)
    (hgap : ∀ x y : Site d, x ≠ y →
      (∑' z : Site d, green d x z * green d y z) ≤ rho * greenSqSum d)
    {m : ℕ} (xs : Fin m → Site d) (i j : Fin m) (hij : xs i ≠ xs j) :
    greenGram d v xs i j / ((v : ℝ) * greenSqSum d) ≤ rho := by
  have hgs1 : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  have hgs : (0 : ℝ) < greenSqSum d := lt_of_lt_of_le zero_lt_one hgs1
  have hden : (0 : ℝ) < (v : ℝ) * greenSqSum d := by positivity
  have hval : greenGram d v xs i j
      = (v : ℝ) * ∑' z : Site d, green d (xs i) z * green d (xs j) z := rfl
  have hbound : (∑' z : Site d, green d (xs i) z * green d (xs j) z) ≤ rho * greenSqSum d :=
    hgap (xs i) (xs j) hij
  rw [hval, div_le_iff₀ hden]
  nlinarith [hbound, hv, hgs]

/-- The near radius `L = (log R)^{2/(d-4)}` raised to the power `d` is
`(log R)^{2d/(d-4)}`, the exponent of the paper's near-pair count. -/
theorem rpow_near_radius_pow (t : ℝ) (ht : 0 ≤ t) (d : ℕ) :
    (t ^ (2 / ((d : ℝ) - 4))) ^ d = t ^ (2 * (d : ℝ) / ((d : ℝ) - 4)) := by
  rw [← Real.rpow_natCast (t ^ (2 / ((d : ℝ) - 4))) d, ← Real.rpow_mul ht,
    div_mul_eq_mul_div]

/-- With the near radius `L = t^{2/(d-4)}` the far-pair Green decay exponent `(1+L)^{4-d}`
is at most `t^{-2}`: this is the paper's `|ρ_{xy}| ≤ C/(\log R)^2` at `sandpile.tex:5518`. -/
theorem rpow_far_exponent_le (t : ℝ) (ht : 1 ≤ t) (d : ℕ) (hd : 5 ≤ d) :
    (1 + t ^ (2 / ((d : ℝ) - 4))) ^ (4 - (d : ℝ)) ≤ t ^ (-2 : ℝ) := by
  have hdR : (5:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hD : (0:ℝ) < (d:ℝ) - 4 := by linarith
  have ht0 : (0:ℝ) ≤ t := by linarith
  have hexp : (0:ℝ) ≤ 2 / ((d:ℝ) - 4) := by positivity
  have hL1 : (1:ℝ) ≤ t ^ (2 / ((d:ℝ) - 4)) := Real.one_le_rpow ht hexp
  have hL0 : (0:ℝ) < t ^ (2 / ((d:ℝ) - 4)) := by linarith
  have hLle : t ^ (2 / ((d:ℝ) - 4)) ≤ 1 + t ^ (2 / ((d:ℝ) - 4)) := by linarith
  have hneg : (4:ℝ) - (d:ℝ) ≤ 0 := by linarith
  have hstep : (1 + t ^ (2 / ((d:ℝ) - 4))) ^ (4 - (d:ℝ))
      ≤ (t ^ (2 / ((d:ℝ) - 4))) ^ (4 - (d:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hL0 hLle hneg
  have harg : 2 / ((d:ℝ) - 4) * (4 - (d:ℝ)) = -2 := by
    field_simp
    ring
  have hval : (t ^ (2 / ((d:ℝ) - 4))) ^ (4 - (d:ℝ)) = t ^ (-2 : ℝ) := by
    rw [← Real.rpow_mul ht0, harg]
  rw [← hval]
  exact hstep

open Classical in
/-- The unordered pairs of `sandpile.tex:5508` as a sum over a Finset of ordered pairs: this
is the shape `pair_sum_split_le` consumes. -/
theorem sum_Ioi_eq_sum_pairs {m : ℕ} (f : Fin m → Fin m → ℝ) :
    ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, f i j
      = ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin m × Fin m => p.1 < p.2),
          f p.1 p.2 := by
  classical
  have hIoi : ∀ i : Fin m, Finset.Ioi i = Finset.univ.filter (fun j : Fin m => i < j) := by
    intro i
    ext j
    simp [Finset.mem_Ioi]
  simp only [hIoi, Finset.sum_filter]
  rw [Finset.sum_product]

end Sandpile
