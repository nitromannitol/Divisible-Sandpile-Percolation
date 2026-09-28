import Sandpile.Support.ExplDyadic
import Sandpile.External.MaxDisplacementProved
import Sandpile.Support.ContCoeffCoarse

/-!
# The Walk Cutoff Error

The walk half of the cutoff error of `sandpile.tex:1908-1921`, in the vocabulary
of the walk, with the maximal-displacement estimate discharged.

`Sandpile.Continuum.exists_cutoff_radius` is the analytic statement: a field
bounded on the `j`-th dyadic annulus by `K (2^{j+1}A)^p`, together with a
Gaussian tail `C e^{-c(2^jA)^2/T}` for reaching that annulus, has a cutoff error
at most `ε` once the cutoff radius is large.  Here that is read on the walk, and
the Gaussian tail is proved rather than assumed: it is the maximal-displacement
estimate `Sandpile.External.maxDisplacement` of `eq:rw-max-displacement`, which
is sealed in the repository.

Three bridges are needed.  `norm_scaledSite_sub` says that the Euclidean norm of
the difference of two scaled sites is the lattice distance divided by the scale,
which is what turns the maximal estimate, stated for the lattice distance, into
a statement about the scaled walk.  `walkLaw_real_displacement_le` reads the
maximal estimate at the integer radius `⌊rR⌋`, which is at least `rR/2` once
`rR ≥ 2`, and so pays a factor `4` in the rate.  `exists_walk_annulus_reach_bound`
puts the starting point back in: the walk reaches the `j`-th annulus about the
origin only by moving `2^jA - ρ` from a start of norm at most `ρ`, and that is at
least half of `2^jA` once `2ρ ≤ A`, which pays another factor `4`.  The rate of
`exists_walk_cutoff_error` is therefore a sixteenth of the rate of the maximal
estimate, and the constant is unchanged.

The confinement that makes the sum finite is discharged too.  The walk stopped
before time `m` lies in the lattice box of radius `m` about its start, so its
scaled position has norm at most `ρ + dm/R`, and the number of annuli that carry
any mass is finite; `exists_walk_cutoff_error_of_annulus_bound` is the form with
no confinement hypothesis and no annulus count, which is what the proof of
Theorem 1.3(i)(b) uses.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}


/-- The Euclidean norm of the difference of two scaled sites is the lattice distance
divided by the scale. -/
theorem norm_scaledSite_sub (R : ℝ) (hR : 0 < R) (y x : Site d) :
    ‖External.Lclt.scaledSite R y - External.Lclt.scaledSite R x‖
      = External.latticeDist y x / R := by
  have hcoord : ∀ i : Fin d,
      (External.Lclt.scaledSite R y - External.Lclt.scaledSite R x) i
        = ((y i - x i : ℤ) : ℝ) / R := by
    intro i
    show ((y i : ℤ) : ℝ) / R - ((x i : ℤ) : ℝ) / R = _
    push_cast
    ring
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin d,
      ‖(External.Lclt.scaledSite R y - External.Lclt.scaledSite R x) i‖ ^ 2
        = (∑ i : Fin d, ((y i - x i : ℤ) : ℝ) ^ 2) * (R⁻¹) ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hcoord i, Real.norm_eq_abs, sq_abs, div_pow]
    field_simp
  rw [hsum, Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
    Real.sqrt_sq (le_of_lt (inv_pos.mpr hR))]
  rw [div_eq_mul_inv]
  rfl

/-- **The maximal-displacement estimate, read on the scaled walk.**  The walk stopped before
time `m` has moved `r` in the scaled picture only if it has moved `rR` in the lattice, and
the integer radius `⌊rR⌋` is at least half of `rR` once `rR ≥ 2`; that is the factor four in
the rate. -/
theorem walkLaw_real_displacement_le (hd : 1 ≤ d) {C₀ c₀ : ℝ} (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (hmax : ∀ (n : ℕ) (N : ℝ), 1 ≤ n → 1 ≤ N → ∀ x : Site d,
      walkLaw d x {X : ℕ → Site d | ∃ k ≤ n, N ≤ External.latticeDist (X k) x} ≤
        ENNReal.ofReal (C₀ * Real.exp (-c₀ * N ^ 2 / (n : ℝ))))
    (R : ℝ) (hR : 0 < R) (x : Site d) (m : ℕ) (hm : 1 ≤ m)
    (τ : (ℕ → Site d) → ℕ) (hτ : ∀ X, τ X ≤ m) (r : ℝ) (hr : 2 ≤ r * R) :
    (walkLaw d x).real {X : ℕ → Site d |
        r ≤ ‖External.Lclt.scaledSite R (X (τ X)) - External.Lclt.scaledSite R x‖}
      ≤ C₀ * Real.exp (-(c₀ * (r * R) ^ 2 / (4 * (m : ℝ)))) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  have hrR0 : (0 : ℝ) ≤ r * R := by linarith
  set N : ℕ := ⌊r * R⌋₊ with hNdef
  have hNle : (N : ℝ) ≤ r * R := Nat.floor_le hrR0
  have hNlt : r * R < (N : ℝ) + 1 := Nat.lt_floor_add_one (r * R)
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ r * R))
  have hNhalf : r * R / 2 ≤ (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hsub : {X : ℕ → Site d |
        r ≤ ‖External.Lclt.scaledSite R (X (τ X)) - External.Lclt.scaledSite R x‖}
      ⊆ {X : ℕ → Site d | ∃ k ≤ m, (N : ℝ) ≤ External.latticeDist (X k) x} := by
    intro X hX
    refine ⟨τ X, hτ X, ?_⟩
    have hXn : r ≤ External.latticeDist (X (τ X)) x / R := by
      rw [← norm_scaledSite_sub R hR]
      exact hX
    have : r * R ≤ External.latticeDist (X (τ X)) x := by
      rw [le_div_iff₀ hR] at hXn
      exact hXn
    linarith
  have hmono : (walkLaw d x).real {X : ℕ → Site d |
        r ≤ ‖External.Lclt.scaledSite R (X (τ X)) - External.Lclt.scaledSite R x‖}
      ≤ (walkLaw d x).real {X : ℕ → Site d | ∃ k ≤ m, (N : ℝ) ≤ External.latticeDist (X k) x} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hval : (0 : ℝ) ≤ C₀ * Real.exp (-c₀ * (N : ℝ) ^ 2 / (m : ℝ)) := by positivity
  have hbound : (walkLaw d x).real
      {X : ℕ → Site d | ∃ k ≤ m, (N : ℝ) ≤ External.latticeDist (X k) x}
      ≤ C₀ * Real.exp (-c₀ * (N : ℝ) ^ 2 / (m : ℝ)) := by
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have := ENNReal.toReal_mono (by simp) (hmax m (N : ℝ) hm hN1' x)
    rwa [ENNReal.toReal_ofReal hval] at this
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp : Real.exp (-c₀ * (N : ℝ) ^ 2 / (m : ℝ))
      ≤ Real.exp (-(c₀ * (r * R) ^ 2 / (4 * (m : ℝ)))) := by
    refine Real.exp_le_exp.mpr ?_
    have hsq2 : (r * R) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith [hNhalf, hrR0, hNpos]
    have hkey : c₀ * (r * R) ^ 2 / (4 * (m : ℝ)) ≤ c₀ * (N : ℝ) ^ 2 / (m : ℝ) := by
      rw [div_le_div_iff₀ (by linarith) hmpos]
      nlinarith [mul_le_mul_of_nonneg_left hsq2 (mul_nonneg hc₀.le hmpos.le)]
    have hrw : -c₀ * (N : ℝ) ^ 2 / (m : ℝ) = -(c₀ * (N : ℝ) ^ 2 / (m : ℝ)) := by ring
    rw [hrw]
    linarith [hkey]
  calc (walkLaw d x).real {X : ℕ → Site d |
        r ≤ ‖External.Lclt.scaledSite R (X (τ X)) - External.Lclt.scaledSite R x‖}
      ≤ C₀ * Real.exp (-c₀ * (N : ℝ) ^ 2 / (m : ℝ)) := le_trans hmono hbound
    _ ≤ C₀ * Real.exp (-(c₀ * (r * R) ^ 2 / (4 * (m : ℝ)))) :=
        mul_le_mul_of_nonneg_left hexp hC₀.le


/-- **The walk reaches the `j`-th dyadic annulus about the origin with a Gaussian
probability.**  From a start of scaled norm at most `ρ`, reaching norm `2^jA` means moving
`2^jA - ρ`, which is at least half of `2^jA` once `2ρ ≤ A`.  The constants depend only on
the dimension; the rate is a sixteenth of the rate of `eq:rw-max-displacement`. -/
theorem exists_walk_annulus_reach_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T → ∀ R : ℝ, 1 ≤ R → ∀ (x : Site d) (ρ A : ℝ), 0 ≤ ρ →
        ‖External.Lclt.scaledSite R x‖ ≤ ρ → 2 * ρ ≤ A → 4 ≤ A →
        ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ R ^ 2 * T → ∀ τ : (ℕ → Site d) → ℕ, (∀ X, τ X ≤ m) →
        ∀ j : ℕ,
          (walkLaw d x).real {X : ℕ → Site d |
              2 ^ j * A ≤ ‖External.Lclt.scaledSite R (X (τ X))‖}
            ≤ C * Real.exp (-(c * (2 ^ j * A) ^ 2 / T)) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hmax⟩ := External.maxDisplacement d hd
  refine ⟨C₀, c₀ / 16, hC₀, by positivity, ?_⟩
  intro T hT R hR x ρ A hρ hxρ hρA hA4 m hm hmT τ hτ j
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hA0 : (0 : ℝ) < A := by linarith
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have h2jA : A ≤ 2 ^ j * A := by nlinarith
  set r : ℝ := 2 ^ j * A - ρ with hrdef
  have hrhalf : 2 ^ j * A / 2 ≤ r := by
    have : ρ ≤ A / 2 := by linarith
    have : ρ ≤ 2 ^ j * A / 2 := by linarith
    linarith
  have hr0 : (0 : ℝ) ≤ r := by nlinarith
  have hrR : 2 ≤ r * R := by nlinarith
  have hsub : {X : ℕ → Site d |
        2 ^ j * A ≤ ‖External.Lclt.scaledSite R (X (τ X))‖}
      ⊆ {X : ℕ → Site d |
        r ≤ ‖External.Lclt.scaledSite R (X (τ X)) - External.Lclt.scaledSite R x‖} := by
    intro X hX
    have hnorm : ‖External.Lclt.scaledSite R (X (τ X))‖ - ‖External.Lclt.scaledSite R x‖
        ≤ ‖External.Lclt.scaledSite R (X (τ X)) - External.Lclt.scaledSite R x‖ :=
      norm_sub_norm_le _ _
    have hXle : 2 ^ j * A ≤ ‖External.Lclt.scaledSite R (X (τ X))‖ := hX
    simp only [Set.mem_setOf_eq, hrdef]
    linarith
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  have hmono : (walkLaw d x).real {X : ℕ → Site d |
        2 ^ j * A ≤ ‖External.Lclt.scaledSite R (X (τ X))‖}
      ≤ (walkLaw d x).real {X : ℕ → Site d |
        r ≤ ‖External.Lclt.scaledSite R (X (τ X)) - External.Lclt.scaledSite R x‖} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hbase := walkLaw_real_displacement_le hd hC₀ hc₀ hmax R hR0 x m hm τ hτ r hrR
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp : Real.exp (-(c₀ * (r * R) ^ 2 / (4 * (m : ℝ))))
      ≤ Real.exp (-(c₀ / 16 * (2 ^ j * A) ^ 2 / T)) := by
    refine Real.exp_le_exp.mpr ?_
    have hsq : (2 ^ j * A) ^ 2 / 4 ≤ r ^ 2 := by nlinarith [hrhalf, hr0]
    have hkey : c₀ / 16 * (2 ^ j * A) ^ 2 / T ≤ c₀ * (r * R) ^ 2 / (4 * (m : ℝ)) := by
      rw [div_le_div_iff₀ hT (by linarith)]
      have hQ : (r * R) ^ 2 = r ^ 2 * R ^ 2 := by ring
      have hc1 : (0 : ℝ) ≤ c₀ * (2 ^ j * A) ^ 2 / 4 := by positivity
      have hstep1 : c₀ * (2 ^ j * A) ^ 2 / 4 * (m : ℝ)
          ≤ c₀ * (2 ^ j * A) ^ 2 / 4 * (R ^ 2 * T) := mul_le_mul_of_nonneg_left hmT hc1
      have hc2 : (0 : ℝ) ≤ c₀ * (R ^ 2 * T) := by positivity
      have hstep2 : c₀ * (R ^ 2 * T) * ((2 ^ j * A) ^ 2 / 4)
          ≤ c₀ * (R ^ 2 * T) * r ^ 2 := mul_le_mul_of_nonneg_left hsq hc2
      nlinarith [hstep1, hstep2, hQ]
    linarith [hkey]
  calc (walkLaw d x).real {X : ℕ → Site d |
        2 ^ j * A ≤ ‖External.Lclt.scaledSite R (X (τ X))‖}
      ≤ C₀ * Real.exp (-(c₀ * (r * R) ^ 2 / (4 * (m : ℝ)))) := le_trans hmono hbase
    _ ≤ C₀ * Real.exp (-(c₀ / 16 * (2 ^ j * A) ^ 2 / T)) :=
        mul_le_mul_of_nonneg_left hexp hC₀.le


/-- **The dyadic sum of `sandpile.tex:1908-1921`, on the walk.**  A reward bounded on the
`j`-th dyadic annulus by `K (2^{j+1}A)^p`, and a Gaussian tail for reaching that annulus,
give a cutoff error at most `ε` once the cutoff radius is large enough, uniformly in the
scale, in the starting point, in the horizon and in the stopping time. -/
theorem exists_walk_cutoff_radius (hd : 1 ≤ d) (p : ℕ) {K C c T ε : ℝ} (hK : 0 ≤ K)
    (hC : 0 ≤ C) (hc : 0 < c) (hT : 0 < T) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ (x : Site d) (R : ℝ) (n : ℕ)
        (τ : (ℕ → Site d) → ℕ) (F : ℕ → (ℕ → Site d) → ℝ),
        (∀ j : ℕ, MeasurableSet {X : ℕ → Site d |
            2 ^ j * A ≤ ‖External.Lclt.scaledSite R (X (τ X))‖}) →
        (∀ᵐ X ∂(walkLaw d x),
            ‖External.Lclt.scaledSite R (X (τ X))‖ < 2 ^ (n + 1) * A) →
        (∀ X : ℕ → Site d, ∀ j ≤ n,
            External.Lclt.scaledSite R (X (τ X)) ∈ Continuum.dyadicAnnulus A j →
            |F (τ X) X| ≤ K * (2 ^ (j + 1) * A) ^ p) →
        (∀ j : ℕ, (walkLaw d x).real {X : ℕ → Site d |
            2 ^ j * A ≤ ‖External.Lclt.scaledSite R (X (τ X))‖}
              ≤ C * Real.exp (-(c * (2 ^ j * A) ^ 2 / T))) →
        Integrable (fun X => (1 - Continuum.cutoff A
            (External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X|) (walkLaw d x) →
        (∫ X, (1 - Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X))))
            * |F (τ X) X| ∂(walkLaw d x)) ≤ ε := by
  obtain ⟨A₀, hA₀1, hA₀⟩ := Continuum.exists_cutoff_radius p hK hC hc hT hε
  refine ⟨A₀, hA₀1, ?_⟩
  intro A hA x R n τ F hmeas hconf hV hq hint
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos (le_trans hA₀1 hA)
  have hM : ∀ j : ℕ, (0 : ℝ) ≤ K * (2 ^ (j + 1) * A) ^ p := by
    intro j
    positivity
  have hstep := Continuum.integral_cutoff_le_sum_reach (walkLaw d x) A hA0 n
      (fun j => K * (2 ^ (j + 1) * A) ^ p) hM
      (fun X => External.Lclt.scaledSite R (X (τ X))) (fun X => F (τ X) X)
      hmeas hconf hV hint
  refine hstep.trans (le_trans (Finset.sum_le_sum ?_) (hA₀ A hA n))
  intro j _
  exact mul_le_mul_of_nonneg_left (hq j) (hM j)

/-- **The walk half of the cutoff error of `sandpile.tex:1908-1921`.**  For a reward bounded
on the `j`-th dyadic annulus by a fixed power of the radius, the cutoff error of the walk is
at most `ε` once the cutoff radius is large enough, uniformly over the scale, over the
starting points of scaled norm at most `ρ`, over the horizons `m ≤ R^2 T` and over the
stopping times below the horizon.  The Gaussian tail for reaching an annulus is the sealed
maximal-displacement estimate, so the only inputs left to the caller are the bound on the
field, the confinement of the stopped walk, and the two side conditions of the integral. -/
theorem exists_walk_cutoff_error (d : ℕ) (hd : 1 ≤ d) (p : ℕ) {K T ε : ℝ} (hK : 0 ≤ K)
    (hT : 0 < T) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 4 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ R : ℝ, 1 ≤ R → ∀ (x : Site d) (ρ : ℝ), 0 ≤ ρ →
      ‖External.Lclt.scaledSite R x‖ ≤ ρ → 2 * ρ ≤ A →
      ∀ m n : ℕ, 1 ≤ m → (m : ℝ) ≤ R ^ 2 * T →
      ∀ τ : (ℕ → Site d) → ℕ, (∀ X, τ X ≤ m) →
      ∀ F : ℕ → (ℕ → Site d) → ℝ,
        (∀ j : ℕ, MeasurableSet {X : ℕ → Site d |
            2 ^ j * A ≤ ‖External.Lclt.scaledSite R (X (τ X))‖}) →
        (∀ᵐ X ∂(walkLaw d x),
            ‖External.Lclt.scaledSite R (X (τ X))‖ < 2 ^ (n + 1) * A) →
        (∀ X : ℕ → Site d, ∀ j ≤ n,
            External.Lclt.scaledSite R (X (τ X)) ∈ Continuum.dyadicAnnulus A j →
            |F (τ X) X| ≤ K * (2 ^ (j + 1) * A) ^ p) →
        Integrable (fun X => (1 - Continuum.cutoff A
            (External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X|) (walkLaw d x) →
        (∫ X, (1 - Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X))))
            * |F (τ X) X| ∂(walkLaw d x)) ≤ ε := by
  obtain ⟨C, c, hC, hc, hreach⟩ := exists_walk_annulus_reach_bound d hd
  obtain ⟨A₀, hA₀1, hA₀⟩ := exists_walk_cutoff_radius hd p hK hC.le hc hT hε
  refine ⟨max A₀ 4, le_max_right _ _, ?_⟩
  intro A hA R hR x ρ hρ hxρ hρA m n hm hmT τ hτ F hmeas hconf hV hint
  have hAA₀ : A₀ ≤ A := le_trans (le_max_left _ _) hA
  have hA4 : (4 : ℝ) ≤ A := le_trans (le_max_right _ _) hA
  exact hA₀ A hAA₀ x R n τ F hmeas hconf hV
    (fun j => hreach T hT R hR x ρ A hρ hxρ hρA hA4 m hm hmT τ hτ j) hint


/-- The Euclidean site distance is at most `d` times the box distance, because each
coordinate difference is at most the box distance. -/
theorem latticeDist_le_boxDist (x y : Site d) :
    External.latticeDist x y ≤ (d : ℝ) * (boxDist x y : ℝ) := by
  refine le_trans (Sandpile.Support.latticeDist_le_sum_abs x y) ?_
  have hb : ∀ i : Fin d, |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| ≤ (boxDist x y : ℝ) := by
    intro i
    have hnat : (x i - y i).natAbs ≤ boxDist x y :=
      Finset.le_sup (f := fun j => (x j - y j).natAbs) (Finset.mem_univ i)
    have hcast : (((x i - y i).natAbs : ℕ) : ℝ) = |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| := by
      rw [Nat.cast_natAbs]
      push_cast
      ring_nf
    rw [← hcast]
    exact_mod_cast hnat
  calc ∑ i : Fin d, |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)|
      ≤ ∑ _i : Fin d, (boxDist x y : ℝ) := Finset.sum_le_sum (fun i _ => hb i)
    _ = (d : ℝ) * (boxDist x y : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The stopped walk is confined.**  The walk lies in the lattice box of radius `n` about
its start at time `n`, so a walk stopped before time `m` has scaled norm at most the scaled
norm of its start plus `dm/R`. -/
theorem ae_norm_scaledSite_stopped_le (hd : 1 ≤ d) (x : Site d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (τ : (ℕ → Site d) → ℕ) (hτ : ∀ X, τ X ≤ m) :
    ∀ᵐ X ∂(walkLaw d x), ‖External.Lclt.scaledSite R (X (τ X))‖
      ≤ ‖External.Lclt.scaledSite R x‖ + (d : ℝ) * (m : ℝ) / R := by
  filter_upwards [ae_boxDist_walk hd x] with X hX
  have hbox : (boxDist (X (τ X)) x : ℝ) ≤ (m : ℝ) := by
    have hsymm : boxDist (X (τ X)) x = boxDist x (X (τ X)) := by
      unfold boxDist
      exact Finset.sup_congr rfl (fun i _ => by rw [← Int.natAbs_neg, neg_sub])
    have h1 := hX (τ X)
    have h2 := hτ X
    rw [hsymm]
    exact_mod_cast le_trans h1 h2
  have hdist : External.latticeDist (X (τ X)) x ≤ (d : ℝ) * (m : ℝ) := by
    refine le_trans (latticeDist_le_boxDist (X (τ X)) x) ?_
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    exact mul_le_mul_of_nonneg_left hbox hd0
  have hnorm := norm_sub_norm_le (External.Lclt.scaledSite R (X (τ X)))
    (External.Lclt.scaledSite R x)
  rw [norm_scaledSite_sub R hR] at hnorm
  have hdiv : External.latticeDist (X (τ X)) x / R ≤ (d : ℝ) * (m : ℝ) / R := by
    gcongr
  linarith

/-- **The walk half of the cutoff error of `sandpile.tex:1908-1921`, with every side
condition of the walk discharged.**  Only the bound on the field over the dyadic annuli, the
measurability of the reaching events and the integrability of the integrand are left to the
caller: the Gaussian tail for reaching an annulus is the sealed maximal-displacement
estimate, and the confinement that makes the dyadic sum finite is the confinement of the
walk in the box of radius `m`.  The two side conditions are discharged in turn by
`measurableSet_reach_stopped` and `integrable_cutoff_error_of_bound` below. -/
theorem exists_walk_cutoff_error_of_annulus_bound (d : ℕ) (hd : 1 ≤ d) (p : ℕ)
    {K T ε : ℝ} (hK : 0 ≤ K) (hT : 0 < T) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 4 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ R : ℝ, 1 ≤ R → ∀ (x : Site d) (ρ : ℝ), 0 ≤ ρ →
      ‖External.Lclt.scaledSite R x‖ ≤ ρ → 2 * ρ ≤ A →
      ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ R ^ 2 * T →
      ∀ τ : (ℕ → Site d) → ℕ, (∀ X, τ X ≤ m) →
      ∀ F : ℕ → (ℕ → Site d) → ℝ,
        (∀ j : ℕ, MeasurableSet {X : ℕ → Site d |
            2 ^ j * A ≤ ‖External.Lclt.scaledSite R (X (τ X))‖}) →
        (∀ (X : ℕ → Site d) (j : ℕ),
            External.Lclt.scaledSite R (X (τ X)) ∈ Continuum.dyadicAnnulus A j →
            |F (τ X) X| ≤ K * (2 ^ (j + 1) * A) ^ p) →
        Integrable (fun X => (1 - Continuum.cutoff A
            (External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X|) (walkLaw d x) →
        (∫ X, (1 - Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X))))
            * |F (τ X) X| ∂(walkLaw d x)) ≤ ε := by
  obtain ⟨A₀, hA₀4, hA₀⟩ := exists_walk_cutoff_error d hd p hK hT hε
  refine ⟨A₀, hA₀4, ?_⟩
  intro A hA R hR x ρ hρ hxρ hρA m hm hmT τ hτ F hmeas hV hint
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le (by linarith) (le_trans hA₀4 hA)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((ρ + (d : ℝ) * (m : ℝ) / R) / A)
    (by norm_num : (1 : ℝ) < 2)
  have hlt : ρ + (d : ℝ) * (m : ℝ) / R < 2 ^ n * A := by
    rw [div_lt_iff₀ hA0] at hn
    exact hn
  have hstep : (2 : ℝ) ^ n * A ≤ 2 ^ (n + 1) * A := by
    have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    nlinarith
  have hconf : ∀ᵐ X ∂(walkLaw d x),
      ‖External.Lclt.scaledSite R (X (τ X))‖ < 2 ^ (n + 1) * A := by
    filter_upwards [ae_norm_scaledSite_stopped_le hd x R hR0 m τ hτ] with X hX
    have : ‖External.Lclt.scaledSite R (X (τ X))‖ ≤ ρ + (d : ℝ) * (m : ℝ) / R := by
      linarith [hX, hxρ]
    linarith
  exact hA₀ A hA R hR x ρ hρ hxρ hρA m n hm hmT τ hτ F hmeas hconf
    (fun X j _ => hV X j) hint



/-- The event that the scaled walk has reached a given radius when it stops is measurable: a
bounded stopping time and the position at it are settled by the positions up to the bound. -/
theorem measurableSet_reach_stopped (R c : ℝ) {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) {m : ℕ} (hτm : ∀ X, τ X ≤ m) :
    MeasurableSet {X : ℕ → Site d | c ≤ ‖External.Lclt.scaledSite R (X (τ X))‖} := by
  have hdep : LatticeProb.DependsUpTo m
      (fun X : ℕ → Site d => ‖External.Lclt.scaledSite R (X (τ X))‖) := by
    intro X Y hXY
    have hτeq : τ X = τ Y :=
      LatticeProb.dependsUpTo_of_isWalkStopping hτ hτm X Y hXY
    have hpt : X (τ Y) = Y (τ Y) := hXY (τ Y) (hτm Y)
    simp only []
    rw [hτeq, hpt]
  have hmeas : Measurable
      (fun X : ℕ → Site d => ‖External.Lclt.scaledSite R (X (τ X))‖) :=
    LatticeProb.measurable_of_dependsUpTo hdep
  exact hmeas measurableSet_Ici

/-- The integrand of the cutoff error is measurable, for a measurable stopped reward. -/
theorem measurable_cutoff_stopped (R A : ℝ) {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) {m : ℕ} (hτm : ∀ X, τ X ≤ m)
    (F : ℕ → (ℕ → Site d) → ℝ) (hF : Measurable fun X : ℕ → Site d => F (τ X) X) :
    Measurable fun X : ℕ → Site d =>
      (1 - Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X| := by
  have hdep : LatticeProb.DependsUpTo m
      (fun X : ℕ → Site d =>
        Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X)))) := by
    intro X Y hXY
    have hτeq : τ X = τ Y :=
      LatticeProb.dependsUpTo_of_isWalkStopping hτ hτm X Y hXY
    have hpt : X (τ Y) = Y (τ Y) := hXY (τ Y) (hτm Y)
    simp only []
    rw [hτeq, hpt]
  have hcut : Measurable
      (fun X : ℕ → Site d =>
        Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X)))) :=
    LatticeProb.measurable_of_dependsUpTo hdep
  exact (measurable_const.sub hcut).mul hF.abs

/-- The integrand of the cutoff error is integrable, for a measurable stopped reward that is
almost surely bounded: the complement of the cutoff has values in `[0,1]`. -/
theorem integrable_cutoff_error_of_bound (hd : 1 ≤ d) (x : Site d) (R A M : ℝ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) {m : ℕ} (hτm : ∀ X, τ X ≤ m)
    (F : ℕ → (ℕ → Site d) → ℝ) (hF : Measurable fun X : ℕ → Site d => F (τ X) X)
    (hb : ∀ᵐ X ∂(walkLaw d x), |F (τ X) X| ≤ M) :
    Integrable (fun X : ℕ → Site d =>
      (1 - Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X|)
      (walkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  refine Integrable.mono' (integrable_const M)
    (measurable_cutoff_stopped R A hτ hτm F hF).aestronglyMeasurable ?_
  filter_upwards [hb] with X hX
  have h0 : 0 ≤ Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X))) :=
    Continuum.cutoff_nonneg A _
  have h1 : Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X))) ≤ 1 :=
    Continuum.cutoff_le_one A _
  have habs : (0 : ℝ) ≤ |F (τ X) X| := abs_nonneg _
  have hnn : (0 : ℝ)
      ≤ (1 - Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X| := by
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  nlinarith



/-- The integrand of the cutoff error is integrable whenever the stopped reward is, because
the complement of the cutoff has values in `[0,1]`. -/
theorem integrable_cutoff_error_of_integrable (x : Site d) (R A : ℝ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) {m : ℕ} (hτm : ∀ X, τ X ≤ m)
    (F : ℕ → (ℕ → Site d) → ℝ) (hF : Measurable fun X : ℕ → Site d => F (τ X) X)
    (hint : Integrable (fun X : ℕ → Site d => F (τ X) X) (walkLaw d x)) :
    Integrable (fun X : ℕ → Site d =>
      (1 - Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X|)
      (walkLaw d x) := by
  refine Integrable.mono' hint.abs
    (measurable_cutoff_stopped R A hτ hτm F hF).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun X => ?_)
  have h0 : 0 ≤ Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X))) :=
    Continuum.cutoff_nonneg A _
  have h1 : Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X))) ≤ 1 :=
    Continuum.cutoff_le_one A _
  have habs : (0 : ℝ) ≤ |F (τ X) X| := abs_nonneg _
  have hnn : (0 : ℝ)
      ≤ (1 - Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X| := by
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  nlinarith

/-- **`E₁` of the four-term bound: the walk cutoff error of `sandpile.tex:1908-1921`, read as
the gap between the two suprema.**  For a reward bounded on the `j`-th dyadic annulus by a
fixed power of the radius, the optimal-stopping value of the reward and the value of its
cut-off version differ by at most `ε` once the cutoff radius is large enough, uniformly over
the scale, over the starting points of scaled norm at most `ρ`, and over the horizons
`m ≤ R^2 T`.  This is the hypothesis `hcut` of
`Sandpile.abs_rescaled_odometer_sub_brownianValue_le`. -/
theorem exists_walk_cutoff_stoppingSup_gap (d : ℕ) (hd : 1 ≤ d) (p : ℕ) {K T ε : ℝ}
    (hK : 0 ≤ K) (hT : 0 < T) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 4 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ R : ℝ, 1 ≤ R → ∀ (x : Site d) (ρ : ℝ), 0 ≤ ρ →
      ‖External.Lclt.scaledSite R x‖ ≤ ρ → 2 * ρ ≤ A →
      ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ R ^ 2 * T →
      ∀ F : ℕ → (ℕ → Site d) → ℝ,
        (∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ m) →
          Measurable fun X : ℕ → Site d => F (τ X) X) →
        (∀ τ : (ℕ → Site d) → ℕ, (∀ X, τ X ≤ m) → ∀ (X : ℕ → Site d) (j : ℕ),
            External.Lclt.scaledSite R (X (τ X)) ∈ Continuum.dyadicAnnulus A j →
            |F (τ X) X| ≤ K * (2 ^ (j + 1) * A) ^ p) →
        BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ m) ∧
          a = ∫ X, F (τ X) X ∂(walkLaw d x)} →
        BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ m) ∧
          a = ∫ X, Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X))) * F (τ X) X
            ∂(walkLaw d x)} →
        (∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ m) →
          Integrable (fun X => F (τ X) X) (walkLaw d x)) →
        (∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ m) →
          Integrable (fun X => Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X)))
            * F (τ X) X) (walkLaw d x)) →
        |stoppingSup m x F - stoppingSup m x
            (fun k X => Continuum.cutoff A (External.Lclt.scaledSite R (X k)) * F k X)| ≤ ε := by
  obtain ⟨A₀, hA₀4, hA₀⟩ := exists_walk_cutoff_error_of_annulus_bound d hd p hK hT hε
  refine ⟨A₀, hA₀4, ?_⟩
  intro A hA R hR x ρ hρ hxρ hρA m hm hmT F hmeasF hV hbddF hbddG hF hχF
  refine abs_stoppingSup_sub_cutoffSup_le x m R A F ε hbddF hbddG hF hχF ?_
  intro τ hτ hτm
  exact hA₀ A hA R hR x ρ hρ hxρ hρA m hm hmT τ hτm F
    (fun j => measurableSet_reach_stopped R (2 ^ j * A) hτ hτm)
    (fun X j hj => hV τ hτm X j hj)
    (integrable_cutoff_error_of_integrable x R A hτ hτm F (hmeasF τ hτ hτm) (hF τ hτ hτm))


end Sandpile
