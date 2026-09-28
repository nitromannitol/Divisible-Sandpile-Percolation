import Sandpile.Support.CrossRectangleWalk
import Sandpile.Support.CrossZeroLimit

/-! # Exact planar crossing duality

Exact planar duality for closed and open level crossings.
-/

open Set Filter Topology MeasureTheory
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
namespace Sandpile.Support

/-- A crossing of the unit square transports to a rectangle by its coordinate
wise affine parametrization. -/
theorem crosses_affine_rectangle {a b : Fin 2 → ℝ} (hab : ∀ i, a i ≤ b i)
    {i : Fin 2} {S : Set (Space 2)}
    (h : Crosses ![0, 0] ![1, 1] i
      ((fun u : Space 2 => WithLp.toLp 2 (fun k => a k + (b k - a k) * u k)) ⁻¹' S)) :
    Crosses a b i S := by
  let g (u : Space 2) : Space 2 := WithLp.toLp 2 (fun k => a k + (b k - a k) * u k)
  have hg : Continuous g := by
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k => continuous_const.add
      (continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) k))
  obtain ⟨Γ, hΓ, hΓc, hΓn, ⟨x, hx, hxa⟩, ⟨y, hy, hyb⟩⟩ := h
  refine ⟨g '' Γ, ?_, hΓc.image hg, hΓn.image _ hg.continuousOn,
    ⟨g x, ⟨x, hx, rfl⟩, ?_⟩, ⟨g y, ⟨y, hy, rfl⟩, ?_⟩⟩
  · rintro z ⟨u, hu, rfl⟩
    refine ⟨(hΓ hu).1, fun k => ?_⟩
    have hu' : 0 ≤ u k ∧ u k ≤ 1 := by
      fin_cases k
      · simpa using (hΓ hu).2 0
      · simpa using (hΓ hu).2 1
    change a k ≤ a k + (b k - a k) * u k ∧ a k + (b k - a k) * u k ≤ b k
    constructor <;> nlinarith [hab k]
  · have hx0 : x i = 0 := by fin_cases i <;> simpa using hxa
    dsimp [g]
    rw [hx0]
    ring
  · have hy1 : y i = 1 := by fin_cases i <;> simpa using hyb
    dsimp [g]
    rw [hy1]
    ring

/-- Approximate planar duality in an arbitrary nondegenerate rectangle. -/
theorem continuum_rectangle_duality {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i)
    {f : Space 2 → ℝ} (hf : Continuous f) {η : ℝ} (hη : 0 < η) :
    Crosses a b 0 {u | -η ≤ f u} ∨ Crosses a b 1 {u | f u ≤ η} := by
  let g (u : Space 2) : Space 2 := WithLp.toLp 2 (fun k => a k + (b k - a k) * u k)
  have hg : Continuous g := by
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k => continuous_const.add
      (continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) k))
  rcases continuum_square_duality 1 η one_pos hη (fun u => f (g u)) (hf.comp hg) with h | h
  · exact Or.inl (crosses_affine_rectangle (fun k => (hab k).le) h)
  · exact Or.inr (crosses_affine_rectangle (fun k => (hab k).le) h)

/-- Closed superlevel crossings and opposite open sublevel crossings are
exactly complementary for a continuous field. -/
theorem not_crosses_iff_crosses_lt {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i)
    {f : Space 2 → ℝ} (hf : Continuous f) (l : ℝ) :
    (¬ Crosses a b 0 {u | l ≤ f u}) ↔ Crosses a b 1 {u | f u < l} := by
  constructor
  · intro hnot
    have hn : ∃ n : ℕ, ¬ Crosses a b 0 {u | l - 1 / ((n : ℝ) + 1) ≤ f u} := by
      by_contra h
      push Not at h
      apply hnot
      apply crosses_of_monotone_levels hf (l := fun n : ℕ => l - 1 / ((n : ℝ) + 1))
      · intro n m hnm
        exact sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hnm 1)) l
      · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub l
      · exact h
    obtain ⟨n, hn⟩ := hn
    let δ : ℝ := 1 / ((n : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    rcases continuum_rectangle_duality hab
      (hf.sub continuous_const : Continuous fun u => f u - (l - δ / 2))
      (show 0 < δ / 4 by positivity) with h | h
    · exact False.elim (hn (crosses_mono (fun u hu => by
        change -(δ / 4) ≤ f u - (l - δ / 2) at hu
        change l - δ ≤ f u
        linarith) h))
    · exact crosses_mono (fun u hu => by
        change f u - (l - δ / 2) ≤ δ / 4 at hu
        change f u < l
        linarith) h
  · intro hlt hge
    obtain ⟨u, hu, hv⟩ := rectangle_crossings_intersect hab hge hlt
    exact (not_lt_of_ge (show l ≤ f u from hu)) (show f u < l from hv)

/-- The open dual crossing event agrees almost surely with the complement of
the closed primal crossing event. -/
theorem open_dual_crossing_ae_eq_compl {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Space 2 → Ω → ℝ) {a b : Fin 2 → ℝ}
    (hab : ∀ i, a i < b i) (hc : ∀ᵐ ω ∂P, Continuous fun u => X u ω) (l : ℝ) :
    {ω | Crosses a b 1 {u | X u ω < l}} =ᵐ[P]
      {ω | Crosses a b 0 {u | l ≤ X u ω}}ᶜ := by
  filter_upwards [hc] with ω hω
  exact propext (not_crosses_iff_crosses_lt hab hω l).symm

/-- Exact duality gives the difference of crossing probabilities used by the
level-shift argument. -/
theorem crossing_probability_loss_eq_dual {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Space 2 → Ω → ℝ)
    (hm : ∀ u, Measurable (X u)) (hc : ∀ᵐ ω ∂P, Continuous fun u => X u ω)
    {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i) (l₀ l₁ : ℝ) :
    P.real {ω | Crosses a b 0 {u | l₀ ≤ X u ω}} -
        P.real {ω | Crosses a b 0 {u | l₁ ≤ X u ω}} =
      P.real {ω | Crosses a b 1 {u | X u ω < l₁}} -
        P.real {ω | Crosses a b 1 {u | X u ω < l₀}} := by
  have he (l : ℝ) : P.real {ω | Crosses a b 1 {u | X u ω < l}} =
      1 - P.real {ω | Crosses a b 0 {u | l ≤ X u ω}} := by
    exact (measureReal_congr (open_dual_crossing_ae_eq_compl P X hab hc l)).trans
      (probReal_compl_eq_one_sub₀ (nullMeasurableSet_crossing P X a b 0 hab l hm hc))
  rw [he l₀, he l₁]
  ring

end Sandpile.Support
