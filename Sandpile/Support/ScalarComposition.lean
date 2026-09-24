/-
Positive third-derivative envelopes for scalar compositions of smooth
bottlenecks, preserving the total derivative and stability bounds.
-/
import Sandpile.Support.PositiveJet

open LatticeProb

open scoped BigOperators

noncomputable section

namespace Sandpile

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma coordPartial_scalar_comp {ψ : ℝ → ℝ} {f : (V → ℝ) → ℝ}
    (hψ : Differentiable ℝ ψ) (hf : Differentiable ℝ f) (i : V) (F : V → ℝ) :
    coordPartial (fun x => ψ (f x)) i F = deriv ψ (f F) * coordPartial f i F := by
  have h := (hψ (f F)).hasDerivAt.comp_hasFDerivAt F (hf F).hasFDerivAt
  unfold coordPartial
  change (fderiv ℝ (ψ ∘ f) F) (Pi.single i 1) = _
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul]

lemma coordPartial_scalar_comp_two {ψ : ℝ → ℝ} {f : (V → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : V) (F : V → ℝ) :
    coordPartial (coordPartial (fun x => ψ (f x)) i) j F =
      deriv ψ (f F) * coordPartial (coordPartial f i) j F +
      deriv (deriv ψ) (f F) * coordPartial f i F * coordPartial f j F := by
  have hψd : ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have he : coordPartial (fun x => ψ (f x)) i = fun x => deriv ψ (f x) * coordPartial f i x := by
    funext x
    exact coordPartial_scalar_comp (hψ.differentiable (by simp)) (hf.differentiable (by simp)) i x
  have hψdf : Differentiable ℝ (fun x => deriv ψ (f x)) := (hψd.comp hf).differentiable (by simp)
  rw [he, coordPartial_mul hψdf
    ((contDiff_coordPartial hf i).differentiable (by simp)),
    coordPartial_scalar_comp (hψd.differentiable (by simp)) (hf.differentiable (by simp))]
  ring

lemma coordPartial_scalar_comp_three {ψ : ℝ → ℝ} {f : (V → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j k : V) (F : V → ℝ) :
    coordPartial (coordPartial (coordPartial (fun x => ψ (f x)) i) j) k F =
      deriv ψ (f F) * coordPartial (coordPartial (coordPartial f i) j) k F +
      deriv (deriv ψ) (f F) *
        (coordPartial (coordPartial f i) j F * coordPartial f k F +
         coordPartial (coordPartial f i) k F * coordPartial f j F +
         coordPartial (coordPartial f j) k F * coordPartial f i F) +
      deriv (deriv (deriv ψ)) (f F) * coordPartial f i F * coordPartial f j F * coordPartial f k F := by
  have hψd : ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hψdd : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv ψ)) := (contDiff_infty_iff_deriv.mp hψd).2
  have hd (i : V) : Differentiable ℝ (coordPartial f i) := (contDiff_coordPartial hf i).differentiable (by simp)
  have hdd (i j : V) : Differentiable ℝ (coordPartial (coordPartial f i) j) :=
    (contDiff_coordPartial (contDiff_coordPartial hf i) j).differentiable (by simp)
  have he : coordPartial (coordPartial (fun x => ψ (f x)) i) j = fun F =>
      deriv ψ (f F) * coordPartial (coordPartial f i) j F +
      deriv (deriv ψ) (f F) * coordPartial f i F * coordPartial f j F := by
    funext F
    exact coordPartial_scalar_comp_two hψ hf i j F
  have hψdf : Differentiable ℝ (fun x => deriv ψ (f x)) := (hψd.comp hf).differentiable (by simp)
  have hψddf : Differentiable ℝ (fun x => deriv (deriv ψ) (f x)) := (hψdd.comp hf).differentiable (by simp)
  have hprod : Differentiable ℝ (fun x => deriv (deriv ψ) (f x) * coordPartial f i x) := hψddf.mul (hd i)
  have hleft : Differentiable ℝ (fun x => deriv ψ (f x) * coordPartial (coordPartial f i) j x) :=
    hψdf.mul (hdd i j)
  have hright : Differentiable ℝ (fun x => deriv (deriv ψ) (f x) * coordPartial f i x * coordPartial f j x) :=
    hprod.mul (hd j)
  rw [he, coordPartial_add hleft hright]
  rw [coordPartial_mul hψdf (hdd i j), coordPartial_mul hprod (hd j), coordPartial_mul hψddf (hd i)]
  rw [coordPartial_scalar_comp (hψd.differentiable (by simp)) (hf.differentiable (by simp)),
    coordPartial_scalar_comp (hψdd.differentiable (by simp)) (hf.differentiable (by simp))]
  ring

lemma abs_mul_le_of_abs_bounds {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) ((abs_nonneg a).trans ha)

def PositiveJet.scalarThird (A : PositiveJet V) (c₁ c₂ c₃ : ℝ)
    (i j k : V) (F : V → ℝ) : ℝ :=
  c₁ * A.three i j k F +
    c₂ * (A.two i j F * A.one k F + A.two i k F * A.one j F + A.two j k F * A.one i F) +
    c₃ * A.one i F * A.one j F * A.one k F

lemma PositiveJet.Bounds.scalarThird_bound {A : PositiveJet V} {β : ℝ} {n : ℕ}
    {f : (V → ℝ) → ℝ} (hA : A.Bounds β n f)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {c₁ c₂ c₃ : ℝ}
    (h₁ : ∀ x, |deriv ψ x| ≤ c₁) (h₂ : ∀ x, |deriv (deriv ψ) x| ≤ c₂)
    (h₃ : ∀ x, |deriv (deriv (deriv ψ)) x| ≤ c₃) (i j k : V) (F : V → ℝ) :
    |coordPartial (coordPartial (coordPartial (fun x => ψ (f x)) i) j) k F| ≤
      A.scalarThird c₁ c₂ c₃ i j k F := by
  rw [coordPartial_scalar_comp_three hψ hA.smooth]
  apply (abs_add_three _ _ _).trans
  apply add_le_add
  · apply add_le_add
    · exact abs_mul_le_of_abs_bounds (h₁ _) (hA.bound_three i j k F)
    · apply abs_mul_le_of_abs_bounds (h₂ _)
      apply (abs_add_three _ _ _).trans
      exact add_le_add
        (add_le_add (abs_mul_le_of_abs_bounds (hA.bound_two i j F) (hA.bound_one k F))
          (abs_mul_le_of_abs_bounds (hA.bound_two i k F) (hA.bound_one j F)))
        (abs_mul_le_of_abs_bounds (hA.bound_two j k F) (hA.bound_one i F))
  · exact abs_mul_le_of_abs_bounds
      (abs_mul_le_of_abs_bounds (abs_mul_le_of_abs_bounds (h₃ _) (hA.bound_one i F)) (hA.bound_one j F))
      (hA.bound_one k F)

lemma PositiveJet.Bounds.scalarThird_stable {A : PositiveJet V} {β : ℝ} {n : ℕ}
    {f : (V → ℝ) → ℝ} (hA : A.Bounds β n f) {c₁ c₂ c₃ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (i j k : V) :
    ExpStable (6 * |β| * n) (A.scalarThird c₁ c₂ c₃ i j k) := by
  have hprod (i j k : V) : ExpStable (6 * |β| * n) (fun F => A.two i j F * A.one k F) := by
    convert (hA.stable_two i j).mul (hA.stable_one k) using 1
    first | rfl | ring
  have hcube : ExpStable (6 * |β| * n) (fun F => c₃ * A.one i F * A.one j F * A.one k F) := by
    convert (((hA.stable_one i).const_mul hc₃).mul (hA.stable_one j)).mul (hA.stable_one k) using 1
    first | rfl | ring
  exact (((hA.stable_three i j k).const_mul hc₁).add
    ((((hprod i j k).add (hprod i k j)).add (hprod j k i)).const_mul hc₂)).add hcube

lemma PositiveJet.Bounds.scalarThird_continuous {A : PositiveJet V} {β : ℝ} {n : ℕ}
    {f : (V → ℝ) → ℝ} (hA : A.Bounds β n f) (c₁ c₂ c₃ : ℝ) (i j k : V) :
    Continuous (A.scalarThird c₁ c₂ c₃ i j k) := by
  have h1 (i : V) := (hA.smooth_one i).continuous
  have h2 (i j : V) := (hA.smooth_two i j).continuous
  have h3 (i j k : V) := (hA.smooth_three i j k).continuous
  unfold PositiveJet.scalarThird
  fun_prop

omit [DecidableEq V] in
lemma sum_two_one_products (T : V → V → ℝ) (O : V → ℝ) :
    (∑ i, ∑ j, ∑ k, (T i j * O k + T i k * O j + T j k * O i)) =
      3 * (∑ i, ∑ j, T i j) * (∑ k, O k) := by
  have h1 : (∑ i, ∑ j, ∑ k, T i j * O k) = (∑ i, ∑ j, T i j) * (∑ k, O k) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have h2 : (∑ i, ∑ j, ∑ k, T i k * O j) = (∑ i, ∑ j, T i j) * (∑ k, O k) := by
    calc
      _ = ∑ i, ∑ k, ∑ j, T i k * O j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := h1
  have h3 : (∑ i, ∑ j, ∑ k, T j k * O i) = (∑ i, ∑ j, T i j) * (∑ k, O k) := by
    calc
      _ = ∑ j, ∑ k, ∑ i, T j k * O i := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      _ = _ := h1
  simp only [Finset.sum_add_distrib]
  rw [h1, h2, h3]
  ring

omit [DecidableEq V] in
lemma PositiveJet.sum_scalarThird (A : PositiveJet V) (c₁ c₂ c₃ : ℝ) (F : V → ℝ) :
    (∑ i, ∑ j, ∑ k, A.scalarThird c₁ c₂ c₃ i j k F) =
      c₁ * (∑ i, ∑ j, ∑ k, A.three i j k F) +
      c₂ * (3 * (∑ i, ∑ j, A.two i j F) * (∑ k, A.one k F)) +
      c₃ * (∑ i, A.one i F) ^ 3 := by
  have hcub : (∑ i, ∑ j, ∑ k, A.one i F * A.one j F * A.one k F) = (∑ i, A.one i F) ^ 3 := by
    calc
      _ = ((∑ i, A.one i F) * (∑ j, A.one j F)) * (∑ k, A.one k F) := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ = _ := by ring
  have ht (i j k : V) : A.scalarThird c₁ c₂ c₃ i j k F =
      c₁ * A.three i j k F + c₂ *
        (A.two i j F * A.one k F + A.two i k F * A.one j F + A.two j k F * A.one i F) +
      c₃ * (A.one i F * A.one j F * A.one k F) := by
    unfold PositiveJet.scalarThird
    ring
  calc
    _ = c₁ * (∑ i, ∑ j, ∑ k, A.three i j k F) +
        c₂ * (∑ i, ∑ j, ∑ k, (A.two i j F * A.one k F + A.two i k F * A.one j F + A.two j k F * A.one i F)) +
        c₃ * (∑ i, ∑ j, ∑ k, A.one i F * A.one j F * A.one k F) := by
      simp only [ht, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    _ = _ := by rw [sum_two_one_products, hcub]

lemma PositiveJet.Bounds.sum_scalarThird_le {A : PositiveJet V} {β : ℝ} {n : ℕ}
    {f : (V → ℝ) → ℝ} (hA : A.Bounds β n f) {c₁ c₂ c₃ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (F : V → ℝ) :
    (∑ i, ∑ j, ∑ k, A.scalarThird c₁ c₂ c₃ i j k F) ≤
      c₁ * (6 * β ^ 2 * (n : ℝ) ^ 2) + 3 * c₂ * (2 * |β| * n) + c₃ := by
  rw [PositiveJet.sum_scalarThird]
  have h1 : 0 ≤ ∑ i, A.one i F := Finset.sum_nonneg (fun i _ => (hA.stable_one i).nonneg F)
  have hprod : (∑ i, ∑ j, A.two i j F) * (∑ i, A.one i F) ≤ 2 * |β| * n := by
    simpa only [mul_one] using mul_le_mul (hA.sum_two F) (hA.sum_one F) h1 (by positivity : 0 ≤ 2 * |β| * (n : ℝ))
  have hcube : (∑ i, A.one i F) ^ 3 ≤ 1 := pow_le_one₀ h1 (hA.sum_one F)
  have hp := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 3)
  have hmiddle : c₂ * (3 * (∑ i, ∑ j, A.two i j F) * (∑ k, A.one k F)) ≤
      3 * c₂ * (2 * |β| * n) := by
    convert mul_le_mul_of_nonneg_left hp hc₂ using 1 <;> first | rfl | ring
  have hlast := mul_le_mul_of_nonneg_left hcube hc₃
  simpa only [mul_one] using add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left (hA.sum_three F) hc₁) hmiddle) hlast

end Sandpile
