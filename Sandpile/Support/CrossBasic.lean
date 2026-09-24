/-
The geometry of the planar crossings of `sandpile.tex:2112-2118`:

  "For a rectangle `𝓡` in the plane, write `H_𝓡(ℓ)` for the event that
   `{𝒳_1 ≥ ℓ} ∩ 𝓡` contains a compact connected left-right crossing of `𝓡`.
   [...] For open sets, ``crosses'' means that the set contains a compact
   connected subset joining the two opposite sides."

This module is the elementary API of that predicate: it is monotone in the
crossed set, hence in the level; it is monotone in the rectangle as long as the
two faces met by the crossing are the same; and a crossing of one level set
transfers to a crossing of another whenever the level sets compare pointwise on
the rectangle.  The last of these is the deterministic step of
`sandpile.tex:2549-2556`, where a crossing of `{max_i 𝒳_{s_i} ≥ 4c}` is turned
into a crossing of `{𝒰_{Z,1}(T,·) > 5dc}`.
-/
import Sandpile.Support.ContinuumPlanar

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Frozen.FixedScaleCrossings

/-- A crossing of a larger set is implied by a crossing of a smaller one. -/
theorem crosses_mono {a b : Fin 2 → ℝ} {i : Fin 2}
    {S S' : Set (Sandpile.Continuum.Space 2)} (hSS : S ⊆ S')
    (hS : Crosses a b i S) : Crosses a b i S' := by
  obtain ⟨Γ, hsub, hcomp, hconn, hp, hq⟩ := hS
  exact ⟨Γ, hsub.trans (Set.inter_subset_inter_left _ hSS), hcomp, hconn, hp, hq⟩

/-- Lowering the level keeps a crossing. -/
theorem crosses_level_mono {a b : Fin 2 → ℝ} {i : Fin 2}
    {f : Sandpile.Continuum.Space 2 → ℝ} {l l' : ℝ} (hl : l' ≤ l)
    (hS : Crosses a b i {u | l ≤ f u}) : Crosses a b i {u | l' ≤ f u} :=
  crosses_mono (fun _ hu => le_trans hl hu) hS

/-- A crossing transfers to another set whenever membership compares on the
rectangle.  Only the points of the rectangle matter, since the crossing is
contained in it. -/
theorem crosses_of_mem_on {a b : Fin 2 → ℝ} {i : Fin 2}
    {S T : Set (Sandpile.Continuum.Space 2)}
    (h : ∀ u ∈ rectSet a b, u ∈ S → u ∈ T)
    (hS : Crosses a b i S) : Crosses a b i T := by
  obtain ⟨Γ, hsub, hcomp, hconn, hp, hq⟩ := hS
  refine ⟨Γ, ?_, hcomp, hconn, hp, hq⟩
  intro u hu
  obtain ⟨h1, h2⟩ := hsub hu
  exact ⟨h u h2 h1, h2⟩

/-- A crossing of one level set becomes a crossing of another whenever the
levels compare pointwise on the rectangle. -/
theorem crosses_of_le_on {a b : Fin 2 → ℝ} {i : Fin 2}
    {f g : Sandpile.Continuum.Space 2 → ℝ} {l l' : ℝ}
    (h : ∀ u ∈ rectSet a b, l ≤ f u → l' ≤ g u)
    (hS : Crosses a b i {u | l ≤ f u}) : Crosses a b i {u | l' ≤ g u} :=
  crosses_of_mem_on h hS

/-- A rectangle grows when its lower corner falls and its upper corner rises. -/
theorem rectSet_mono {a b a' b' : Fin 2 → ℝ} (ha : ∀ k, a k ≤ a' k) (hb : ∀ k, b' k ≤ b k) :
    rectSet a' b' ⊆ rectSet a b := by
  intro p hp k
  exact ⟨le_trans (ha k) (hp k).1, le_trans (hp k).2 (hb k)⟩

/-- A crossing of a subrectangle whose two faces in the crossing direction lie
on the faces of the larger rectangle is a crossing of the larger rectangle. -/
theorem crosses_rect_mono {a b a' b' : Fin 2 → ℝ} {i : Fin 2}
    {S : Set (Sandpile.Continuum.Space 2)}
    (hr : rectSet a' b' ⊆ rectSet a b) (hai : a' i = a i) (hbi : b' i = b i)
    (hS : Crosses a' b' i S) : Crosses a b i S := by
  obtain ⟨Γ, hsub, hcomp, hconn, ⟨p, hpΓ, hpa⟩, ⟨q, hqΓ, hqb⟩⟩ := hS
  refine ⟨Γ, ?_, hcomp, hconn, ⟨p, hpΓ, by rw [hpa, hai]⟩, ⟨q, hqΓ, by rw [hqb, hbi]⟩⟩
  intro u hu
  obtain ⟨h1, h2⟩ := hsub hu
  exact ⟨h1, hr h2⟩

/-- The deterministic step of `sandpile.tex:2549-2556`.  If `G` is within `c` of
`F` on the rectangle, if `D * G ≤ U` everywhere, and if `{F ≥ 4c}` crosses, then
`{U > H}` crosses for every `H < 3Dc`.  The paper's case is `D = 2d` and
`H = 5dc`. -/
theorem crosses_value_of_approx {a b : Fin 2 → ℝ} {i : Fin 2} {c D H : ℝ}
    (hD : 0 < D) (hH : H < 3 * D * c)
    {F G U : Sandpile.Continuum.Space 2 → ℝ}
    (hGF : ∀ u ∈ rectSet a b, F u - c ≤ G u)
    (hGU : ∀ u, D * G u ≤ U u)
    (hcross : Crosses a b i {u | 4 * c ≤ F u}) :
    Crosses a b i {u | H < U u} := by
  refine crosses_of_mem_on (fun u hu h1 => ?_) hcross
  have h1' : 4 * c ≤ F u := h1
  show H < U u
  have hG : 3 * c ≤ G u := by have := hGF u hu; linarith
  have hDG : D * (3 * c) ≤ D * G u := mul_le_mul_of_nonneg_left hG hD.le
  have hDU := hGU u
  nlinarith

/-- `ofReal c ≤ x + ofReal (c/2)` forces `ofReal (c/2) ≤ x`. -/
theorem ofReal_half_le_of_add {c : ℝ} (hc : 0 ≤ c) {x : ℝ≥0∞}
    (h : ENNReal.ofReal c ≤ x + ENNReal.ofReal (c / 2)) :
    ENNReal.ofReal (c / 2) ≤ x := by
  have hcc : c / 2 + c / 2 = c := by ring
  have hsplit : ENNReal.ofReal c = ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 2) := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith), hcc]
  rw [hsplit] at h
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp (by rwa [add_comm x] at h)

/-- Subadditivity: the outer measure of `A` is at most that of `A ∩ B` plus that
of the complement of `B`.  No measurability is needed, which is what lets the
possibly non-measurable crossing events be intersected with a good event. -/
theorem measure_le_inter_add_compl {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : Set Ω) : P A ≤ P (A ∩ B) + P Bᶜ := by
  have hsub : A ⊆ (A ∩ B) ∪ Bᶜ := by
    intro x hx
    by_cases hB : x ∈ B
    · exact Or.inl ⟨hx, hB⟩
    · exact Or.inr hB
  calc P A ≤ P ((A ∩ B) ∪ Bᶜ) := measure_mono hsub
    _ ≤ P (A ∩ B) + P Bᶜ := measure_union_le _ _

/-- A lower bound holding eventually is a lower bound for the `liminf` in `ℝ≥0∞`. -/
theorem le_liminf_ennreal {p : ℝ≥0∞} {f : ℝ → ℝ≥0∞}
    (h : ∀ᶠ R in atTop, p ≤ f R) : p ≤ Filter.liminf f atTop :=
  Filter.le_liminf_of_le (by isBoundedDefault) h


/-- A crossing of the positive set is a crossing of a level set at some positive
level: the compact connected set on which the continuous field is positive has a
positive minimum, so it lies in `{δ ≤ X}` for some `δ > 0`. -/
theorem crosses_pos_of_exists_level {X : Sandpile.Continuum.Space 2 → ℝ}
    (hX : Continuous X) {a b : Fin 2 → ℝ} {i : Fin 2}
    (h : Crosses a b i {u | 0 < X u}) :
    ∃ δ : ℝ, 0 < δ ∧ Crosses a b i {u | δ ≤ X u} := by
  obtain ⟨Γ, hsub, hcomp, hconn, hp, hq⟩ := h
  obtain ⟨u₀, hu₀, hmin⟩ := hcomp.exists_isMinOn hconn.nonempty hX.continuousOn
  refine ⟨X u₀, (hsub hu₀).1, Γ, ?_, hcomp, hconn, hp, hq⟩
  intro u hu
  exact ⟨hmin hu, (hsub hu).2⟩

end Sandpile.Support
