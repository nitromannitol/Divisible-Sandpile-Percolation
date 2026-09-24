import Sandpile.Support.MeanAKolmogorov

open MeasureTheory

namespace Sandpile.Support

/-- **Moments pass from a process to a modification of it.**  If `F` equals `G`
almost surely and `H` equals `K` almost surely, the `p`-th moment of the
increment `F - H` is that of `G - K`. -/
theorem integral_abs_sub_rpow_eq_of_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {p : ℝ} (_hp : 0 ≤ p) (F G H K : Ω → ℝ)
    (h1 : F =ᵐ[P] G) (h2 : H =ᵐ[P] K)
    (hint : Integrable (fun ω => |G ω - K ω| ^ p) P) :
    Integrable (fun ω => |F ω - H ω| ^ p) P ∧
      ∫ ω, |F ω - H ω| ^ p ∂P = ∫ ω, |G ω - K ω| ^ p ∂P := by
  have h : (fun ω => |F ω - H ω| ^ p) =ᵐ[P] fun ω => |G ω - K ω| ^ p := by
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1, hω2]
  exact ⟨hint.congr h.symm, integral_congr_ae h⟩

end Sandpile.Support