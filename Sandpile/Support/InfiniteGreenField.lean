import Sandpile.Basic
import Sandpile.Walk

/-!
# Infinite Gaussian Green field

The infinite Gaussian Green field of `eq:dgt4-infinite-green-field`
(`sandpile.tex:4834-4836`), in the representation fixed for this
formalization: the limit of the finite-box partial sums along the boxes, not
an unordered real `tsum`. For the Gaussian scenery of the threshold branch the
partial sums converge in `L²` and almost surely, so the limit below is the
field the paper uses; on the null set where the real limit does not exist the
value is zero, and every statement that depends on the value is stated in its
almost-sure form.
-/

open scoped Classical
open MeasureTheory Filter Set Topology

namespace Sandpile

/-- The box `box_n = {z ∈ ℤ^d : |z_i| ≤ n for all i}`. -/
def greenFieldBox (d : ℕ) (n : ℕ) : Set (Site d) :=
  {z | ∀ i : Fin d, |z i| ≤ (n : ℤ)}

/-- `greenFieldBox d n` is finite: it embeds in the finite product
`∏ i : Fin d, Icc (-n) n`, so it inherits a `Fintype` instance from that
embedding. -/
noncomputable instance greenFieldBoxFintype (d n : ℕ) : Fintype ↑(greenFieldBox d n) := by
  have h1 : greenFieldBox d n
      ⊆ Set.pi (Set.univ : Set (Fin d)) (fun _ => Set.Icc (-(n:ℤ)) (n:ℤ)) := by
    intro z hz i _
    exact abs_le.mp (hz i)
  have h2 : (Set.pi (Set.univ : Set (Fin d))
      (fun _ => Set.Icc (-(n:ℤ)) (n:ℤ))).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc (a := -(n:ℤ)) (b := (n:ℤ)))
  exact h2.subset h1 |>.fintype

/-- The finite-box partial sum `V_n(x) = ∑_{z ∈ box_n} G(x,z) ζ(z)` of
`eq:dgt4-infinite-green-field`. -/
noncomputable def infiniteGreenFieldPartial {d : ℕ} (n : ℕ)
    (ζ : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ z : greenFieldBox d n, green d x z * ζ z

/-- The infinite Green field `V_∞(x) = lim_n V_n(x)` of
`eq:dgt4-infinite-green-field`: the limit of the finite-box partial sums along
the boxes when it exists, and zero on the exceptional set where it does not.
For the Gaussian scenery the limit exists almost surely and in `L²`, so this is
the field of the paper. -/
noncomputable def infiniteGreenField {d : ℕ}
    (ζ : Site d → ℝ) (x : Site d) : ℝ :=
  if h : ∃ L : ℝ, Tendsto (fun n => infiniteGreenFieldPartial n ζ x) atTop (𝓝 L)
  then Classical.choose h
  else 0

end Sandpile