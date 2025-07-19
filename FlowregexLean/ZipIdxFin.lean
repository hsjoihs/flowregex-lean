import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs

/--
Same as `List.zipIdx`, but with `Fin` indices.
-/
def List.zipIdxFin {α} (l : List α) {m : Nat} (h_len : m = l.length) (n : Nat) : List (α × Fin (m + n)) :=
 match hl : l, n with
  | [], _=> []
  | x :: xs, n =>
    let h_m : m = xs.length + 1 := by simp at h_len; assumption
    let head_isLt : n < m + n := by simp [h_m]
    let rest : List (α × Fin (xs.length + (n + 1))) := zipIdxFin xs (by rfl) (n + 1)
    -- Now I need to convince that  `List (α × Fin (xs.length + (n + 1)))` is the same thing as `List (α × Fin (xs.length + 1 + n))`
    let cast : Fin (xs.length + (n + 1)) -> Fin (m + n) := fun ⟨ a, isLt' ⟩ =>
      let new_isLt : a < m + n := by
        rw [h_m, show xs.length + 1 + n = xs.length + (n + 1) from by ac_rfl]
        assumption
      ⟨ a, new_isLt ⟩
    (x, ⟨ n, head_isLt ⟩ ) :: rest.map (fun (x, i) => (x, cast i))

theorem zipIdxFin_length {α} {l : List α} {n : Nat} {m : Nat} (h_len : m = l.length)  :
  (l.zipIdxFin h_len n).length = m := by
  induction l generalizing m n with
  | nil =>
    simp at h_len
    simp [List.zipIdxFin, h_len]
  | cons a l ih =>
    unfold List.zipIdxFin
    simp
    simp at h_len
    have ih2 := @ih (n + 1) l.length (by rfl)
    simp [ih2]
    exact h_len.symm
