import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Lattice.Basic
import FlowregexLean.Conversion

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

def BitVec.toFinsetFin {m : Nat} (bv : BitVec m) : Finset (Fin m) :=
  let list : List Bool := bv.toBoolListLE
  let length_proof : m = list.length := bv.toBoolListLE_length.symm
  let zipped : List (Bool × Fin m) := list.zipIdxFin length_proof 0
  let indices : List (Fin m) := zipped |>.filter (fun x => x.1) |>.map Prod.snd
  Finset.filter (fun i => i ∈ indices) Finset.univ
