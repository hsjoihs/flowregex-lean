import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import FlowregexLean.Conversion

/--
Same as `List.zipIdx`, but with `Fin` indices.
-/
def zipIdxFin {α} (l : List α) {m : Nat} (h_len : m = l.length) (n : Nat := 0) : List (α × Fin (m + n)) :=
 match hl : l, n, m with
  | [], _, _ => []
  | x :: xs, _, 0 => False.elim <| by simp at h_len
  | x :: xs, n, m' + 1 =>
    let head_isLt : n < m' + 1 + n := by simp
    let h_len' : m' = xs.length := by grind
    let rest : List (α × Fin (m' + (n + 1))) := zipIdxFin xs h_len' (n + 1)
    -- Now I need to convince that  `List (α × Fin (m' + (n + 1)))` is the same thing as `List (α × Fin (m' + 1 + n))`
    let cast : Fin (m' + (n + 1)) -> Fin (m' + 1 + n) := fun ⟨ a, isLt' ⟩ =>
      let new_isLt : a < m' + 1 + n := by
        rw [← show m' + (n + 1) = m' + 1 + n from by ac_rfl]
        assumption
      ⟨ a, new_isLt ⟩
    (x, ⟨ n, head_isLt ⟩ ) :: rest.map (fun (x, i) => (x, cast i))

def BitVec.toFinsetFin {n : Nat} (bv : BitVec n) : Finset (Fin n) :=
  let list : List Bool := bv.toBoolListLE
  let length_proof : list.length = n := bv.toBoolListLE_length
  let indices : List (Fin n) := zipIdxFin list length_proof.symm
    |>.filter (fun (b, i) => b)
    |>.map (fun (_, i) => i)
  let nodup : List.Nodup indices := by sorry
  let indices_multiset : Multiset (Fin n) := ↑indices -- coerce
  ⟨ indices_multiset, by apply nodup ⟩
