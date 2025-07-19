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


def rangeloop_length {n : Nat} {list : List Nat}
  : (List.range.loop n list).length = n + list.length := by
  induction n generalizing list with
  | zero => simp [List.range.loop]
  | succ n ih =>
    unfold List.range.loop
    have ih2 := @ih (n :: list)
    simp [ih]
    ac_rfl

def range_length {n : Nat} : (List.range n).length = n := by
  unfold List.range
  have h := @rangeloop_length n []
  simp [h]

def map_length {α β : Type} (f : α -> β) (l : List α) :
  (l.map f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

set_option pp.proofs true

def zipIdxFin_length {α} {l : List α} {n : Nat} {m : Nat} (h_len : m = l.length)  :
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

def BitVec.fromFinsetFin {m : Nat} (s : Finset (Fin m)) : BitVec m :=
  -- We need a list of length `m` whose values are indices that are in `Fin m`.
  -- We first create a list of length `m` by using `List.range m`,
  let h_range_len : m = (List.range m).length := (@range_length m).symm

  -- And then we zip it with `Fin m` indices.
  let range_range : List (Nat × Fin m) := (List.range m).zipIdxFin h_range_len 0

  -- Of course, the length is still `m`.
  have h_range_range_len : m = range_range.length := by
    have len1 : ((List.range m).zipIdxFin h_range_len 0).length = m := zipIdxFin_length h_range_len
    symm
    unfold range_range
    exact len1

  -- Now we transcribe the membership of `s` into a list of `Bool` values.
  let little_endian : List Bool := range_range.map (fun (_i, i) => i ∈ s)

  -- Of course, the length is still `m`.
  let length_proof : m = little_endian.length := by
    have len1 := map_length (fun (_i, i) => i ∈ s) range_range
    unfold little_endian
    simp [h_range_range_len]

  let ans : BitVec (little_endian.length) := BitVec.ofBoolListLE little_endian
  BitVec.cast length_proof.symm ans
