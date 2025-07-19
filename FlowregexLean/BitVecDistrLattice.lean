import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Lattice.Basic
import FlowregexLean.Conversion
import FlowregexLean.ZipIdxFin
import FlowregexLean.LengthLemmas

def BitVec.toFinsetFin {m : Nat} (bv : BitVec m) : Finset (Fin m) :=
  let list : List Bool := bv.toBoolListLE
  let length_proof : m = list.length := bv.toBoolListLE_length.symm
  let zipped : List (Bool × Fin m) := list.zipIdxFin length_proof 0
  let indices : List (Fin m) := zipped |>.filter (fun x => x.1) |>.map Prod.snd
  Finset.filter (fun i => i ∈ indices) Finset.univ

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
