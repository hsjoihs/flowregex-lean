import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Defs
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

theorem zipIdxFin_forget_bound {α} {l : List α} {m : Nat} (h_len : m = l.length) (n : Nat := 0) :
  List.map (fun ⟨ a, ⟨ i, _isLt ⟩ ⟩ => (a, i)) (l.zipIdxFin h_len n) = List.zipIdx l n := by
  induction l generalizing m n with
  | nil =>
    unfold List.zipIdxFin
    simp [List.zipIdx]
  | cons x xs ih =>
    simp
    unfold List.zipIdxFin
    simp
    simp at h_len
    have ih2 := ih (by rfl) (n + 1)
    rw [← ih2]
    congr

theorem nodup_cons {α} {a : α} {rest : List α}  :  (a :: rest).Nodup -> rest.Nodup := by
  unfold List.Nodup
  intro h_nodup
  rw [List.pairwise_cons] at h_nodup
  exact h_nodup.right

theorem nodup_cons2 {α} {β} {a : α} {rest : List α} {f : α → β} : (List.map f (a :: rest)).Nodup -> (List.map f rest).Nodup := by
  rw [List.map_cons]
  apply nodup_cons

theorem nodup_snd_preserved_by_filter {α}
  (l : List (Bool × α))
  (h_nodup_snd : List.Nodup (List.map Prod.snd l)) :
  List.Nodup (List.map Prod.snd (List.filter (fun x => x.1) l)) := by
  induction l with
  | nil => grind only [List.filter_nil, List.map_nil, = List.nodup_iff_pairwise_ne, →
    List.eq_nil_of_map_eq_nil]
  | cons pair rest ih =>
    let (b, a) := pair
    unfold List.filter List.map
    by_cases h : b
    simp [h]
    constructor
    · grind only [= List.pairwise_filter, = List.mem_map, List.Pairwise.filter,
      List.eq_or_mem_of_mem_cons, → List.Pairwise.of_cons, = List.nodup_cons, List.Pairwise.map, =
      List.nodup_iff_pairwise_ne, List.mem_cons_of_mem, = List.pairwise_map, List.mem_cons_self,
      List.map_cons, → List.eq_nil_of_map_eq_nil, = List.pairwise_iff_forall_sublist, cases eager
      Prod]
    · apply ih
      apply nodup_cons2 at h_nodup_snd
      assumption
    · rw [Bool.not_eq_true] at h
      simp [h]
      match h2 : List.filter (fun x => x.1) rest with
      | [] => simp [h2]
      | (b2, a2) :: xs =>
        simp [h2]
        grind only [List.mem_filter, = List.pairwise_filter, = List.mem_map, List.Pairwise.filter,
          List.eq_or_mem_of_mem_cons, → List.Pairwise.of_cons, = List.nodup_cons, List.Pairwise.map,
          = List.nodup_iff_pairwise_ne, List.mem_cons_of_mem, = List.pairwise_map, List.map_cons, →
          List.eq_nil_of_map_eq_nil, = List.pairwise_iff_forall_sublist, cases eager Prod]

theorem List.zipIdx_nodup {α} {n : Nat} (l : List α) : List.Nodup (List.map Prod.snd (List.zipIdx l n)) := by
  induction l generalizing n with
  | nil => simp only [List.zipIdx_nil, List.map_nil, List.nodup_nil]
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    unfold List.Nodup
    unfold List.Nodup at ih
    rw [List.pairwise_cons]
    constructor
    · grind only [List.contains_map, List.length_cons, = List.mem_zipIdx_iff_le_and_getElem?_sub,
      = List.mem_map, =_ List.contains_iff_mem, List.contains_eq_mem, = List.any_eq,
      List.Pairwise.map, = List.pairwise_map, → List.eq_nil_of_map_eq_nil, =
      List.pairwise_iff_forall_sublist, cases eager Prod]
    · exact @ih (n + 1)

theorem zipIdxFin_nodup {α} {n m : Nat} (l : List α) (h_len : m = l.length) :
  (List.map Prod.snd (l.zipIdxFin h_len n)).Nodup := by
  have nodup_zipidx_ : List.Nodup (List.map Prod.snd (List.zipIdx l n)) := List.zipIdx_nodup l
  rw [← @zipIdxFin_forget_bound α l m] at nodup_zipidx_
  · simp at nodup_zipidx_
    sorry
  · exact h_len

def BitVec.toFinsetFin {m : Nat} (bv : BitVec m) : Finset (Fin m) :=
  let list : List Bool := bv.toBoolListLE
  let length_proof : m = list.length := bv.toBoolListLE_length.symm
  let zipped : List (Bool × Fin m) := list.zipIdxFin length_proof 0
  let indices : List (Fin m) := zipped |>.filter (fun x => x.1) |>.map Prod.snd
  let nodup : List.Nodup indices := by
    unfold indices
    apply nodup_snd_preserved_by_filter
    apply @zipIdxFin_nodup Bool 0 m list length_proof
  let indices_multiset : Multiset (Fin m) := ↑indices -- coerce
  ⟨ indices_multiset, by apply nodup ⟩
