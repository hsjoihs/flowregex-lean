import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import FlowregexLean.Conversion

/--
Same as `List.zipIdx`, but with `Fin` indices.
-/
def zipIdxFin {α} (l : List α) {m : Nat} (h_len : m = l.length) (n : Nat := 0) : List (α × Fin (m + n)) :=
 match hl : l, n with
  | [], _=> []
  | x :: xs, n =>
    let m' := xs.length
    let h_m : m = m' + 1 := by simp at h_len; grind only
    let head_isLt : n < m + n := by simp [h_m]
    let h_len' : m' = xs.length := by grind
    let rest : List (α × Fin (m' + (n + 1))) := zipIdxFin xs h_len' (n + 1)
    -- Now I need to convince that  `List (α × Fin (m' + (n + 1)))` is the same thing as `List (α × Fin (m' + 1 + n))`
    let cast : Fin (m' + (n + 1)) -> Fin (m + n) := fun ⟨ a, isLt' ⟩ =>
      let new_isLt : a < m + n := by
        rw [h_m, show m' + 1 + n = m' + (n + 1) from by ac_rfl]
        assumption
      ⟨ a, new_isLt ⟩
    (x, ⟨ n, head_isLt ⟩ ) :: rest.map (fun (x, i) => (x, cast i))

theorem zipIdxFin_forget_bound {α} {l : List α} {m : Nat} (h_len : m = l.length) (n : Nat := 0) :
  List.map (fun ⟨ a, ⟨ i, isLt ⟩ ⟩ => (a, i)) (zipIdxFin l h_len n) = List.zipIdx l n := by
  induction l generalizing m n with
  | nil =>
    unfold zipIdxFin
    simp [List.zipIdx]
  | cons x xs ih =>
    simp
    unfold zipIdxFin
    simp
    simp at h_len
    match m with
    | 0 => simp at h_len -- contradiction
    | m' + 1 =>
      simp at h_len
      have ih2 := ih h_len (n + 1)
      rw [← ih2]
      congr
      · exact h_len.symm
      · sorry
      · exact h_len.symm
      · sorry

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

theorem zipped_indices_nodup {α} {n : Nat} (l : List α) (h_len : n = l.length) :
  (List.map Prod.snd <| zipIdxFin l h_len).Nodup := by
  induction l with
  | nil =>
    unfold zipIdxFin
    grind only [List.nodup_nil, = List.nodup_iff_count, List.length_nil, usr List.Nodup.count, List.map_nil, =
    List.nodup_iff_pairwise_ne, usr List.count_le_length, = List.pairwise_map, = List.count_eq_length_filter, =
    List.count_nil, → List.eq_nil_of_map_eq_nil, = List.pairwise_iff_forall_sublist]
  | cons b rest ih =>
    simp at h_len
    sorry


def BitVec.toFinsetFin {n : Nat} (bv : BitVec n) : Finset (Fin n) :=
  let list : List Bool := bv.toBoolListLE
  let length_proof : list.length = n := bv.toBoolListLE_length
  let zipped : List (Bool × Fin n) := zipIdxFin list length_proof.symm
  let indices : List (Fin n) := zipped |>.filter (fun x => x.1) |>.map Prod.snd
  let nodup : List.Nodup indices := by
    unfold indices
    apply nodup_snd_preserved_by_filter
    sorry
  let indices_multiset : Multiset (Fin n) := ↑indices -- coerce
  ⟨ indices_multiset, by apply nodup ⟩
