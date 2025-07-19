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

theorem List.mem_of_map_mem_of_injective {α β} {f : α → β} {a : α} {b : β} {as : List α}
 (h_inj : Function.Injective f) (hb : b ∈ List.map f as) (eq : f a = b) : a ∈ as
  :=  by
  induction as with
  | nil => simp at hb
  | cons x xs ih =>
    simp only [List.map_cons] at hb
    by_cases h : f x = b
    · simp
      rw [← h] at eq
      apply h_inj at eq
      left
      exact eq
    · simp only [List.mem_cons, List.mem_map] at hb
      obtain hb | hb := hb
      · symm at hb
        contradiction
      · simp only [List.mem_cons]
        grind only [= List.mem_map, → List.eq_nil_of_map_eq_nil]

theorem nodup_injective_map {α β} {f : α → β} {l : List α} (h_nodup : l.Nodup) :
  Function.Injective f -> (List.map f l).Nodup := by
  intro h_inj
  induction l with
  | nil => grind only [List.map_nil, List.nodup_nil]
  | cons a as ih =>
    unfold List.map
    unfold List.Nodup at h_nodup
    rw [List.pairwise_cons] at h_nodup
    unfold List.Nodup
    rw [List.pairwise_cons]
    constructor
    · intro b
      intro hb
      have uneq := h_nodup.left
      contrapose! uneq
      use a
      constructor
      · exact List.mem_of_map_mem_of_injective h_inj hb uneq
      · rfl
    · unfold List.Nodup at ih
      apply ih
      exact h_nodup.right

theorem zipIdxFn_le_of_mem {α} {xs : List α} {n : Nat} (h_len : m = xs.length) (x2 : α) (ind : Fin (m + n)) :
  (x2, ind) ∈ xs.zipIdxFin h_len n → n ≤ ↑ind := by
  induction xs generalizing n m with
  | nil =>
    unfold List.zipIdxFin
    simp
  | cons x xs ih =>
    unfold List.zipIdxFin
    simp
    intro h_mem
    obtain h_mem | h_mem := h_mem
    · rw [h_mem.right]
    · obtain ⟨ a, k, rest1, ha_x2, hk_ind ⟩ := h_mem
      rw [ha_x2] at rest1
      have ih2 := @ih (xs.length) (n + 1) (by rfl) k rest1
      rw [← hk_ind]
      simp
      trans n + 1
      · apply Nat.le_add_right
      · exact ih2

set_option pp.proofs true

theorem zipIdxFin_nodup {α} {n m : Nat} (l : List α) (h_len : m = l.length) :
  (List.map Prod.snd (l.zipIdxFin h_len n)).Nodup := by
  induction l generalizing n m with
  | nil => grind only [= List.singleton_sublist, List.length_cons, List.contains_map, usr
      List.length_filter_le, = List.cons_sublist_cons, List.Sublist.filter, List.filter_nil,
      List.nodup_nil, = List.contains_append, usr List.sublist_append_right, usr List.map_subset, usr
      List.Sublist.length_le, List.contains_cons, = List.sublist_filter_iff, List.pairwise_singleton,
      =_ List.countP_eq_length_filter, = List.nodup_iff_count, List.length_nil, List.mem_filter,
      List.length_map, = List.pairwise_filter, = List.mem_map, = List.pairwise_append,
      List.Sublist.cons, usr List.Sublist.countP_le, List.count_cons, List.Pairwise.filter, =_
      List.filter_map, List.eq_or_mem_of_mem_cons, List.map_nil, usr List.Nodup.count, usr
      List.Sublist.filter, = List.sublist_cons_iff, =_ List.contains_iff_mem, → List.Pairwise.of_cons,
      → List.Sublist.of_cons_cons, usr List.filter_subset, List.contains_eq_mem, List.Sublist.map, =
      List.nodup_cons, usr List.Sublist.count_le, = List.any_eq, List.Pairwise.map, =
      List.nodup_append, List.elem_nil, List.length_append, = List.count_append, List.Sublist.refl, =
      List.nodup_iff_pairwise_ne, usr List.count_le_length, = List.sublist_nil, List.mem_cons_of_mem,
      List.filter_cons, = List.any_append, usr List.sublist_append_left, = List.cons_sublist_iff, →
      List.Pairwise.sublist, usr List.Nodup.sublist, List.nil_sublist, = List.pairwise_pair, =
      List.pairwise_map, List.mem_cons_self, = List.filter_map, → List.Sublist.subset,
      List.filter_append, = List.count_eq_length_filter, = List.countP_eq_length_filter, =
      List.subset_def, usr List.length_pos_of_mem, → List.eq_nil_of_append_eq_nil, =
      List.countP_eq_length_filter', = List.countP_append, usr List.Sublist.map, = List.count_nil, →
      List.eq_nil_of_map_eq_nil, List.map_cons, List.map_append, List.mem_append, =
      List.sublist_map_iff, = List.pairwise_iff_forall_sublist, usr
      List.sublist_append_of_sublist_right, usr List.Sublist.eq_of_length, cases eager Prod, cases Or]
  | cons x xs ih =>
    unfold List.zipIdxFin
    simp at h_len
    simp
    constructor
    · intro x2
      intro hx2
      intro h3
      apply zipIdxFn_le_of_mem at h3
      contrapose! h3
      rw [h3, ← Nat.succ_eq_add_one]
      apply Nat.lt.base
    · sorry

--  have nodup_zipidx_ : List.Nodup (List.map Prod.snd (List.zipIdx l n)) := List.zipIdx_nodup l
--  rw [← @zipIdxFin_forget_bound α l m h_len] at nodup_zipidx_
--  simp at nodup_zipidx_
--  have h_iff := @List.nodup_map_iff (Fin (m + n)) Nat (fun u : (Fin (m + n)) => (↑u : Nat))
--  sorry


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
