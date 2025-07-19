theorem rangeloop_length {n : Nat} {list : List Nat}
  : (List.range.loop n list).length = n + list.length := by
  induction n generalizing list with
  | zero => simp [List.range.loop]
  | succ n ih =>
    unfold List.range.loop
    have ih2 := @ih (n :: list)
    simp [ih]
    ac_rfl

theorem range_length {n : Nat} : (List.range n).length = n := by
  unfold List.range
  have h := @rangeloop_length n []
  simp [h]

theorem map_length {α β : Type} (f : α -> β) (l : List α) :
  (l.map f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
