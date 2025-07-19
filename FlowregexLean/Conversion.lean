def BitVec.ofBoolVecLE {n : Nat} (v : Vector Bool n) : BitVec n :=
  let ans : BitVec (v.toList.length) := BitVec.ofBoolListLE v.toList
  have h : v.toList.length = n := by simp only [Vector.length_toList]
  BitVec.cast h ans

def BitVec.toBoolListLE {n : Nat} (bv : BitVec n) : List Bool :=
  match n with
  | 0 => []
  | m + 1 =>
    match m with
    | 0 => [bv.getLsb 0]
    | k + 1 =>
    let rest : BitVec (k + 1 - 1 + 1) := bv.extractLsb (k + 1) 1
    bv.getLsb 0 :: BitVec.toBoolListLE (BitVec.cast (show k + 1 - 1 + 1 = k + 1 by simp) rest)

theorem BitVec.toBoolListLE_length {n : Nat} (bv : BitVec n) :
    (BitVec.toBoolListLE bv).length = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    unfold BitVec.toBoolListLE
    grind only [= getLsb_eq_getElem, List.length_cons, = cast_eq, List.length_nil, =
      Fin.getElem_fin]
