import FlowregexLean.Conversion

inductive RE (S : Type) where
  | empty_set : RE S
  | singleton : S → RE S
  | union : RE S → RE S → RE S
  | concat : RE S → RE S → RE S
  | star : RE S → RE S
deriving Inhabited, BEq, DecidableEq

abbrev BitVecConverter (n : Nat) := BitVec n → BitVec n

def RE.to_bitvec_converter {S : Type} [DecidableEq S] [BEq S]
  {N : Nat} (str : Vector S N) (r : RE S) : BitVecConverter (N + 1) :=
  match r with
  | RE.empty_set => fun _ => BitVec.zero (N + 1)
  | RE.union r1 r2 =>
      fun bv => BitVec.or (RE.to_bitvec_converter str r1 bv) (RE.to_bitvec_converter str r2 bv)
  | RE.concat r1 r2 =>
      RE.to_bitvec_converter str r2 ∘ RE.to_bitvec_converter str r1
  | RE.singleton s =>
    -- Intuitively, we want to create a new bit vector where:
    -- new_vec[0] = 0
    -- new_vec[i + 1] = vec[i] && (str[i] == s)
    fun bv =>
      let vec := BitVec.truncate N bv
      let indicators : Vector Bool N := str.map (fun x => if x == s then true else false)
      let new_vec_before_shift : BitVec N := BitVec.and vec <| BitVec.ofBoolVecLE indicators
      let new_vec : BitVec (N + 1) := BitVec.cons false new_vec_before_shift
      new_vec
  | RE.star r =>
    let idOrOnce : BitVec (N + 1) → BitVec (N + 1) := fun bv => BitVec.or bv (RE.to_bitvec_converter str r bv)
    fun bv =>
      -- Intuitively, we want to return the following:
      -- `bv |
      --  (RE.to_bitvec_converter str r bv) |
      --  (RE.to_bitvec_converter str r (RE.to_bitvec_converter str r bv)) | ...`
      --
      -- Since `RE.to_bitvec_converter str r` distributes over `or`,
      -- we can compute this by repeatedly applying `a \mapsto a | f(a)` and finding a fixed point.
      -- where `f` is the function `RE.to_bitvec_converter str r`.

      -- The fixed point always exists, since the bit can only change from 0 to 1, and there are only finitely many bits.
      -- (in other words, this is because of the Kleene fixed-point theorem on the power set lattice)
      sorry
