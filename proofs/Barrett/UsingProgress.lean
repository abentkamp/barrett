import Barrett.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

-- TODO: This seems to be missing from Aeneas's library
@[progress]
theorem core.slice.index.Slice.index.spec  (a : Slice U8) (s e : Usize) (hs : s ≤ e) (he : e ≤ a.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) a
      { start := s, «end» := e } ⦃ r => r.length = e.val - s.val ⦄ := sorry

-- TODO: This seems to be missing from Aeneas's library
@[progress]
theorem HShiftRight.hShiftRightI64I32.spec  (a : I64) (b : I32) (h : b < 64#i32) :
    (a >>> b : Result I64) ⦃ r => r = a.bv >>> b.bv ⦄ := sorry

-- TODO: This seems to be missing from Aeneas's library
@[progress]
theorem HShiftRight.hShiftRightI64I64.spec  (a : I64) (b : I64) (h : b < 64#i64) :
    (a >>> b : Result I64) ⦃ r => r = a.bv >>> b.bv ⦄ := sorry


namespace barrett

@[progress]
theorem barrett_reduce_spec (value : Std.I32) (i : Std.I64) :
( do
    -- let i ← lift (core.convert.num.FromI64I32.from value)
    let t ← i * BARRETT_MULTIPLIER
    let i1 ← BARRETT_R >>> 1#i32
    let t1 ← t + i1
    let quotient ← t1 >>> BARRETT_SHIFT
    let quotient1 ← lift (IScalar.cast .I32 quotient)
    let sub ← quotient1 * FIELD_MODULUS
    value - sub  : Result Std.I32) ⦃ _ => True ⦄ := by
  -- unfold barrett_reduce
  progress* <;>  bvify 64 at *
  sorry -- bv_decide

end barrett
