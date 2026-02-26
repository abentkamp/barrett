import Barrett.Funs
import Std.Tactic.Do

open Std.Do Aeneas.Std

attribute [spec] lift

@[spec]
theorem HMul.hMulI64I64.spec (a b : I64) (h : a.bv.smulOverflow b = false) :
    ⦃ ⌜ True ⌝ ⦄ (a * b) ⦃⇓ r => ⌜ r.bv = a.bv * b.bv ⌝ ⦄ :=
  sorry

@[spec]
theorem HMul.hMulI32I32.spec (a b : I32) (h : a.bv.smulOverflow b = false) :
    ⦃ ⌜ True ⌝ ⦄ (a * b) ⦃⇓ r => ⌜ r.bv = a.bv * b.bv ⌝ ⦄ :=
  sorry

@[spec]
theorem HSub.hSubI32I32.spec (a b : I32) (h : a.bv.ssubOverflow b = false) :
    ⦃ ⌜ True ⌝ ⦄ (a - b) ⦃⇓ r => ⌜ r.bv = a.bv - b.bv ⌝ ⦄ :=
  sorry

@[spec]
theorem HAdd.hAddI64I64.spec (a b : I64) (h : a.bv.saddOverflow b = false) :
    ⦃ ⌜ True ⌝ ⦄ (a + b) ⦃⇓ r => ⌜ r.bv = a.bv + b.bv ⌝ ⦄ :=
  sorry

@[spec]
theorem HShiftRight.hShiftRightI64I32.spec (a : I64) (b : I32) (hb : b.bv < 64) :
    ⦃ ⌜ True ⌝ ⦄ (a >>> b) ⦃⇓ r => ⌜ r.bv = a.bv >>> b.bv ⌝ ⦄ :=
  sorry

@[spec]
theorem HShiftRight.hShiftRightI64I64.spec (a : I64) (b : I64) (hb : b.bv < 64) :
    ⦃ ⌜ True ⌝ ⦄ (a >>> b) ⦃⇓ r => ⌜ r.bv = a.bv >>> b.bv ⌝ ⦄ :=
  sorry

@[spec]
theorem Result.ok.spec (a : I64) : ⦃ ⌜ True ⌝ ⦄ Result.ok a ⦃⇓ r => ⌜ r.bv = a.bv ⌝ ⦄ := by
  mvcgen


@[spec]
theorem Result.ok32.spec (a : I32) : ⦃ ⌜ True ⌝ ⦄ Result.ok a ⦃⇓ r => ⌜ r.bv = a.bv ⌝ ⦄ := by
  mvcgen

theorem IScalar.bv_I64ofInt : (I64.ofInt n hn).bv = BitVec.ofInt 64 n := by rfl
theorem IScalar.bv_I32ofInt : (I32.ofInt n hn).bv = BitVec.ofInt 32 n := by rfl

theorem IScalar.cast_val64 :
  @Int.cast (BitVec 64) BitVec.instIntCast
  (@IScalar.val IScalarTy.I64 n : ℤ) = n.bv := by rw [I64.Nat_cast_BitVec_val]


theorem IScalar.cast_val32 :
  @Int.cast (BitVec 32) BitVec.instIntCast
  (@IScalar.val IScalarTy.I32 n : ℤ) = n.bv := by rw [I32.Nat_cast_BitVec_val]

theorem IScalar.bv_mkI64 : (@IScalar.mk IScalarTy.I64 x).bv = x := rfl
theorem IScalar.bv_mkI32 : (@IScalar.mk IScalarTy.I32 x).bv = x := rfl

-- @[bv_normalize]
-- theorem xx :
--    IScalarTy.I64.numBits = 64 := rfl

#check IScalar.cast


def wrapper (a : I64) : BitVec 64 := a.bv
theorem xxxx (a : I64) : a.bv = wrapper a := by rfl


def wrapper32 (a : I32) : BitVec 32 := a.bv
theorem xxxx32 (a : I32) : a.bv = wrapper32 a := by rfl



open barrett

set_option trace.Meta.Tactic.bv true

theorem barrett_reduce.spec (value : I32)
    (h1 : BitVec.sle (- BARRETT_R.bv) (core.convert.num.FromI64I32.from value).bv)
    (h2 : BitVec.sle (core.convert.num.FromI64I32.from value).bv BARRETT_R.bv) :
    ⦃ ⌜ True ⌝ ⦄
    barrett_reduce value
    ⦃⇓ r => ⌜
    BitVec.slt (- FIELD_MODULUS.bv) r.bv ∧ BitVec.slt r.bv FIELD_MODULUS.bv
    ∧ r.bv.smod FIELD_MODULUS.bv = value.bv.smod FIELD_MODULUS.bv
    ⌝ ⦄ := by
  unfold barrett_reduce BARRETT_MULTIPLIER BARRETT_SHIFT FIELD_MODULUS BARRETT_R at *
  mvcgen
  all_goals try simp only [
    IScalar.bv_I64ofInt, IScalar.bv_mkI64, IScalar.bv_I32ofInt, IScalar.bv_mkI32,
    IScalar.cast_val64, IScalar.cast_val32, IScalarTy.numBits,
    core.convert.num.FromI64I32.from, IScalar.cast] at *
  all_goals try simp only [xxxx, xxxx32] at *
  · bv_decide
  · bv_decide
  · bv_decide
  · bv_decide (timeout := 1200)
