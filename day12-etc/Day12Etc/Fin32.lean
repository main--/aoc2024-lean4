import Day12Etc.Theorems

structure Fin32 (n: Fin UInt32.size) where
  val: UInt32
  isLt: val.toNat < n
deriving Repr, BEq
attribute [coe] Fin32.val


namespace Fin32

instance inhabited (h: 0 < n): Inhabited (Fin32 n) where
  default := ⟨0, h⟩


def ofFin (f: Fin n) (h: n < UInt32.size): Fin32 ⟨n, h⟩ := ⟨f.val.toUInt32, by
  have f_lt_uint_max := Nat.lt_trans f.isLt h
  simp
  rw [Nat.mod_eq_of_lt f_lt_uint_max]
  exact f.isLt
⟩
def ofNat (val: Nat) (h1: val < n) (h2: n < UInt32.size): Fin32 ⟨n, h2⟩ := Fin32.ofFin ⟨val, h1⟩ h2

def toFin (f: Fin32 n): Fin n := ⟨f.val.toNat, f.isLt⟩
@[simp] def toNat (f: Fin32 n): Nat := f.val.toNat

@[inline] def tryPred (f: Fin32 n): Option (Fin32 n) :=
  if nz: 0 < f.val then
    some ⟨f.val - 1, (by
      rw [UInt32.toNat_sub_of_le _ _ nz]
      simp
      --rw [←UInt32.toNat_ofNat_of_lt n.isLt]
      --rw [←UInt32.lt_iff_toNat_lt]
      exact sub_one_still_lt f.isLt
    )⟩
  else
    none

@[inline] def trySucc (f: Fin32 n): Option (Fin32 n) :=
  let succ := f.val.toNat + 1
  if nmax: succ < n then
    some ⟨succ.toUInt32, (by
      apply UInt32.toNat_lt_of_lt
      . exact n.isLt
      . rw [UInt32.lt_iff_toNat_lt]
        rw [UInt32.toNat_ofNat_of_lt n.isLt, UInt32.toNat_ofNat_of_lt (Nat.lt_trans nmax n.isLt)]
        exact nmax
    )⟩
  else
    none

--@[simp] protected theorem eta (a : Fin n) (h : a < n) : (⟨a, h⟩ : Fin n) = a := rfl
--@[simp] theorem eta (f: Fin32 n) (h: f.val.toNat < n): (⟨f.val, h⟩) = f.val := rfl
theorem val_mk {m: UInt32} {n : Fin UInt32.size} (h : m.toNat < n) : (⟨m, h⟩ : Fin32 n).val = m := rfl
--instance finEnum: FinEnum (Fin32 n) where

end Fin32
