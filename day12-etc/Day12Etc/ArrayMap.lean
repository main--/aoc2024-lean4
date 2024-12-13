import Mathlib


structure ArrayMap (α: Type) (β: Type) [fea: FinEnum α] where
  data: Vector β fea.card

namespace ArrayMap
variable {α: Type} {β: Type} [fea: FinEnum α]
def init (init: β): ArrayMap α β := { data := Vector.mkVector fea.card init }
@[inline] def get (map: ArrayMap α β) (key: α) := map.data.get (fea.equiv key)
@[inline] def set (map: ArrayMap α β) (key: α) (value: β): ArrayMap α β := ⟨map.data.set (fea.equiv key) value⟩
def update (map: ArrayMap α β) (key: α) (update: β -> β): ArrayMap α β :=
  let index := fea.equiv key
  let newval := update (map.data.get index)
  ⟨map.data.set index newval⟩
def iter (map: ArrayMap α β): List (α × β) :=
  let keys := fea.toList
  keys.map (fun k => (k, map.get k))
-- i am very lazy so just using hashmap's repr
instance [Hashable α] [Repr α] [Repr β] : Repr (ArrayMap α β) where
  reprPrec am := instReprList.reprPrec am.iter
  --reprPrec am := Std.HashMap.instRepr.reprPrec (Std.HashMap.ofList am.iter)
-- end library code from day8
end ArrayMap


-- so uhm
-- turns out that the stdlib instances for FinEnum (Fn n) and FinEnum (Prod a b) are defined using FinEnum.ofList
-- which means that every single time we use FinEnum.equiv, we would end up creating a list of all possible values,
-- deduplicate the list, and then iterate it to look for the right value
-- this turns out to be VERY slow. pikachu.jpg
-- I accidentally O(n**10) or something
instance betterEnumFin: FinEnum (Fin n) where
  card := n
  equiv := {
    toFun := id
    invFun := id
    left_inv := id_eq
    right_inv := id_eq
  }

theorem Nat.ediv_lt_of_lt_mul {a b c : Nat} (h1: 0 < c) (h2: a < b * c): a / c < b :=
  (Nat.div_lt_div_of_lt_of_dvd (Nat.dvd_mul_left c b) h2).trans_eq (Nat.mul_div_cancel b h1)


theorem div_elim_insignificant_summand {a b c: Nat} (hb0: 0 < b) (hcb: c < b) : (a * b + c) / b = a := by
  rw [Nat.add_div hb0, Nat.div_eq_of_lt hcb, Nat.mul_div_cancel a hb0]
  simp
  exact Nat.mod_lt c hb0

instance betterEnumProd α β [fea: FinEnum α] [feb: FinEnum β]: FinEnum (α × β) where
  card := fea.card * feb.card
  equiv := {
    toFun prod :=
      --let (a, b) := prod.map fea.equiv feb.equiv
      let (a, b) := (fea.equiv prod.fst, feb.equiv prod.snd)
      ⟨a.val * feb.card + b.val, by
        have h3: (FinEnum.card α) * (FinEnum.card β) = (FinEnum.card α).pred * (FinEnum.card β) + (FinEnum.card β) := by
          convert (Nat.succ_mul (FinEnum.card α).pred (FinEnum.card β))
          exact (Nat.succ_pred (Nat.ne_of_lt a.pos).symm).symm
        rw [h3]
        convert Nat.lt_of_add_one_le _
        rw [Nat.add_assoc]
        exact Nat.add_le_add (Nat.mul_le_mul_right (FinEnum.card β) (Nat.le_sub_one_of_lt a.isLt)) (Nat.add_one_le_of_lt b.isLt)
      ⟩
    invFun f :=
      let ia := f.val / feb.card
      let ib := f.val % feb.card
      (
        fea.equiv.symm ⟨ia, Nat.ediv_lt_of_lt_mul (Nat.pos_of_mul_pos_left f.pos) f.isLt⟩,
        feb.equiv.symm ⟨ib, Nat.mod_lt f.val (LT.lt.gt (Nat.pos_of_mul_pos_left f.pos))⟩
      )
    left_inv x := by
      simp
      have rul := Nat.mul_add_mod_of_lt (a:=(fea.equiv x.fst).val) (b := feb.card) (c := (feb.equiv x.snd).val) (feb.equiv x.snd).isLt
      rw [Prod.eq_iff_fst_eq_snd_eq]
      apply And.intro
      case left =>
        simp [div_elim_insignificant_summand (a:=(fea.equiv x.fst).val) (feb.equiv x.snd).pos (feb.equiv x.snd).isLt]
      case right =>
        simp [rul]
    right_inv x := by simp [Nat.div_add_mod']
  }


abbrev Vector2d h w β := ArrayMap ((Fin h) × (Fin w)) β
