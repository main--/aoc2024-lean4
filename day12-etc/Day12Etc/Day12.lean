import Day12Etc.ArrayMap

structure Region where
  area: Nat
  perimeter: Nat
deriving Repr

inductive RegionEntry where
| region (r: Region)
| merged (i: Nat)

structure Worker (h w: Nat) where
  groups: Array RegionEntry
  regionAssignments: Vector2d h w (Option Nat)
  raValid: ∀ (i: Nat), some i ∈ regionAssignments.data.toArray → i < groups.size

/-
idea: iterate in order across all fields on the map
look at all matching predecessors
- if none found => make a new region
- if one fond => grow region
- if two found => merge regions (and add myself)
-/

def Worker.make {h w: Nat}: Worker h w := {
  groups := Array.empty
  regionAssignments := ArrayMap.init none
  raValid := by simp [ArrayMap.init, Vector.mkVector, Array.mkArray_eq_toArray_replicate]
}

def exampleData: Vector (Vector Char 4) 4 := #v[
  #v['A', 'A', 'A', 'A'],
  #v['B', 'B', 'C', 'D'],
  #v['B', 'B', 'C', 'C'],
  #v['E', 'E', 'E', 'C']
]


def predecessors2d (x: Fin h) (y: Fin w): List ((Fin h) × (Fin w)) :=
  (if nz: x.val > 0 then [(⟨x.val - 1, Nat.sub_one_lt_of_le nz (Nat.le_of_lt x.isLt)⟩, y)] else [])
  ++
  (if nz: y.val > 0 then [(x, ⟨y.val - 1, Nat.sub_one_lt_of_le nz (Nat.le_of_lt y.isLt)⟩)] else [])
def predecessors (f: Fin n) (width: Nat): List (Fin n) :=
  (if width ≤ f.val then [⟨f - width, Nat.lt_of_le_of_lt (Nat.sub_le f.val width) f.isLt⟩] else [])
  ++
  (if nz: f.val > 0 ∧ (f.val % width ≠ 0) then [⟨f.val - 1, Nat.sub_one_lt_of_le nz.left (Nat.le_of_lt f.isLt)⟩] else [])
theorem preds_max_2: (predecessors x y).length < 3 := by
  simp [predecessors, List.length_append]
  repeat split ; repeat simp


-- prove equivalence of predecessors2d and predecessors to show that predecessors is correct
theorem predecessors2d_1d_eq (x: Fin h) (y: Fin w): predecessors2d x y = (predecessors (FinEnum.equiv (x, y)) w).map FinEnum.equiv.symm := by
  simp [predecessors, predecessors2d, FinEnum.equiv, betterEnumProd, betterEnumFin]
  split
  case isTrue xgz =>
    split
    case isTrue ygz =>
      simp
      split
      case isTrue ht2 =>
        simp
        split
        case isTrue =>
          simp
          apply And.intro <;> apply And.intro
          . --rw [div_sub_same (a:=(x.val * w + y.val)) (b:=w) _]
            rw [<-Nat.succ.injEq, Nat.succ_eq_add_one, Nat.succ_eq_add_one, ←Nat.div_eq_sub_div y.pos ht2, Nat.add_comm _ y, Nat.add_mul_div_right y.val x.val y.pos, Nat.div_eq_of_lt y.isLt, Nat.sub_one_add_one (Nat.ne_of_lt xgz).symm]
            simp
          . sorry
          . sorry
          . sorry
        case isFalse hyp =>
          simp at hyp
          have hyp := hyp (Or.inr ygz)
          rw [Nat.mul_add_mod', Nat.mod_eq_of_lt y.isLt] at hyp
          exact absurd hyp (Nat.ne_of_lt ygz).symm
      case isFalse hyp =>
        simp at hyp
        apply Nat.lt_of_add_right_lt at hyp
        exact absurd hyp (Nat.le_lt_asymm (Nat.le_mul_of_pos_left w xgz))
    case isFalse yz =>
      simp at yz
      simp
      split
      case isTrue a =>
        split
        case isTrue b =>
          -- bug found here: -1 should not be allowed if divisible by width
          -- (bug exists no longer)
          rw [Nat.mul_add_mod', Nat.mod_eq_of_lt y.isLt] at b
          exact absurd yz b.right
        case isFalse b =>
          simp
          apply And.intro
          . simp [yz]
            rw [←Nat.sub_one_mul, Nat.mul_div_cancel (x.val - 1) y.pos]
          . rw [Fin.ext_iff]
            simp [*]
            rw [←Nat.sub_one_mul, Nat.mul_mod_left]
      case isFalse a =>
        simp [yz]
        simp [yz] at a
        exact absurd a (Nat.le_lt_asymm (Nat.le_mul_of_pos_left w xgz))
  case isFalse xez =>
    simp at xez
    split
    case isTrue ygz =>
      simp [*]
      split
      case isTrue hyp =>
        absurd (Nat.le_lt_asymm hyp) y.isLt
        simp
      case isFalse =>
        simp
        split
        case isTrue ym0 =>
          rw [Nat.mod_eq_of_lt y.isLt] at ym0
          apply Nat.ne_of_lt at ygz
          exact absurd ym0 ygz.symm
        case isFalse ymn0 =>
          simp
          apply And.intro
          . rw [Fin.ext_iff]
            simp [*]
            exact (Nat.div_eq_of_lt _).symm
          . exact (Nat.mod_eq_of_lt (Nat.sub_lt_right_of_lt_add _ (Nat.lt_add_right 1 y.isLt))).symm
    case isFalse yz =>
      simp [*]



def Worker.work {h w: Nat} (wrk: Worker h w) (map: Vector (Vector Char w) h) :=
  ()
where
  iter (wrk: Worker h w) (x: Fin h) (y: Fin w): Worker h w :=
    let sym := (map.get x).get y
    let relevant_preds := (predecessors x y).filter (fun (x2, y2) =>
      let sym2 := (map.get x2).get y2
      sym2 = sym
    )
    have lenmax: relevant_preds.length < 3 := Nat.lt_of_le_of_lt (List.length_filter_le _ _) preds_max_2
    match rpm: relevant_preds with
    | [] =>
      -- no matching region, so we create a new one
      let regid := wrk.groups.size
      let groups := wrk.groups.push (RegionEntry.region { area := 1, perimeter := 4 })
      have gsp1: groups.size = wrk.groups.size + 1 := by
        unfold groups
        simp [List.push_toArray, Array.size_toArray, List.length_append]
      {
        regionAssignments := wrk.regionAssignments.set (x, y) regid,
        groups,
        raValid := (by
          intro i
          simp [ArrayMap.set]
          rw [<-Array.mem_toList, Array.toList_set]
          intro somei

          apply List.mem_or_eq_of_mem_set at somei
          simp at somei
          exact somei.by_cases (fun ind => by
            apply wrk.raValid at ind
            rw [gsp1]
            exact Nat.lt_add_one_of_lt ind
          ) (fun base => by
            rw [gsp1, base]
            unfold regid
            simp
          )
        )
      }
    | [pred] =>
      -- add the current tile to the existing region, only one side touches (for now)
      let existingRegion := (wrk.regionAssignments.get pred).get! -- will prove later

      {
        regionAssignments := wrk.regionAssignments.set (x, y) existingRegion
        groups := wrk.groups.modify existingRegion (fun r => { area := r.area + 1, perimeter := r.perimeter + 4 - 2 })
        raValid := sorry
      }
    | [p1, p2] =>
      let existingRegion1 := (wrk.regionAssignments.get p1).get!
      let existingRegion2 := (wrk.regionAssignments.get p2).get!
      if existingRegion1 == existingRegion2 then
        -- add the current tile to the existing region, but this time with two sides touching
        {
          regionAssignments := wrk.regionAssignments.set (x, y) existingRegion1
          groups := wrk.groups.modify existingRegion1 (fun r => { area := r.area + 1, perimeter := r.perimeter + 4 - 4 })
          raValid := sorry
        }
      else
        -- the current tile merges two regions that were separate before
        sorry
    | x1::x2::x3::xs =>
      have lenmin: relevant_preds.length ≥ 3 := (by simp [rpm])
      absurd lenmin (by
        rw [<-rpm] at lenmax
        simp
        exact lenmax
      )
    /-
    if let [] := relevant_preds then
      sorry
    else if let not1: [pred] := relevant_preds then
      sorry
    else if let not2: [p1, p2] := relevant_preds then
      sorry
    else
      absurd (not0 ∧ not1 ∧ not2) (by
        sorry
      )
-/
