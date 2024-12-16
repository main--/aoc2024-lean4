import Day12Etc.ArrayMap

namespace Day12

structure Region where
  area: Nat
  perimeter: Nat
deriving Repr

inductive RegionEntry where
| region (r: Region)
| merged (i: Nat)
deriving Repr

structure Worker (h w: Nat) where
  iteration: Fin (w * h + 1)
  groups: Array RegionEntry
  regionAssignments: Vector Nat iteration
  raValid: ∀ (i: Nat), i ∈ regionAssignments.toArray → i < groups.size
  mergedGroupsValid: ∀ (i j: Nat), groups[i]? = some (RegionEntry.merged j) → (j < i)
deriving Repr

inductive IterResult (h w: Nat) where
| cont (w: Worker h w)
| done (groups: Array RegionEntry)

/-
idea: iterate in order across all fields on the map
look at all matching predecessors
- if none found => make a new region
- if one fond => grow region
- if two found => merge regions (and add myself)
-/

def Worker.make {h w: Nat} (h1: 0 < h) (h2: 0 < w): Worker h w := {
  iteration := ⟨0, by simp [h1, h2]⟩
  groups := #[]
  regionAssignments := #v[]
  raValid := by simp
  mergedGroupsValid := by simp
}
def Worker.resolveRegion (w: Worker h w) (reg: Fin w.groups.size): (Region × (Fin w.groups.size)) :=
  match cond: w.groups[reg.val] with
  | RegionEntry.region r => (r, reg)
  | RegionEntry.merged j =>
    have ltreg: j < reg := (by
      rw [←Option.some_inj, ←Array.getElem?_eq_getElem] at cond
      exact w.mergedGroupsValid reg j cond
    )
    w.resolveRegion ⟨j, Nat.lt_trans ltreg reg.isLt⟩

def calc_prices (groups: Array RegionEntry): List Nat :=
  groups.toList.filterMap (fun re => match re with
  | RegionEntry.merged _ => none
  | RegionEntry.region r => some (r.area * r.perimeter)
  )

def Worker.prices (wrk: Worker w h): List Nat :=
  calc_prices wrk.groups

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
def predecessors (f: Fin n) (width: Nat): List (Fin f) :=
  (if cond: 0 < width ∧ width ≤ f.val then
  have f_valid: f.val - width < f.val := (by
    apply Nat.sub_lt
    . apply Nat.lt_of_lt_of_le
      . exact cond.left
      . exact cond.right
    . exact cond.left
  )--Nat.sub_lt (Nat.lt_of_lt_of_le cond.left cond.right) cond.left
  [⟨f - width, f_valid⟩] else [])
  ++
  (if nz: f.val > 0 ∧ (f.val % width ≠ 0) then [(Fin.last (f.val - 1)).cast (Nat.sub_one_add_one (Nat.ne_of_gt nz.left))] else [])
theorem preds_max_2: (predecessors x y).length < 3 := by
  simp [predecessors, List.length_append]
  repeat split ; repeat simp

/-
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
            exact (Nat.div_eq_of_lt (sorry)).symm
          . exact (Nat.mod_eq_of_lt (Nat.sub_lt_right_of_lt_add sorry (Nat.lt_add_right 1 y.isLt))).symm
    case isFalse yz =>
      simp [*]
-/


def flattenMap (map: Vector (Vector Char w) h): Vector Char (w * h) :=
  ⟨(map.toArray.map Vector.toArray).flatten, (by
    rw [←Array.length_toList, Array.toList_flatten, List.length_flatten, Array.toList_map, List.map_map]
    conv =>
      rhs
      rw [<-Vector.length_toList map]
    induction map.toList with
    | nil => simp
    | cons x xs ih =>
      simp
      simp at ih
      rw [Nat.mul_add_one, Nat.add_comm]
      apply Nat.add_right_cancel_iff.mpr
      exact ih
      -- slowly getting the hang of this =)
  )⟩

def Worker.run_iteration {h w: Nat} (wrk: Worker h w) (map: Vector Char (w * h)) (notdone: ↑wrk.iteration < (w * h)): Worker h w :=
  let cur_iter: Fin (w*h) := ⟨wrk.iteration, notdone⟩
  let next_iter := cur_iter.succ
  let sym := map.get cur_iter
  let preFilter := predecessors cur_iter w
  let relevant_preds: List (Fin cur_iter) := preFilter.filter (fun i2 =>
    let sym2 := map.get (i2.castLE cur_iter.isLt)
    sym2 = sym
  )
  have lenmax: relevant_preds.length < 3 := Nat.lt_of_le_of_lt (List.length_filter_le _ preFilter) preds_max_2
  match rpm: relevant_preds with
  | [] =>
    -- no matching region, so we create a new one
    let regid := wrk.groups.size
    let groups := wrk.groups.push (RegionEntry.region { area := 1, perimeter := 4 })
    have gsp1: groups.size = wrk.groups.size + 1 := by
      unfold groups
      simp [List.push_toArray, Array.size_toArray, List.length_append]
    {
      iteration := next_iter,
      regionAssignments := wrk.regionAssignments.push regid,
      groups,
      raValid := (by
        intro i
        simp [ArrayMap.set]
        rw [<-Array.mem_toList]
        intro somei

        --apply List.mem_or_eq_of_mem_set at somei
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
      mergedGroupsValid := (by
        intro i j hyp
        unfold groups at hyp
        by_cases hc: i = wrk.groups.size
        .
          rw [hc, Array.getElem?_eq_some_iff] at hyp
          simp at hyp
        .
          simp [Array.getElem?_push, hc] at hyp
          exact wrk.mergedGroupsValid i j hyp
      )
    }
  | [pred] =>
    -- add the current tile to the existing region, only one side touches (for now)
    let existingRegion := wrk.regionAssignments.get pred
    let (region, regid) := wrk.resolveRegion ⟨existingRegion, wrk.raValid existingRegion (Array.getElem_mem _)⟩
    {
      iteration := next_iter,
      regionAssignments := wrk.regionAssignments.push existingRegion
      groups := wrk.groups.set regid (RegionEntry.region { area := region.area + 1, perimeter := region.perimeter + 4 - 2 })
      raValid := (by
        intro i hyp
        have ih := wrk.raValid
        rw [Array.size_set]
        rw [Vector.toArray_push, Array.mem_push] at hyp
        apply hyp.elim
        . exact ih i
        . intro iex
          --unfold Vector.get at existingRegion
          unfold existingRegion at iex
          unfold Vector.get at iex
          conv at iex =>
            rhs
            congr
            . skip
            . simp
          have idxele := Array.getElem_mem (l:=wrk.regionAssignments.toArray) (pred.isLt.trans_eq ((Vector.size_toArray wrk.regionAssignments).symm))
          rw [←iex] at idxele
          exact ih i idxele
      )
      mergedGroupsValid := (by
        intro i j hyp
        unfold groups at hyp
        rw [Array.getElem?_eq_some_iff] at hyp
        exact hyp.elim (fun ha => by
          rw [Array.getElem_set]
          split
          . simp
          . intro ismerge
            rw [Array.size_set] at ha
            rw [←Option.some_inj, ←Array.getElem?_eq_getElem] at ismerge
            exact wrk.mergedGroupsValid i j ismerge
        )
      )
    }
  | [p1, p2] =>
    let existingRegion1 := wrk.regionAssignments.get p1
    let existingRegion2 := wrk.regionAssignments.get p2
    let (region1, regid1) := wrk.resolveRegion ⟨existingRegion1, wrk.raValid existingRegion1 (Array.getElem_mem _)⟩
    let (region2, regid2) := wrk.resolveRegion ⟨existingRegion2, wrk.raValid existingRegion2 (Array.getElem_mem _)⟩
    if neq: regid2 == regid1 then
      -- add the current tile to the existing region, but this time with two sides touching
      -- region1 = region2 btw
      {
        iteration := next_iter,
        regionAssignments := wrk.regionAssignments.push existingRegion1
        groups := wrk.groups.set regid1 (RegionEntry.region { area := region1.area + 1, perimeter := region1.perimeter + 4 - 4 })
        raValid := (by
          intro i hyp
          have ih := wrk.raValid
          rw [Array.size_set]
          rw [Vector.toArray_push, Array.mem_push] at hyp
          apply hyp.elim
          . exact ih i
          . intro iex
            --unfold Vector.get at existingRegion
            unfold existingRegion1 at iex
            unfold Vector.get at iex
            conv at iex =>
              rhs
              congr
              . skip
              . simp
            have idxele := Array.getElem_mem (l:=wrk.regionAssignments.toArray) (p1.isLt.trans_eq ((Vector.size_toArray wrk.regionAssignments).symm))
            rw [←iex] at idxele
            exact ih i idxele
        )
        mergedGroupsValid := (by
          intro i j hyp
          unfold groups at hyp
          rw [Array.getElem?_eq_some_iff] at hyp
          exact hyp.elim (fun ha => by
            rw [Array.getElem_set]
            split
            . simp
            . intro ismerge
              rw [Array.size_set] at ha
              rw [←Option.some_inj, ←Array.getElem?_eq_getElem] at ismerge
              exact wrk.mergedGroupsValid i j ismerge
          )
        )
      }
    else
      -- the current tile merges two regions that were separate before
      let keepreg := min regid1 regid2
      let mergereg := max regid1 regid2
      have mergeSmaller: ↑keepreg < ↑mergereg := by
        unfold keepreg
        unfold mergereg
        simp
        simp at neq
        exact neq
      {
        iteration := next_iter,
        regionAssignments := wrk.regionAssignments.push existingRegion1
        groups := (
          wrk.groups.set keepreg (RegionEntry.region { area := region1.area + region2.area + 1, perimeter := region1.perimeter + region2.perimeter + 4 - 4 })
          ).set mergereg (RegionEntry.merged keepreg)
        raValid := (by
          intro i hyp
          have ih := wrk.raValid
          rw [Array.size_set]
          rw [Array.size_set]
          rw [Vector.toArray_push, Array.mem_push] at hyp
          apply hyp.elim
          . exact ih i
          . intro iex
            unfold existingRegion1 at iex
            unfold Vector.get at iex
            conv at iex =>
              rhs
              congr
              . skip
              . simp
            have idxele := Array.getElem_mem (l:=wrk.regionAssignments.toArray) (p1.isLt.trans_eq ((Vector.size_toArray wrk.regionAssignments).symm))
            rw [←iex] at idxele
            exact ih i idxele
        )
        mergedGroupsValid := (by
          intro i j hyp
          unfold groups at hyp
          rw [Array.getElem?_eq_some_iff] at hyp
          exact hyp.elim (fun ha => by
            rw [Array.getElem_set]
            rw [Array.getElem_set]
            split <;> try split
            . intro ismerge
              repeat rw [Array.size_set] at ha
              simp at ismerge
              rename_i mi
              rw [←mi, ←ismerge]
              exact mergeSmaller
            . simp
            . intro ismerge
              rw [Array.size_set] at ha
              rw [←Option.some_inj, ←Array.getElem?_eq_getElem] at ismerge
              exact wrk.mergedGroupsValid i j ismerge
          )
        )
      }
  | x1::x2::x3::xs =>
    have lenmin: relevant_preds.length ≥ 3 := (by simp [rpm])
    have nlenmin: ¬(relevant_preds.length ≥ 3) := (by
      rw [<-rpm] at lenmax
      simp
      exact lenmax
    )
    {
      iteration := next_iter,
      regionAssignments := absurd lenmin nlenmin,
      groups := absurd lenmin nlenmin,
      raValid := absurd lenmin nlenmin,
      mergedGroupsValid := absurd lenmin nlenmin,
    }

theorem Worker.iter_inc {w h: Nat} {map: Vector Char (w*h)} (wrk: Worker h w) (notdone: ↑wrk.iteration < (w * h)): (wrk.run_iteration map notdone).iteration.val = wrk.iteration.val + 1 := by
  simp [Worker.run_iteration]
  repeat split <;> repeat simp

def Worker.work {h w: Nat} (wrk: Worker h w) (map: Vector Char (w * h)): Worker h w :=
  if notdone: ↑wrk.iteration < (w * h) then
    (wrk.run_iteration map notdone).work map
  else
    wrk
termination_by (w * h) - wrk.iteration
decreasing_by
  rw [wrk.iter_inc]
  refine Nat.sub_lt_sub_left notdone ?_
  simp

theorem Worker.done_after_work (wrk: Worker h w): ↑(wrk.work map).iteration = w * h := by
  rw [Worker.work]
  split
  case isTrue notdone =>
    have vrec: (w * h) - (wrk.run_iteration map notdone).iteration < w * h - ↑wrk.iteration := by
      rw [wrk.iter_inc]
      refine Nat.sub_lt_sub_left notdone ?_
      simp
    exact Worker.done_after_work _
  case isFalse hyp =>
    apply Nat.ge_of_not_lt at hyp
    have le := Nat.le_of_lt_add_one wrk.iteration.isLt
    have asd := GE.ge.le hyp
    exact Nat.eq_iff_le_and_ge.mpr (And.intro le (GE.ge.le hyp))
termination_by (w * h) - wrk.iteration

def worker44: Worker 4 4 := Worker.make (by simp) (by simp)

#guard 140 = (Worker.prices (worker44.work (flattenMap exampleData))).sum

structure ParsedMap where
  width: Nat
  height: Nat
  map: Vector (Vector Char width) height

def parseInput (s: String): Option ParsedMap :=
  let lines := s.splitOn "\n"
  let height := lines.length
  if nonempty: height = 0
  then none
  else
    let width := lines[0].length
    let map: List (Option (Vector Char _)) := lines.map (fun s =>
        let s := s.toList.toArray
      if checkw: s.size = width then
        some (Vector.mk s checkw)
      else
        none
    )
    map.allSome.map (fun as =>
      let as := as.toArray
      let height := as.size
      { width, height, map := Vector.mk as rfl }
    )

theorem sub_one_still_lt (h: a < b): a - 1 < b := Nat.lt_of_le_of_lt (Nat.sub_le a 1) h
def fin_sub1 (f: Fin n): Fin n := ⟨f.val - 1, sub_one_still_lt f.isLt⟩

/-
part 2 idea:
postprocessing step
iter (frist linewise, then column-wise):
  pair of tiles, pair of tiles right above them
  for each pair:
    if same region (after resolving) AND different region than all other tiles:
      that_region.perimeter -= 1
-/
def part2 {h w: Nat} (wrk: { wrk: Worker h w // ↑wrk.iteration = w * h }) :=
  -- horizontally
  let idxsHorizontal := (List.finRange (h+1)).flatMap (fun x => (List.finRange w).map (x, ·))
  let groups := idxsHorizontal.foldl (fun groups c =>
    let (cx, cy) := c
    if ynz: cy.val = 0 then
      -- do nothing on the first column (we need a pair of tiles to work with)
      groups
    else
      let lowerPair := if xlt: cx.val < h then
        [some (cx.castLT xlt, fin_sub1 cy), some (cx.castLT xlt, cy)]
      else
        [none, none]
      let upperPair := if xnz: cx ≠ 0 then
        [some (cx.pred xnz, fin_sub1 cy), some (cx.pred xnz, cy)]
      else
        [none, none]
      let pairs := [lowerPair, upperPair]
      -- resolve into region IDs
      let pairs := pairs.map (·.map (·.map (fun pos =>
        let pos := FinEnum.equiv pos
        let ra := wrk.val.regionAssignments.get (pos.cast (by
          simp [FinEnum.card, wrk.prop]
          exact Nat.mul_comm h w
        ))
        (wrk.val.resolveRegion ⟨ra, wrk.val.raValid ra (Array.getElem_mem _)⟩).snd
      )))
      -- iterate over [(pair1, pair2), (pair2, pair1)] to reduce code duplication
      (pairs.zip pairs.reverse).foldl (fun groups (pair, otherPair) =>
        match pair with
        | [some r1, some r2] => if r1 = r2 && !otherPair.contains (some r1) then
            groups.modify r1 (fun reg => match reg with
            | RegionEntry.region reg => RegionEntry.region { reg with perimeter := reg.perimeter - 1 }
            | _ => reg
            )
          else groups
        | _ => groups
      ) groups
  ) wrk.val.groups
  -- vertically (this is copy-pasted, probably there is a good way to not duplicate the code)
  let idxsVertical := (List.finRange (w+1)).flatMap (fun y => (List.finRange h).map (·, y))
  let groups := idxsVertical.foldl (fun groups c =>
    let (cx, cy) := c
    if xnz: cx.val = 0 then
      -- do nothing on the first row (we need a pair of tiles to work with)
      groups
    else
      let lowerPair := if ylt: cy.val < w then
        [some (fin_sub1 cx, cy.castLT ylt), some (cx, cy.castLT ylt)]
      else
        [none, none]
      let upperPair := if ynz: cy ≠ 0 then
        [some (fin_sub1 cx, cy.pred ynz), some (cx, cy.pred ynz)]
      else
        [none, none]
      let pairs := [lowerPair, upperPair]
      -- resolve into region IDs
      let pairs := pairs.map (·.map (·.map (fun pos =>
        let pos := FinEnum.equiv pos
        let ra := wrk.val.regionAssignments.get (pos.cast (by
          simp [FinEnum.card, wrk.prop]
          exact Nat.mul_comm h w
        ))
        (wrk.val.resolveRegion ⟨ra, wrk.val.raValid ra (Array.getElem_mem _)⟩).snd
      )))
      -- iterate over [(pair1, pair2), (pair2, pair1)] to reduce code duplication
      (pairs.zip pairs.reverse).foldl (fun groups (pair, otherPair) =>
        match pair with
        | [some r1, some r2] => if r1 = r2 && !otherPair.contains (some r1) then
            groups.modify r1 (fun reg => match reg with
            | RegionEntry.region reg => RegionEntry.region { reg with perimeter := reg.perimeter - 1 }
            | _ => reg
            )
          else groups
        | _ => groups
      ) groups
  ) groups
  (calc_prices groups).sum

#guard 80 = (part2 ⟨(worker44.work (flattenMap exampleData)), Worker.done_after_work _⟩)

def main (p2: Bool) (_args: List String) : IO Unit := do
  let file ← IO.FS.readFile "input.txt"
  match parseInput file with
  | none => IO.println "Invalid input"
  | some { width, height, map } =>
    if nz: 0 < height ∧ 0 < width then
      let wrk := Worker.make nz.left nz.right
      let wrk := wrk.work (flattenMap map)
      if p2 then
        let result := part2 ⟨wrk, Worker.done_after_work _⟩
        IO.println s!"Result: {result}"
      else
        let result := wrk.prices.sum
        IO.println s!"Result: {result}"
    else
    IO.println "empty map"
