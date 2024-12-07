import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

structure Map where
  width: Nat
  height: Nat
  map: Vector (Vector Char width) height
deriving Repr

theorem allSome_length (l: List (Option α)): List.allSome l = some l' → l'.length = l.length := by
  intro h
  rw [List.allSome] at h
  induction l generalizing l' with
  | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq, List.nil_eq] at h; simp; exact h
  | cons head tail ih =>
    cases head with
    | none => simp only [List.mapM_cons, id_eq, Option.pure_def, Option.bind_eq_bind,
      Option.none_bind, reduceCtorEq] at h
    | some a =>
      simp only [List.mapM_cons, id_eq, Option.pure_def, Option.bind_eq_bind,
        Option.bind.eq_def] at h
      split at h
      case cons.some.h_1 => contradiction
      case cons.some.h_2 heq =>
        simp at h
        rw [<-h]
        simp
        apply ih heq
-- and after hours of proving this I realize that I could just use the height of the final list instead of proving that the length doesn't change ...

def parseInput (s: String): Option Map :=
  let lines := (s.splitOn "\n").map (List.toArray ∘ String.toList)
  let height := lines.length
  if nonempty: height = 0
  then none
  else
    let width := lines[0].size
    let map := lines.map (fun s => if checkw: s.size = width then some (Vector.mk s checkw) else none)
    have map_length: map.length = height := List.length_map lines _
    let as := map.allSome
    if isSome: as.isSome then
      some { width, height, map := Vector.mk (as.get isSome).toArray (by simp [<-map_length, allSome_length map]) }
    else none

def exampleInput := "....#.....
.........#
..........
..#.......
.......#..
..........
.#..^.....
........#.
#.........
......#..."

def exampleMap := parseInput exampleInput
#guard exampleMap.isSome

inductive Orientation where
| up
| down
| left
| right
deriving Repr, BEq

abbrev Coords (m: Map) := Fin m.height × Fin m.width

def enumFin (l: Vector α n): List (Fin l.size × α) := (List.finRange l.size).zip l.toList

def findStart (m: Map): Option (Coords m × Orientation) :=
  let res := (enumFin m.map).findSome? (fun (i, row) =>
    let caretPos := row.indexOf? '^'
    caretPos.map (Fin.cast m.map.size_toArray i, ·)
  )
  res.map (fun r => (r, Orientation.up))

#guard (findStart { width := 1, height := 1, map := Vector.singleton (Vector.singleton '^') }).isSome
#guard (findStart { width := 1, height := 1, map := Vector.singleton (Vector.singleton ' ') }).isNone

-- for some weird reason Option.bind doesn't work here and so I need a helper function for this unit test
def checkParseAndFindStart (s: String): Bool := match parseInput s with
| none => false
| some x => (findStart x).isSome
#guard checkParseAndFindStart exampleInput

structure MapWalk where
  map: Map
  -- reaching the same turning point in the same orientation a second time would lead to an infinite loop
  -- preventing this is desirable anyways, but because this is lean4, we even have to prove it!
  turningPoints: List (Coords map × Orientation)
  visited: Vector (Vector Bool map.width) map.height

--def x := Fin.subNat 42 44

--#eval ((Fin.mk 42 (by simp)): Fin 100).pred

def Coords.next (c: Coords m) (o: Orientation): Option (Coords m) :=
  if nontrivial: m.width > 0 ∧ m.height > 0 then
    match (c, o) with
    | ((x, y), Orientation.up) =>
      if nonzero: x.castSucc = (Fin.mk 0 (by simp [nontrivial])) then none
      else
        some (x.castSucc.pred nonzero, y)
    | ((x, y), Orientation.down) =>
      if notmax: x < (m.height - 1) then
      let smol: Fin (m.height - 1) := x.castLT notmax
      some (smol.succ.cast (by
        rw [Nat.sub_add_cancel]
        refine Nat.succ_le_of_lt ?_
        simp [nontrivial]
      ), y)
      else none
    | ((x, y), Orientation.left) =>
      if nonzero: y.castSucc = (Fin.mk 0 (by simp [nontrivial])) then none
      else
        some (x, y.castSucc.pred nonzero)
    | ((x, y), Orientation.right) =>
      if notmax: y < (m.width - 1) then
      let smol: Fin (m.width - 1) := y.castLT notmax
      some (x, smol.succ.cast (by
        rw [Nat.sub_add_cancel]
        refine Nat.succ_le_of_lt ?_
        simp [nontrivial]
      ))
      else none
  else none

abbrev Visited (map: Map) := Vector Bool (map.width * map.height)
theorem Visited.validIndex (map: Map) (x: Fin map.height) (y: Fin map.width): (x * map.width + y) < (map.width * map.height) :=
  by
    have nontrivialh: 1 ≤ map.height := by
      by_cases sw: 1 ≤ map.height
      . exact sw
      . simp at sw
        rw [sw] at x
        exact x.elim0
    have foo: (map.height - 1) + 1 = map.height := Nat.sub_add_cancel nontrivialh
    rw (config := { occs := .pos [2] }) [foo.symm]
    rw [Nat.left_distrib]
    simp
    rw [←Nat.add_one_le_iff]
    rw [Nat.add_assoc]
    apply Nat.add_le_add
    . rw [Nat.mul_comm]
      apply Nat.mul_le_mul_left
      refine Nat.le_sub_one_of_lt ?_
      simp
    . refine Nat.succ_le_of_lt ?_
      simp
def Visited.markVisited (v: Visited map) (c: Coords map): Visited map :=
  let (x, y) := c
  v.set (x * map.width + y) true (Visited.validIndex map x y)
def Visited.isVisited (v: Visited map) (c: Coords map): Bool :=
  let (x, y) := c
  v.get (Fin.mk (x * map.width + y) (Visited.validIndex map x y))
def Visited.count (v: Visited map): Nat := (v.toList.filter (·)).count true
def Visited.mk: Visited map := Vector.mkVector (map.width * map.height) false

inductive WalkOutcome (map: Map) where
| exited (visited: Visited map)
| needTurn (visited: Visited map) (pos: Coords map)

def Orientation.turnRight: Orientation -> Orientation
| up => right
| right => down
| down => left
| left => up

def Map.isBlocked (map: Map) (c: Coords map): Bool := map.map[c.fst][c.snd] = '#'

def remainingSizeInDirection (map: Map) (c: Coords map) (or: Orientation): Nat :=
  let (x, y) := c
  match or with
  | Orientation.up => x
  | Orientation.down => map.height - x
  | Orientation.left => y
  | Orientation.right => map.width - y

def asd :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h
def sdf := asd.elim (fun w => (fun hw: 0 < w => show ∃ x, 0 < x from (Exists.intro w hw)))

def walkUntilObstacle (map: Map) (visited: Visited map) (pos: Coords map) (or: Orientation): WalkOutcome map :=
  match hnp: pos.next or with
  | none => WalkOutcome.exited visited
  | some nextPos =>
    if map.isBlocked nextPos then
      WalkOutcome.needTurn visited pos
    else
      have term: remainingSizeInDirection map nextPos or < remainingSizeInDirection map pos or := by
        simp [remainingSizeInDirection]
        unfold Coords.next at hnp
        cases or with
        | up =>
          simp at hnp
          exact hnp.right.elim (fun w => (fun hw => show nextPos.fst < pos.fst from (by
            rw [←hw, Lean.Omega.Prod.fst_mk]
            simp [Fin.castSucc, Fin.pred, Fin.castAdd, Fin.subNat, Fin.lt_def]
            simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at w
            rw [Fin.mk.inj_iff] at w
            apply Nat.sub_one_lt
            apply w
          )))
        | left =>
          simp at hnp
          exact hnp.right.elim (fun w => (fun hw => show nextPos.snd < pos.snd from (by
            rw [←hw, Lean.Omega.Prod.fst_mk]
            simp [Fin.castSucc, Fin.pred, Fin.castAdd, Fin.subNat, Fin.lt_def]
            simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at w
            rw [Fin.mk.inj_iff] at w
            apply Nat.sub_one_lt
            apply w
          )))
        | down =>
          simp at hnp
          apply Nat.sub_lt_sub_left
          . exact pos.fst.is_lt
          . exact hnp.elim (fun w => (fun hw => (hw.elim (fun v => (fun hv => show pos.fst < nextPos.fst from (by
            simp [←hv, Lean.Omega.Prod.fst_mk, Fin.cast, Fin.lt_def]
          ))))))
        | right =>
          simp at hnp
          apply Nat.sub_lt_sub_left
          . exact pos.snd.is_lt
          . exact hnp.elim (fun w => (fun hw => (hw.elim (fun v => (fun hv => show pos.snd < nextPos.snd from (by
            simp [←hv, Lean.Omega.Prod.fst_mk, Fin.cast, Fin.lt_def]
          ))))))
      walkUntilObstacle map (visited.markVisited nextPos) nextPos or
termination_by remainingSizeInDirection map pos or

instance : LawfulBEq (Coords map) := inferInstance
instance : LawfulBEq Orientation where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | contradiction
  rfl {a} := by cases a <;> decide
instance : LawfulBEq (Coords map × Orientation) := inferInstance

theorem MaxFinList (l: List (Fin n)) (hnd: List.Nodup l): l.length ≤ n := le_of_le_of_eq (List.Nodup.length_le_card hnd) (Fintype.card_fin n)
instance : Fintype (Fin n × Fin m) := instFintypeProd (Fin n) (Fin m)

instance Orientation.fintype : Fintype Orientation where
  elems := ⟨{ Orientation.up, Orientation.down, Orientation.left, Orientation.right }, by simp⟩
  complete := fun x => by cases x <;> simp

theorem MaxTwoFinList (l: List (Fin n × Fin m)) (hnd: List.Nodup l): l.length ≤ n * m := le_of_le_of_eq (List.Nodup.length_le_card hnd) (by
  rw [Fintype.card_prod (Fin n) (Fin m), Fintype.card_fin n, Fintype.card_fin m]
)

theorem MaxOrientation (l: List Orientation) (hnd: List.Nodup l): l.length ≤ 4 := le_of_le_of_eq (List.Nodup.length_le_card hnd) (by
  simp [Fintype.card, Finset.univ, Fintype.elems]
)

theorem MaxTurningPoints (l: List (Coords map × Orientation)) (tpu: List.Nodup l): l.length ≤ map.height * map.width * 4 := le_of_le_of_eq (List.Nodup.length_le_card tpu) (by
  rw [Fintype.card_prod (Coords map) Orientation, Fintype.card_prod (Fin map.height) (Fin map.width), Fintype.card_fin map.height, Fintype.card_fin map.width]
  simp [Fintype.card, Finset.univ, Fintype.elems]
)

def findVisitedPositions.loop (map: Map) (turningPoints: List (Coords map × Orientation)) (tpu: List.Nodup turningPoints) (visited: Visited map) (pos: Coords map) (or: Orientation): Option (Visited map) :=
  let turningPoint := (pos, or)
  if notcontains: turningPoints.contains turningPoint then
    none
  else
    let turningPoints := (pos, or)::turningPoints
    have tpu': List.Nodup turningPoints := (by
      simp [turningPoints, tpu, notcontains]
      rw [<-List.contains_iff_mem]
      exact notcontains
    )
    match walkUntilObstacle map visited pos or with
    | WalkOutcome.exited v => some v
    | WalkOutcome.needTurn v p => findVisitedPositions.loop map turningPoints tpu' v p or.turnRight
termination_by (map.height * map.width * 4) - turningPoints.length
decreasing_by
  apply Nat.sub_lt_sub_left
  . exact MaxTurningPoints turningPoints tpu'
  . simp

def findVisitedPositions (map: Map): Option (Visited map) :=
  (findStart map).bind (fun (sp, so) =>
    findVisitedPositions.loop map [] List.nodup_nil (Visited.mk.markVisited sp) sp so
  )

def countVisited (map: Map): Option Nat :=
  (findVisitedPositions map).map Visited.count

#guard some 41 = exampleMap.bind countVisited

def putObstruction (map: Map) (c: Coords map): Map :=
  let (x,y) := c
  { map with map := map.map.set x ((map.map.get x).set y '#') }

def allCoords (map: Map): List (Coords map) := (List.finRange map.height).product (List.finRange map.width)

def Map.mayObstacle (map: Map) (c: Coords map): Bool := map.map[c.fst][c.snd] = '.'

def part2 (map: Map): Option Nat :=
  (findVisitedPositions map).map (fun visited =>
    ((allCoords map).filter (fun c =>
      (visited.isVisited c) ∧ (map.mayObstacle c) ∧ (findVisitedPositions (putObstruction map c)).isNone
    )).length
  )

#guard some 6 = exampleMap.bind part2

def main (args: List String) : IO Unit := do
  let file ← IO.FS.readFile "input.txt"
  match parseInput file with
  | none => IO.println "Invalid input"
  | some map =>
    if args[0]? = "2" then
      let result := part2 map
      IO.println s!"Result: {result}"
    else
      let result := countVisited map
      IO.println s!"Result: {result}"
