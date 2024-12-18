import Batteries
import Day12Etc.Fin32
import Day12Etc.VectorExt
import Day12Etc.StringExt

namespace Day15

def exampleInput := "########
#..O.O.#
##@.O..#
#...O..#
#.#.O..#
#...O..#
#......#
########

<^^>>>vv<v>>v<<"

inductive Move where
| up
| down
| left
| right
deriving Repr

def Move.fromChar: (c: Char) -> Option Move
| '<' => some .left
| '>' => some .right
| '^' => some .up
| 'v' => some .down
| _ => none

inductive Tile where
| wall
| box
| free
deriving Repr, BEq, DecidableEq

def Tile.fromChar: (c: Char) -> Option Tile
| '#' => some .wall
| 'O' => some .box
| '.'
| '@' => some .free
| _ => none

structure Map where
  height: Fin UInt32.size
  width: Fin UInt32.size
  pos: (Fin32 height × Fin32 width)
  map: Vector (Vector Tile width) height
deriving Repr


def parseInput (s: String): Option (Map × List Move) := do
  let (map, moves) <- s.splitOnce "\n\n"
  let moves := moves.replace "\n" ""
  let moves <- (moves.toList.map Move.fromChar).allSome
  let mapLines := map.splitOn "\n"
  let (spx, spy) <- mapLines.enum.findSome? (fun (x, l) => (l.revPosOf '@').map (x, String.Pos.byteIdx ·))
  let map <- (mapLines.map (fun l => ((String.toList l).map Tile.fromChar).allSome)).allSome
  if hnz: 0 < map.length then
    let width := map[0].length
    let map <- (map.map (fun a =>
      let a := List.toArray a
      if h: a.size = width then
        some (Vector.mk a h)
      else
        none
    )).allSome
    let map := map.toArray
    let height := map.size
    if valid: (spx < height ∧ spy < width) ∧ (height < UInt32.size ∧ width < UInt32.size) then
      some ({
        height := ⟨height, valid.right.left⟩,
        width := ⟨width, valid.right.right⟩,
        map := Vector.mk map rfl,
        pos := (Fin32.ofNat spx valid.left.left valid.right.left, Fin32.ofNat spy valid.left.right valid.right.right)
      }, moves)
    else
      none
  else
    none

def exampleData := parseInput exampleInput

abbrev Vector32 h w := (Fin32 h × Fin32 w)
def next_coords (c: Vector32 h w) (o: Move): Option (Vector32 h w) :=
  let (x, y) := c
  match o with
  | .up => x.tryPred.map (·, y)
  | .down => x.trySucc.map (·, y)
  | .left => y.tryPred.map (x, ·)
  | .right => y.trySucc.map (x, ·)


def remainingSizeInDirection (c: Vector32 h w) (m: Move): Nat :=
  let (x, y) := c
  match m with
  | .up => x.toNat
  | .down => h - x.toNat
  | .left => y.toNat
  | .right => w - y.toNat
theorem remainingDecreases {h w: Fin UInt32.size} (p np: Vector32 h w): (next_coords p m) = some np → remainingSizeInDirection np m < remainingSizeInDirection p m := by
  intro hyp
  unfold next_coords at hyp
  unfold Fin32.tryPred at hyp
  unfold Fin32.trySucc at hyp
  unfold remainingSizeInDirection
  simp at hyp
  cases m <;> simp <;> simp at hyp <;> apply hyp.elim <;> intro h1 h2 <;> simp [Prod.ext_iff] at h2
  case up =>
    rw [←h2.left, UInt32.toNat_sub_of_le]
    case a => apply Nat.add_one_le_of_lt h1
    exact Nat.sub_one_lt (Nat.ne_of_lt h1).symm
  case left =>
    rw [←h2.right, UInt32.toNat_sub_of_le]
    case a => apply Nat.add_one_le_of_lt h1
    exact Nat.sub_one_lt (Nat.ne_of_lt h1).symm
  case down =>
    rw [←h2.left]
    apply Nat.sub_lt_sub_left
    . exact p.fst.isLt
    . conv => rhs; rw [Fin32.val_mk ]
      rw [UInt32.toNat_ofNat_of_lt (Nat.lt_trans h1 h.isLt)]
      simp
  case right =>
    rw [←h2.right]
    apply Nat.sub_lt_sub_left
    . exact p.snd.isLt
    . conv => rhs; rw [Fin32.val_mk ]
      rw [UInt32.toNat_ofNat_of_lt (Nat.lt_trans h1 w.isLt)]
      simp



def next_coords_with_lt_proof (c: Vector32 h w) (m: Move): Option { cn: Vector32 h w // remainingSizeInDirection cn m < remainingSizeInDirection c m } :=
  match cond: next_coords c m with
  | none => none
  | some cn => some ⟨cn, remainingDecreases c cn cond⟩

def Map.moveBox {h w: Fin UInt32.size} (map: Vector (Vector Tile w) h) (pos: Vector32 h w) (direction: Move): Option (Vector (Vector Tile w) h) := do
  let nextpos <- next_coords_with_lt_proof pos direction
  match map.get2d_32 nextpos with
  | Tile.wall => none
  | Tile.free => some (moveBox map pos nextpos)
  | Tile.box =>
    let map <- Map.moveBox map nextpos direction
    some (moveBox map pos nextpos)
termination_by remainingSizeInDirection pos direction
where
  moveBox (map: Vector (Vector Tile w) h) (p1: Vector32 h w) (p2: Vector32 h w) := map
    |>.modify32 p1.fst (·.set32 p1.snd Tile.free)
    |>.modify32 p2.fst (·.set32 p2.snd Tile.box)

def Map.step (m: Map) (direction: Move): Option Map := do
  let nextpos <- next_coords_with_lt_proof m.pos direction
  match m.map.get2d_32 nextpos with
  | Tile.wall => none
  | Tile.free => some { m with pos := nextpos }
  | Tile.box =>
    let map <- Map.moveBox m.map nextpos direction
    some { m with pos := nextpos, map }

def Map.execute (m: Map) (moves: List Move): Map :=
  moves.foldl (fun map move => (map.step move).getD map) m

def Map.sumGpsCoords (m: Map): Nat :=
  (m.map.toList.enum.flatMap (fun (x, line) => line.toList.enum.map (fun (y, tile) =>
    if tile = Tile.box then
      x * 100 + y
    else 0
  ))).sum

#guard some 2028 = exampleData.map (Map.sumGpsCoords ∘ Map.execute.uncurry)


def main (p2: Bool) (_args: List String) : IO Unit := do
  let file ← IO.FS.readFile "day15.txt"
  match parseInput file with
  | none => IO.println "Invalid input"
  | some (map, moves) =>
    let result := (map.execute moves).sumGpsCoords
    IO.println s!"Result: {result}"
