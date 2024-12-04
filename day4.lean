import Batteries

def data := "MMMSXXMASM
MSAMXMSMSA
AMXSXMAAMM
MSAMASMSMX
XMASAMXAMM
XXAMMXXAMA
SMSMSASXSS
SAXAMASAAA
MAMMMXMMMM
MXMXAXMASX"

abbrev Matrix := List (List Char)

def parseInput (s: String): Matrix := (s.splitOn "\n").map String.toList

def iterDiagonal (l: Matrix): Matrix := (l.enum.map (fun (i, x) => x.drop i)).transpose ++ (l.enum.map (fun (i, x) => (x.take i).reverse)).transpose

def iterateAllDirectionsForward (m: Matrix): List (List Char) :=
  m ++ m.transpose ++ iterDiagonal m ++ iterDiagonal m.reverse
def iterateAllDirections (m: Matrix): List (List Char) := let d := iterateAllDirectionsForward m; d ++ d.map List.reverse

def allOffsets (l: List Char): List String := (List.range l.length).map (fun i => ((l.drop i).take 4).asString)

def iterateAllCandidates (m: Matrix): List String := ((iterateAllDirections m).map allOffsets).flatten

def aoc4_1 (m: Matrix): Nat := (iterateAllCandidates m).count "XMAS"

#eval aoc4_1 (parseInput data)




/-
failed experiment

def diagonalize (l: Matrix): Matrix := l.enum.map (fun (i, x) => x.rotateLeft i)

-- prove that diagonalize yields the same number of rows
example: l.length = (diagonalize l).length := by rw[diagonalize, List.length_map, List.enum_length]

-- prove that diagonalize yields the same number of columns
theorem unused_enum : List.map f l = List.map (f ∘ Prod.snd) l.enum :=
  by rw [←List.map_map, List.enum_map_snd]
theorem rotateLeft_length : (List.rotateLeft l i).length = l.length := by
  unfold List.rotateLeft
  simp
  split
  . rfl
  . rw [List.length_append, Nat.add_comm, ←List.length_append, List.take_append_drop]

example: l.map List.length = (diagonalize l).map List.length := by
  rw[diagonalize, List.map_map, unused_enum, List.map_eq_map_iff]
  simp
  intros
  rw [rotateLeft_length]
-/
