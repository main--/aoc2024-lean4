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


def Matrix.getChar (m: Matrix) (x: Nat) (y: Nat): Char := ((m.get? x).bind (fun r => r.get? y)).getD ' '

def isX_MAS (m: Matrix) (x: Nat) (y: Nat): Bool :=
  (x ≥ 1) ∧ (y ≥ 1) ∧ (m.getChar x y = 'A')
  ∧ ([m.getChar (x-1) (y-1), m.getChar (x+1) (y+1)].mergeSort = ['M', 'S'])
  ∧ ([m.getChar (x-1) (y+1), m.getChar (x+1) (y-1)].mergeSort = ['M', 'S'])
example: isX_MAS [['M', ' ', 'M'], [' ', 'A', ' '], ['S', ' ', 'S']] 1 1 = True := by rw [isX_MAS, Matrix.getChar, Matrix.getChar, Matrix.getChar, Matrix.getChar, Matrix.getChar]; simp; rw [List.mergeSort_of_sorted]; simp
example: isX_MAS [['M', ' ', 'M'], [' ', 'A', ' '], ['S', ' ', 'S']] 0 1 = False := by rw [isX_MAS, Matrix.getChar, Matrix.getChar, Matrix.getChar, Matrix.getChar, Matrix.getChar]; simp
example: isX_MAS [['M', ' ', 'M'], [' ', 'A', ' '], ['S', ' ', 'S']] 2 1 = False := by rw [isX_MAS, Matrix.getChar, Matrix.getChar, Matrix.getChar, Matrix.getChar, Matrix.getChar]; simp
example: isX_MAS [['M', ' ', 'M'], [' ', 'A', ' '], ['Y', ' ', 'S']] 1 1 = False := by
  rw [isX_MAS, Matrix.getChar, Matrix.getChar, Matrix.getChar, Matrix.getChar, Matrix.getChar]
  simp
  rw [List.mergeSort_of_sorted, List.mergeSort_of_sorted]
  simp
  simp
  simp

def count_x_mas (m: Matrix) :=
  let coords := m.enum.flatMap (fun (i, x) => (List.range x.length).map (fun j => (i, j)))
  coords.countP (fun (x, y) => isX_MAS m x y)

#eval count_x_mas (parseInput data)
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
