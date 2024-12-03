def input := "7 6 4 2 1
1 2 7 8 9
9 7 6 2 1
1 3 2 4 5
8 6 4 4 1
1 3 6 7 9"

def parseInput (s: String): List (List Nat) :=
  (s.splitOn "\n").map (fun x => (x.splitOn " ").map String.toNat!)
 

def iterPairwise (l: List α): List (α × α) := (l.drop 1).zip l

def safeLevels (l: List Nat): Bool := ((iterPairwise l).all (fun (a, b) => a > b ∧ ((a - b) ≤ 3))) ∨ ((iterPairwise l).all (fun (a, b) => (a < b) ∧ ((b - a) ≤ 3)))
example: safeLevels [1, 3, 2, 4, 5] = False := by rw [safeLevels, iterPairwise]; simp

def safeLevels2 (l: List Nat): Bool := ((List.range l.length).map (fun i => l.eraseIdx i)).any (safeLevels ·)

def aoc2_1 (l: List (List Nat)): Nat := l.countP safeLevels
def aoc2_2 (l: List (List Nat)): Nat := l.countP safeLevels2

#eval aoc2_1 (parseInput input)
#eval aoc2_2 (parseInput input)
