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

def aoc2_1 (l: List (List Nat)): Nat :=
  l.countP safeLevels

#eval aoc2_1 (parseInput input)
