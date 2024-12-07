import Batteries

def combine_part1 (x: Nat) (y: Nat): List Nat := [y + x, y * x]

def potentialValues (l: List Nat) (combine: Nat → Nat → List Nat): List Nat := match l with
| [] => []
| x::[] => [x]
| x::xs => (potentialValues xs combine).flatMap (combine · x)

#guard (potentialValues [10, 19].reverse combine_part1).contains 190
#guard (potentialValues [81, 40, 27].reverse combine_part1).contains 3267
#guard (potentialValues [11, 6, 16, 20].reverse combine_part1).contains 292

structure Equation where
  expected: Nat
  nums: List Nat
deriving Repr

def parseInput (s: String) : Option (List Equation) :=
  ((s.splitOn "\n").map (fun l =>
    match l.splitOn ": " with
    | [exp, tail] =>
      match (exp.toNat?, ((tail.splitOn " ").map String.toNat?).allSome) with
      | (some expected, some nums) => some { expected, nums }
      | _ => none
    | _ => none
  )).allSome

def Equation.isValid (e: Equation) (combine: Nat → Nat → List Nat) := (potentialValues e.nums.reverse combine).contains e.expected

def exampleInput := parseInput "190: 10 19
3267: 81 40 27
83: 17 5
156: 15 6
7290: 6 8 6 15
161011: 16 10 13
192: 17 8 14
21037: 9 7 18 13
292: 11 6 16 20"

def sumValidEquations (l: List Equation) (combine: Nat → Nat → List Nat): Nat := ((l.filter (Equation.isValid · combine)).map Equation.expected).sum
def aoc7_1 (l: List Equation): Nat := sumValidEquations l combine_part1

def find_next_pow10 (x: Nat): Nat :=
  if x = 0 then
    1
  else
    10 * (find_next_pow10 (x / 10))
#guard 100 = find_next_pow10 42
#guard 100 = find_next_pow10 99
#guard 1000 = find_next_pow10 100
#guard 1000 = find_next_pow10 101
#guard 1000 = find_next_pow10 999
#guard 10000 = find_next_pow10 1000
def conc_num (x: Nat) (y: Nat): Nat := x * (find_next_pow10 y) + y
#guard 12345 = conc_num 12 345
def combine_part2 (x: Nat) (y: Nat): List Nat := [x + y, x * y, conc_num x y]
def aoc7_2 (l: List Equation): Nat := sumValidEquations l combine_part2

#guard some 3749 = exampleInput.map aoc7_1
