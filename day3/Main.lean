import Regex

def corrupted := "xmul(2,4)%&mul[3,7]!@^do_not_mul(5,5)+mul(32,64]then(mul(11,8)mul(8,5))"

inductive Instr where
  | mul (x: Nat) (y: Nat)
  | do
  | dont
  deriving Repr


def parse_instr (cap: Regex.Captures): Instr :=
  match cap.groups[2]?.join.map Substring.toString with
  | some "do" => Instr.do
  | some "don't" => Instr.dont
  | _ => Instr.mul cap.groups[0]!.get!.toString.toNat! cap.groups[1]!.get!.toString.toNat!

def parse_mul_instrs (s: String) (with_do_dont: Bool): Array Instr :=
  let pattern := if with_do_dont then regex% r"mul\((\d\d?\d?),(\d\d?\d?)\)|(do(n't)?)\(\)" else regex% r"mul\((\d\d?\d?),(\d\d?\d?)\)"
  (Regex.all_captures s pattern).map parse_instr

--#eval parse_mul_instrs "xmul(2,4)&mul[3,7]!^don't()_mul(5,5)+mul(32,64](mul(11,8)undo()?mul(8,5))" True

def exec_muls_helper (l: List Instr) (soFar: Nat) (active: Bool): Nat := match l, active with
  | [], _ => soFar
  | Instr.do::ls, _ => exec_muls_helper ls soFar True
  | Instr.dont::ls, _ => exec_muls_helper ls soFar False
  | (Instr.mul x y)::ls, Bool.true => exec_muls_helper ls (soFar + x * y) active
  | (Instr.mul _ _)::ls, Bool.false => exec_muls_helper ls soFar active
def exec_muls (a: Array Instr): Nat := exec_muls_helper a.toList 0 True

-- idk how to prove anything with regex parsing (lol)
--example: exec_muls (parse_mul_instrs corrupted) = 161 := rfl

def main (args: List String) : IO Unit := do
  let file ← IO.FS.readFile "input.txt"
  let parsed := parse_mul_instrs file (args[0]? = "2")
  let result := exec_muls parsed
  IO.println s!"Result: {result}"
