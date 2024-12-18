import Mathlib
import Day12Etc.StringExt

namespace Day17

def exampleInputStr := "Register A: 729
Register B: 0
Register C: 0

Program: 0,1,5,4,3,0"

structure Registers where
  (ra rb rc: Int)
deriving Repr

structure Instruction where
  opcode: Fin 8
  operand: Fin 8
deriving Repr

structure StartState where
  regs: Registers
  instrs: List Instruction
deriving Repr

structure Machine where
  regs: Registers
  text: Array (Fin 8)
  ip: Nat
  output: List (Fin 8)
deriving Repr

def parseInput (s: String): Option Machine := do
  let (regs, prog) <- s.splitOnce "\n\n"
  let regs <- ((regs.splitOn "\n").map (fun s => (String.splitOnce s ": ").bind (String.toInt? ∘ Prod.snd))).allSome
  let regs <- match regs with
  | [ra, rb, rc] => some ({ ra, rb, rc }: Registers)
  | _ => none
  let prog := prog.replace "Program: " ""
  let nibbles <- ((prog.splitOn ",").map (fun s => (String.toNat? s).bind (fun oc => if h: oc < 8 then some (Fin.mk oc h) else none))).allSome
  /-
  let instrs <- ((nibbles.toChunks 2).map (fun ch => match ch with
  | [opcode, operand] => some ({ opcode, operand }: Instruction)
  | _ => none
  )).allSome
  -/
  some { regs, text := nibbles.toArray, ip := 0, output := [] }

def exampleInput := parseInput exampleInputStr

-- returns false if halt
def Machine.stepi (m: Machine): Option Machine :=
  let operand_ip := m.ip + 1
  if hlt: operand_ip < m.text.size then
    let instr := m.text[m.ip]
    let operand := m.text[operand_ip]
    --dbg_trace "{m.ip} {repr m.regs} {instr} {operand}"
    let ip := m.ip + 2
    let newm := match hi: instr with
    | 0 | 6 | 7 => -- shl
      let num := m.regs.ra
      let den := decodeComboOperand operand
      let res := Int.shiftRight num den.toNat
      --dbg_trace "{num} {den} {res}"
      let regs := if hi1: instr = 0 then
        { m.regs with ra := res }
      else if hi2: instr = 6 then
        { m.regs with rb := res }
      else if hi3: instr = 7 then
        { m.regs with rc := res }
      else
        absurd hi (by simp [hi1, hi2, hi3])
      { m with ip, regs }
    | 1 => -- xor B
      let regs := { m.regs with rb := Int.xor m.regs.rb (decodeLitOperand operand) }
      { m with ip, regs }
    | 2 => -- b = oper % 8
      let oper := decodeComboOperand operand
      let regs := { m.regs with rb := oper % 8 }
      { m with ip, regs }
    | 3 => -- jnz
      if m.regs.ra = 0 then
        { m with ip }
      else
        { m with ip := (decodeLitOperand operand).toNat }
    | 4 => -- xor b, c
      let regs := { m.regs with rb := Int.xor m.regs.rb m.regs.rc }
      { m with ip, regs }
    | 5 => -- out operand
      let oval := (decodeComboOperand operand) % 8
      { m with ip, output := oval::m.output }
    some newm
  else
    none
where
  @[inline] decodeLitOperand (o: Fin 8): Int := o.val
  @[inline] decodeComboOperand (o: Fin 8): Int := match o with
  | 0 | 1 | 2 | 3 => o.val
  | 4 => m.regs.ra
  | 5 => m.regs.rb
  | 6 => m.regs.rc
  | 7 => panic "bad combo operand"

def Machine.run (m: Machine) (iterations: Nat): List (Fin 8) :=
  if iterations = 0 then
    m.output
  else
    let output := m.output
    match m.stepi with
    | none => output
    | some m => m.run (iterations - 1)

--#eval exampleInput
--#eval (exampleInput.map (·.run 1000)).map List.reverse




def main (p2: Bool) (_args: List String) : IO Unit := do
  let file ← IO.FS.readFile "day17.txt"
  match parseInput file with
  | none => IO.println "Invalid input"
  | some machine =>
    let result := ",".intercalate ((machine.run 1000000).reverse.map (fun x => x.val.repr))
    IO.println s!"Result: {result}"
