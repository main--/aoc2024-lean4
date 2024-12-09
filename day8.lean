import Mathlib


structure ArrayMap (α: Type) (β: Type) [FinEnum α] where
  data: Vector β (FinEnum.card α)

def ArrayMap.init [FinEnum α] (init: β): ArrayMap α β := { data := Vector.mkVector (FinEnum.card α) init }
def ArrayMap.get [FinEnum α] (map: ArrayMap α β) (key: α) := map.data.get (FinEnum.equiv key)
def ArrayMap.update [FinEnum α] (map: ArrayMap α β) (key: α) (update: β -> β): ArrayMap α β :=
  let index := FinEnum.equiv key
  let newval := update (map.data.get index)
  ⟨map.data.set index newval⟩
def ArrayMap.iter [fea: FinEnum α] (map: ArrayMap α β): List (α × β) :=
  let keys := fea.toList
  keys.map (fun k => (k, map.get k))
-- i am very lazy so just using hashmap's repr
instance [fea: FinEnum α] [Hashable α] [Repr α] [Repr β] : Repr (ArrayMap α β) where
  reprPrec am := Std.HashMap.instRepr.reprPrec (Std.HashMap.ofList am.iter)

abbrev AntennaFrequency := { c: Char // c.isAlphanum }
instance AntennaFrequency.finEnum: FinEnum AntennaFrequency :=
  FinEnum.ofList
    (((List.range 256).map Char.ofNat).filterMap (β := AntennaFrequency) (fun c => if p: c.isAlphanum then some ⟨c, p⟩ else none))
    (by
      intro af
      simp [List.mem_filterMap, Subtype.eq]
      exists af.val.toNat
      rw [Char.ofNat_toNat]
      refine ⟨?_, ?_⟩
      . have pe := af.prop
        rw [Char.toNat.eq_1]
        simp [Char.isAlphanum, Char.isAlpha, Char.isDigit, Char.isUpper, Char.isLower] at pe
        repeat rw [UInt32.le_iff_toNat_le] at pe
        cases pe
        case refine_1.inl c1 =>
          cases c1 <;> rename_i c <;> exact lt_of_le_of_lt (a := af.val.val.toNat) c.right (by simp)
        case refine_1.inr c2 => exact lt_of_le_of_lt (a := af.val.val.toNat) c2.right (by simp)
      . exists af.prop
    )
#guard (26+26+10) = FinEnum.card AntennaFrequency

structure Coords (h: Nat) (w: Nat) where
  x: Fin h
  y: Fin w
deriving Repr, DecidableEq, Hashable


def exampleInput := "............
........0...
.....0......
.......0....
....0.......
......A.....
............
............
........A...
.........A..
............
............"

structure Input where
  height: Nat
  width: Nat
  antennas: ArrayMap AntennaFrequency (List (Coords height width))
deriving Repr

def List.enumFin (l: List α): List (Fin l.length × α) := (List.finRange l.length).zip l
theorem List.enumFinLength (l: List α): l.length = l.enumFin.length := by simp [List.enumFin]

def parseInput (s: String): Option Input :=
  let lines := s.splitOn "\n"
  if neh: lines.length = 0
  then
    none
  else
    let width := lines[0].length
    let tiles := lines.enumFin.flatMap (fun (x, line) =>
      let chars := line.toList
      if checkw: chars.length = width then
        line.toList.enumFin.map (fun (y, c) => some (⟨x, y.cast checkw⟩, c))
      else
        [none]
    )
    tiles.allSome.map (collectAntennas { height := lines.length, width, antennas := ArrayMap.init [] })
where
  collectAntennas (i: Input) (l: List ((Coords i.height i.width) × Char)): Input := match l with
  | [] => i
  | (pos, c)::xs =>
    if isaf: c.isAlphanum then
      collectAntennas { i with antennas := i.antennas.update ⟨c, isaf⟩ (pos::·) } xs
    else
      collectAntennas i xs

def exampleData := parseInput exampleInput
--#eval repr exampleData

def ratToFin (n: Nat) (r: Rat): Option (Fin n) :=
  if r.isInt then
    r.num.toNat'.bind (fun i =>
      if nf: i < n then some ⟨i, nf⟩ else none
    )
  else none

def filterValidAntinodes (c: (Rat × Rat)): Option (Coords h w) := match (ratToFin h c.fst, ratToFin w c.snd) with
  | (some x, some y) => some ⟨x, y⟩
  | _ => none

def pairAntinodes {h w: Nat} (a b: Coords h w): List (Coords h w) :=
  if a = b then [] else
  let a := (Rat.ofInt a.x, Rat.ofInt a.y)
  let b := (Rat.ofInt b.x, Rat.ofInt b.y)
  let delta := b - a
  [a - delta, b + delta, a + (delta/3), b - (delta/3)].filterMap filterValidAntinodes
#guard [⟨1, 3⟩, ⟨7, 6⟩] = pairAntinodes (h := 10) (w := 10) ⟨3, 4⟩ ⟨5, 5⟩

def freqAntinodes {h w: Nat} (pan: (a b: Coords h w) → List (Coords h w)) (l: List (Coords h w)): List (Coords h w) := (l.product l).flatMap pan.uncurry
#eval freqAntinodes (h := 10) (w := 10) pairAntinodes [⟨3, 4⟩, ⟨5, 5⟩, ⟨4, 8⟩]

def Input.findAntinodes (i: Input) (pan: (a b: Coords i.height i.width) → List (Coords i.height i.width)) :=
  let antinodes := i.antennas.iter.flatMap ((freqAntinodes pan) ∘ Prod.snd)
  (Std.HashSet.ofList antinodes).size

--#eval exampleData.map (Input.findAntinodes · pairAntinodes)

def pairAntinodes2 {h w: Nat} (a b: Coords h w): List (Coords h w) :=
  if a = b then [] else
  let a := (Rat.ofInt a.x, Rat.ofInt a.y)
  let b := (Rat.ofInt b.x, Rat.ofInt b.y)
  let delta := b - a
  let slope := delta.fst / delta.snd
  let step := (Rat.ofInt slope.num, Rat.ofInt slope.den)
  let steps := max h w
  (Int.range (-steps) steps).filterMap (fun i => filterValidAntinodes (a + (step * i)))

#eval exampleData.map (Input.findAntinodes · pairAntinodes2)
