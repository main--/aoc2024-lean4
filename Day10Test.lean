import Mathlib


structure ArrayMap (α: Type) (β: Type) [fea: FinEnum α] where
  data: Vector β fea.card

namespace ArrayMap
variable {α: Type} {β: Type} [fea: FinEnum α]
def init (init: β): ArrayMap α β := { data := Vector.mkVector fea.card init }
@[inline] def get (map: ArrayMap α β) (key: α) := map.data.get (fea.equiv key)
@[inline] def set (map: ArrayMap α β) (key: α) (value: β): ArrayMap α β := ⟨map.data.set (fea.equiv key) value⟩
def update (map: ArrayMap α β) (key: α) (update: β -> β): ArrayMap α β :=
  let index := fea.equiv key
  let newval := update (map.data.get index)
  ⟨map.data.set index newval⟩
def iter (map: ArrayMap α β): List (α × β) :=
  let keys := fea.toList
  keys.map (fun k => (k, map.get k))
-- i am very lazy so just using hashmap's repr
instance [Hashable α] [Repr α] [Repr β] : Repr (ArrayMap α β) where
  reprPrec am := instReprList.reprPrec am.iter
  --reprPrec am := Std.HashMap.instRepr.reprPrec (Std.HashMap.ofList am.iter)
-- end library code from day8
end ArrayMap


-- so uhm
-- turns out that the stdlib instances for FinEnum (Fn n) and FinEnum (Prod a b) are defined using FinEnum.ofList
-- which means that every single time we use FinEnum.equiv, we would end up creating a list of all possible values,
-- deduplicate the list, and then iterate it to look for the right value
-- this turns out to be VERY slow. pikachu.jpg
-- I accidentally O(n**10) or something
instance betterEnumFin: FinEnum (Fin n) where
  card := n
  equiv := {
    toFun := id
    invFun := id
    left_inv := id_eq
    right_inv := id_eq
  }

theorem Nat.ediv_lt_of_lt_mul {a b c : Nat} (h1: 0 < c) (h2: a < b * c): a / c < b :=
  (Nat.div_lt_div_of_lt_of_dvd (Nat.dvd_mul_left c b) h2).trans_eq (Nat.mul_div_cancel b h1)


theorem div_elim_insignificant_summand {a b c: Nat} (hb0: 0 < b) (hcb: c < b) : (a * b + c) / b = a := by
  rw [Nat.add_div hb0, Nat.div_eq_of_lt hcb, Nat.mul_div_cancel a hb0]
  simp
  exact Nat.mod_lt c hb0

instance betterEnumProd α β [fea: FinEnum α] [feb: FinEnum β]: FinEnum (α × β) where
  card := fea.card * feb.card
  equiv := {
    toFun prod :=
      --let (a, b) := prod.map fea.equiv feb.equiv
      let (a, b) := (fea.equiv prod.fst, feb.equiv prod.snd)
      ⟨a.val * feb.card + b.val, by
        have h3: (FinEnum.card α) * (FinEnum.card β) = (FinEnum.card α).pred * (FinEnum.card β) + (FinEnum.card β) := by
          convert (Nat.succ_mul (FinEnum.card α).pred (FinEnum.card β))
          exact (Nat.succ_pred (Nat.ne_of_lt a.pos).symm).symm
        rw [h3]
        convert Nat.lt_of_add_one_le _
        rw [Nat.add_assoc]
        exact Nat.add_le_add (Nat.mul_le_mul_right (FinEnum.card β) (Nat.le_sub_one_of_lt a.isLt)) (Nat.add_one_le_of_lt b.isLt)
      ⟩
    invFun f :=
      let ia := f.val / feb.card
      let ib := f.val % feb.card
      (
        fea.equiv.symm ⟨ia, Nat.ediv_lt_of_lt_mul (Nat.pos_of_mul_pos_left f.pos) f.isLt⟩,
        feb.equiv.symm ⟨ib, Nat.mod_lt f.val (LT.lt.gt (Nat.pos_of_mul_pos_left f.pos))⟩
      )
    left_inv x := by
      simp
      have rul := Nat.mul_add_mod_of_lt (a:=(fea.equiv x.fst).val) (b := feb.card) (c := (feb.equiv x.snd).val) (feb.equiv x.snd).isLt
      rw [Prod.eq_iff_fst_eq_snd_eq]
      apply And.intro
      case left =>
        simp [div_elim_insignificant_summand (a:=(fea.equiv x.fst).val) (feb.equiv x.snd).pos (feb.equiv x.snd).isLt]
      case right =>
        simp [rul]
    right_inv x := by simp [Nat.div_add_mod']
  }


abbrev Digit := Fin 10
abbrev Vector2d h w β := ArrayMap ((Fin h) × (Fin w)) β

structure Map where
  width: Nat
  height: Nat
  data: Vector (Vector Digit width) height

abbrev Coords (m: Map) := (Fin m.height × Fin m.width)

def Map.get (m: Map) (c: Coords m) := m.data[c.fst][c.snd]

def exampleInputString := "0123
1234
8765
9876"

def parseDigit (c: Char): Option Digit :=
  if range: c ≥ '0' ∧ c ≤ '9' then
    some ⟨(c.toNat - '0'.toNat), (by
      have top := Nat.lt_add_one_of_le range.right
      simp at top
      simp [Char.toNat, UInt32.toNat.eq_1]
      exact Nat.sub_lt_left_of_lt_add (by apply range.left) top
    )⟩
  else
    none

def parseInput (s: String): Option Map :=
  let lines := s.splitOn "\n"
  let height := lines.length
  if nonempty: height = 0
  then none
  else
    let width := lines[0].length
    let map: List (Option (Vector Digit _)) := lines.map (fun s =>
      (s.toList.map parseDigit).allSome.bind (fun s =>
        let s := s.toArray
        if checkw: s.size = width then
          some (Vector.mk s checkw)
        else
          none
      )
    )
    map.allSome.map (fun as =>
      let as := as.toArray
      let height := as.size
      { width, height, data := Vector.mk as rfl }
    )

--def exampleInput := parseInput exampleInputString

def Map.byLevel (m: Map): ArrayMap Digit (List (Coords m)) :=
  let allCoords := (List.finRange m.height).flatMap (fun x => (List.finRange m.width).map (x, ·))
  allCoords.foldl (fun out coord => out.update (m.get coord) (coord::·)) (ArrayMap.init [])

def Coords.neighbors {h w: Nat} (c: (Fin h) × (Fin w)): List ((Fin h) × (Fin w)) :=
  let (x, y) := c
  ((neighbors1d x).map (·, y)) ++ ((neighbors1d y).map (x, ·))
where
  neighbors1d {n: Nat} (f: Fin n): List (Fin n) :=
    (if nz: 0 < f.val then [⟨f.val - 1, Nat.sub_one_lt_of_le nz (Nat.le_of_lt f.isLt)⟩] else [])
    ++
    (if nmax: f.val + 1 < n then [⟨f.val + 1, nmax⟩] else [])

--#eval Coords.neighbors (h := 10) (w := 10) (5, 5)

/-
def scoreTrailheads (m: Map): Nat :=
  let byLevel := m.byLevel
  let work := (List.finRange 10).foldr (fun i work =>
    match i with
    | 9 => work -- nothing to do, map was initialized to 1
    | i => atLevel byLevel i work
  ) (ArrayMap.init 1)
  ((byLevel.get 0).map work.get).sum
where
  atLevel (byLevel: ArrayMap Digit (List (Coords m))) (l: Fin 10) (work: Vector2d m.height m.width Nat) :=
    (byLevel.get l).foldl (fun work coord =>
      work.update coord (((coord.neighbors.filter (fun nc => (m.get nc) = (l + 1))).map (work.get ·)).sum)
    ) work

def scoreTrailheads2 (m: Map) :=
  let byLevel := m.byLevel
  let work := (List.finRange 10).foldr (fun i work =>
    match i with
    | 9 => work -- nothing to do, map was initialized to 1
    | i => atLevel byLevel i work
  ) (ArrayMap.init 1)
  repr work
  --((byLevel.get 0).map work.get).sum
where
  atLevel (byLevel: ArrayMap Digit (List (Coords m))) (l: Fin 10) (work: Vector2d m.height m.width Nat) :=
    (byLevel.get l).foldl (fun work coord =>
      work.update coord (((coord.neighbors.filter (fun nc => (m.get nc) = (l + 1))).map (work.get ·)).sum)
    ) work
-/


/-
def warshallAlgo {numVertex: Nat} (edges: List ((Fin numVertex) × (Fin numVertex))) :=
  let connected := ArrayMap.init false
  let connected := edges.foldl (fun conn e => conn.set e true) connected
  let connected := (List.finRange numVertex).foldl (fun conn v => conn.set (v, v) true) connected
  let iter := List.finRange numVertex
  ((iter.productTR iter).productTR iter).foldl (fun conn ((k, i), j) =>
    if (conn.get (i, k)) ∧ (conn.get (k, j)) then
      conn.set (i, j) true
    else conn
  ) connected
-/
--variable {numVertex: Nat}
abbrev Fin32 (n: UInt32) := { val: UInt32 // val < n }
def Fin32.succ (f: Fin32 n): Option (Fin32 n) := if v: f.val + 1 < n then some ⟨f.val + 1, v⟩ else none
theorem Fin32.pos (i : Fin32 n) : 0 < n :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
instance enumFin32: FinEnum (Fin32 n) where
  card := n.toNat
  equiv := {
    toFun x := ⟨x.val.toNat, x.prop⟩
    invFun x := ⟨UInt32.ofNatCore x.val (Nat.lt_trans x.prop (UInt32.toNat_lt_size n)), (by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNatCore]
      exact x.prop
    )⟩
    left_inv x := by
      simp
      convert Subtype.coe_eta _ _
      exact x.prop
    right_inv x := by simp
  }
def Fin.toFin32 (f: Fin n) (h: n < UInt32.size): (Fin32 n.toUInt32) := enumFin32.equiv.symm (f.cast (by
  unfold FinEnum.card
  unfold enumFin32
  simp
  rw [Nat.mod_eq_of_lt h]
))

abbrev warshallAlgo.Conn (numVertex: UInt32) := ArrayMap ((Fin32 numVertex) × (Fin32 numVertex)) Bool
def innermost (numVertex: UInt32) (k i j: Fin32 numVertex) (conn: warshallAlgo.Conn numVertex): warshallAlgo.Conn numVertex :=
    let set := (conn.get (i, k)) && (conn.get (k, j))
    --dbg_trace "innermost {k} {i} {j} {set}";
    if set then
      conn.set (i, j) true
    else conn
def iterJ (numVertex: UInt32) (k i j: Fin32 numVertex) (conn: warshallAlgo.Conn numVertex): warshallAlgo.Conn numVertex :=
    --dbg_trace "iterJ {k} {i} {j}";
    if jval: j.val + 1 < numVertex then
      iterJ numVertex k i ⟨j.val+1, jval⟩ (innermost numVertex k i j conn)
    else conn
termination_by numVertex - j.val
decreasing_by sorry
def iterI (numVertex: UInt32) (k i: Fin32 numVertex) (conn: warshallAlgo.Conn numVertex): warshallAlgo.Conn numVertex :=
    --dbg_trace "iterI {k} {i}";
    if ival: i.val + 1 < numVertex then
      iterI numVertex k ⟨i.val+1, ival⟩ (iterJ numVertex k i ⟨0, k.pos⟩ conn)
    else conn
termination_by numVertex - i.val
decreasing_by sorry
def iterK (numVertex: UInt32) (k: Fin32 numVertex) (conn: warshallAlgo.Conn numVertex): warshallAlgo.Conn numVertex :=
    --dbg_trace "iterK {k}";
    match k.succ with
    | some nextk => iterK numVertex nextk (iterI numVertex k ⟨0, k.pos⟩ conn)
    | none => conn
termination_by numVertex - k.val
decreasing_by sorry
/-
decreasing_by
  simp
  --rw [<-UInt32.lt_iff_toNat_lt]
  rw [UInt32.toNat_sub_of_le _ _ (Nat.le_of_lt kval), UInt32.toNat_sub_of_le _ _ (Nat.le_of_lt k.prop)]
  convert Nat.sub_lt_sub_left (m:=numVertex.toNat) _ _
  . rw [<-UInt32.lt_iff_toNat_lt]
    exact k.prop
  . rw [UInt32.toNat_add]
    rw [Nat.mod_eq_of_lt _]
    . simp
    .
      have lul := UInt32.lt_iff_toNat_lt.mp k.prop

      --have lul2 := UInt32.toNat_lt_size numVertex
      --have lul3 := Nat.lt_trans lul lul2
      simp only [UInt32.reduceToNat]

    --rw [Nat.mod_eq_of_lt (Nat.lt_trans (UInt32.lt_iff_toNat_lt.mp k.prop) sorry)]

    --rw [<-UInt32.lt_iff_toNat_lt]
    --simp
-/
/-
def warshallAlgo (edges: List ((Fin numVertex) × (Fin numVertex))): warshallAlgo.Conn numVertex :=
  dbg_trace "beginWarshall {numVertex}";
  let connected := ArrayMap.init false
  if nontrivial: 0 < numVertex then
    dbg_trace "haveArraymap {connected.data.size}";
    let connected := edges.foldl (fun conn e => conn.set e true) connected
    dbg_trace "haveEdges {edges.length}";
    let connected := (List.finRange numVertex).foldl (fun conn v => conn.set (v, v) true) connected
    dbg_trace "haveVertices";
    iterK numVertex ⟨0, nontrivial⟩ connected
  else connected
-/
def warshallAlgo (edges: List ((Fin numVertex) × (Fin numVertex))): warshallAlgo.Conn numVertex.toUInt32 :=
  dbg_trace "beginWarshall {numVertex}";
  let connected := ArrayMap.init false
  if nonhuge: numVertex < UInt32.size then
    if nontrivial: 0 < numVertex.toUInt32 then
      let connected := edges.foldl (fun conn (x, y) => conn.set (x.toFin32 nonhuge, y.toFin32 nonhuge) true) connected
      dbg_trace "haveEdges {edges.length}";
      let connected := (List.finRange numVertex).foldl (fun conn v => conn.set (v.toFin32 nonhuge, v.toFin32 nonhuge) true) connected
      dbg_trace "haveVertices";
      iterK numVertex.toUInt32 ⟨0, nontrivial⟩ connected
    else connected
  else connected

--def genericWarshallAlgo [FinEnum α] (edges: List (α × α))
instance feCoords: FinEnum (Coords m) := inferInstance

def scoreTrailheads (m: Map) :=
  let allCoords: List (Coords m) := (List.finRange m.height).flatMap (fun x => (List.finRange m.width).map (x, ·))
  let edges := allCoords.flatMap (fun c =>
    let v := m.get c
    if nmax: v.val + 1 < 10 then
      let nval: Fin 10 := ⟨v.val + 1, nmax⟩
      (c.neighbors.filter (fun n => nval = m.get n)).map (c, ·)
    else []
  )
  let genericEdges := edges.map (·.map feCoords.equiv feCoords.equiv)
  let byLevel := m.byLevel
  let transitiveConnections := warshallAlgo genericEdges
  if nonhuge: feCoords.card < UInt32.size then
  ((byLevel.get 0).map (fun zero =>
    (byLevel.get 9).countP (fun nine => transitiveConnections.get ((feCoords.equiv zero).toFin32 nonhuge, (feCoords.equiv nine).toFin32 nonhuge))
  )).sum
  else
  0


--#eval exampleInput.map scoreTrailheads


def main (args: List String) : IO Unit := do
  let file ← IO.FS.readFile "input.txt"
  match parseInput file with
  | none => IO.println "Invalid input"
  | some map =>
    if args[0]? = "2" then
      let result := "sorry"
      IO.println s!"Result: {result}"
    else
      let result := scoreTrailheads map
      IO.println s!"Result: {result}"
