import Day12Etc.Fin32

@[inline]
def Vector.modify (v: Vector α n) (i: Fin n) (f: α -> α): Vector α n :=
  -- Array.modify has some (unsafe) special sauce which lets it edit the item in place without bumping the reference count
  -- this is very important when modifying vectors inside other vectors
  ⟨v.toArray.modify i f, (Array.size_modify v.toArray i f).trans (Vector.size_toArray _)⟩

@[inline]
def Vector.get32 (v: Vector α n) (i: Fin32 ⟨n, hn⟩): α :=
  v.uget i.val.toUSize (by
    rw [UInt32.toNat_toUSize]
    exact i.isLt
  )

@[inline]
def Vector.set32 (v: Vector α n) (i: Fin32 ⟨n, hn⟩) (x: α): Vector α n :=
  let a := v.uset i.val.toUSize x (by
    rw [UInt32.toNat_toUSize, Vector.size_toArray v]
    exact i.isLt
  )
  ⟨a, (Array.size_set v.toArray i.val.toNat x _).trans (Vector.size_toArray v)⟩

@[inline]
def Vector.modify32 (v: Vector α n) (i: Fin32 ⟨n, hn⟩) (f: α -> α): Vector α n :=
  -- unfortunately there is no umodify
  v.modify i.toFin f

@[inline]
def Vector.get2d_32 (v: Vector (Vector α w) h) (pos: Fin32 ⟨h, hh⟩ × Fin32 ⟨w, hw⟩) := (v.get32 pos.fst).get32 pos.snd
