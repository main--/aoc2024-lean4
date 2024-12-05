import Batteries

def data := "47|53
97|13
97|61
97|47
75|29
61|13
75|53
29|13
97|29
53|29
61|53
97|53
61|29
47|13
75|47
97|75
47|61
75|61
47|29
75|13
53|13

75,47,61,53,29
97,61,53,29,13
75,29,13
75,97,47,61,53
61,13,29
97,13,75,29,47"


structure NonemptyList (α: Type) where
  l: List α
  nonempty: l.length > 0


abbrev Rule := Nat × Nat

abbrev Pages := NonemptyList Nat


/-
theorem splitOn_nonempty (s: String): (s.splitOn x).length > 0 := by
  unfold String.splitOn
  simp
  unfold String.splitOnAux
  simp
  split
  . simp
  . split
    . simp
    . unfold String.splitOnAux
      simp

theorem lt_not_ge (a b: Nat) : (a <= b) = ¬ (a > b) := by simp

theorem splitOnAux_nonempty (i_valid: i.byteIdx ≤ s.endPos.byteIdx) : (String.splitOnAux s sep b i j r).length > 0 := by
  unfold String.splitOnAux
  split
  . simp
  . split
    . simp
      split
      . apply splitOnAux_nonempty
        rename_i notend _ _
        rw [String.endPos.eq_1]
        simp
        rw [lt_not_ge]
        rw [<-decide_eq_false_iff_not]
        rw [←String.atEnd.eq_1]
        apply notend
        --rw [String.next, String.get, String.utf8GetAux.eq_def]
        --simp
      . apply splitOnAux_nonempty
    . apply splitOnAux_nonempty
termination_by (s.endPos.1 - (i - j).1, sep.endPos.1 - j.1)
decreasing_by
  all_goals simp_wf
  focus
    rename_i h _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (String.lt_next s _)
  focus
    refine Prod.Lex.left (sep.endPos.byteIdx - (sep.next j).byteIdx) (sep.endPos.byteIdx - j.byteIdx) ?_
    refine Nat.sub_lt_sub_left ?_ ?_
    . simp
    . simp
  focus
    rename_i h _ _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (String.lt_next s _))
-/
/-
theorem splitOnAux_nonempty : (String.splitOnAux s sep b i j r).length > 0 := by
  unfold String.splitOnAux
  split
  . simp
  . split
    . simp
      split
      . apply splitOnAux_nonempty
      . apply splitOnAux_nonempty
    . apply splitOnAux_nonempty
termination_by (s.endPos.1 - (i - j).1, sep.endPos.1 - j.1)
decreasing_by
  all_goals simp_wf
  focus
    rename_i h _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (String.lt_next s _)
  focus
    refine Prod.Lex.left (sep.endPos.byteIdx - (sep.next j).byteIdx) (sep.endPos.byteIdx - j.byteIdx) ?_
    refine Nat.sub_lt_sub_left ?_ ?_
    . simp
    . simp
  focus
    rename_i h _ _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (String.lt_next s _))

I was too stupid to prove it for String.splitOn so I'm proving it for Substring.splitOn instead
-/
theorem splitOnLoop_nonempty : (Substring.splitOn.loop s sep b i j r).length > 0 := by
  unfold Substring.splitOn.loop
  split
  . simp
    . split
      . split
        . exact splitOnLoop_nonempty
        . exact splitOnLoop_nonempty
      . exact splitOnLoop_nonempty
  . split
    . simp
    . simp
termination_by s.bsize - i.1
decreasing_by -- anyone who really knows lean4 would probably laugh their ass off here
  focus
    simp
  focus
    rename_i h _
    refine Nat.sub_lt_sub_left h ?_
    apply Substring.lt_next
    exact h
  focus
    simp
  focus
    rename_i h _ _
    refine Nat.sub_lt_sub_left h ?_
    apply Substring.lt_next
    exact h
  focus
    rename_i h _ _
    refine Nat.sub_lt_sub_left h ?_
    apply Substring.lt_next
    exact h


theorem splitOn_nonempty : (Substring.splitOn s sep).length > 0 := by
  unfold Substring.splitOn
  split
  . simp
  . exact splitOnLoop_nonempty


def parseInput (s: String): ((List Rule) × (List Pages)) :=
  let pair := s.splitOn "\n\n"
  assert! pair.length = 2
  let rules := (pair[0]!.splitOn "\n").map (fun l =>
    let xy := l.splitOn "|"
    assert! xy.length = 2
    (xy[0]!.toNat!, xy[1]!.toNat!)
  )
  let pages := (pair[1]!.splitOn "\n").map (fun l =>
    { l:= (l.toSubstring.splitOn ",").map (String.toNat! ∘ Substring.toString), nonempty := (by
      rw [List.length_map]
      apply splitOn_nonempty
    ) }
  )
  (rules, pages)

def validateRule (r: Rule) (p: Pages): Bool := ¬ ((p.l.dropWhile (· ≠ r.snd)).contains r.fst)
example: validateRule (47, 53) { l := [75,47,61,53,29], nonempty := (by simp) } = True := by rw [validateRule]; simp
example: validateRule (97, 75) { l := [75,97,47,61,53], nonempty := (by simp) } = False := by rw [validateRule]; simp
theorem validateRule_pos (hab : a ≠ b) (hac3 : a ≠ c3) (hbc1 : b ≠ c1) (hbc2 : b ≠ c2) : (validateRule (a, b) { l:= [c1, a, c2, b, c3], nonempty } = True) := by
  rw [validateRule]
  simp
  rw [List.dropWhile_cons_of_pos, List.dropWhile_cons_of_pos, List.dropWhile_cons_of_pos, List.dropWhile_cons_of_neg]
  . simp
    apply And.intro
    case left => exact hab
    case right => exact hac3
  . simp
  . simp; exact hbc2.symm
  . simp; exact hab
  . simp; exact hbc1.symm
theorem validateRule_neg (hbc1 : b ≠ c1): (validateRule (a, b) { l:= [c1, b, c2, a, c3], nonempty } = False) := by
  rw [validateRule]
  simp
  rw [List.dropWhile_cons_of_pos, List.dropWhile_cons_of_neg]
  simp
  . simp
  . simp; exact hbc1.symm

theorem middleIndexValid (xs: List α) (nonempty : xs.length > 0) : List.length xs / 2 < List.length xs := Nat.div_lt_self nonempty (by simp)
def validateRules (r: List Rule) (p: Pages): Bool := r.all (validateRule · p)

def sumMiddleNums (p: List Pages): Nat :=
  List.sum (p.map (fun ps => ps.l[ps.l.length / 2]'(Nat.div_lt_self ps.nonempty (by simp))))
def aoc5_1 (r: List Rule) (p: List Pages): Nat := sumMiddleNums (p.filter (validateRules r ·))
#eval aoc5_1.uncurry (parseInput data)

def fixRules (r: List Rule) (p: Pages): Pages :=
  { l := p.l.mergeSort (fun x y => r.contains (x, y) ∧ ¬r.contains (y, x)), nonempty := by rw [List.length_mergeSort]; exact p.nonempty }

def aoc5_2 (r: List Rule) (p: List Pages): Nat := sumMiddleNums ((p.filter (¬validateRules r ·)).map (fixRules r ·))
#eval aoc5_2.uncurry (parseInput data)
