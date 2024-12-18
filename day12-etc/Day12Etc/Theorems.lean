theorem sub_one_still_lt (h: a < b): a - 1 < b := Nat.lt_of_le_of_lt (Nat.sub_le a 1) h
