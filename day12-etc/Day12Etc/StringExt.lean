def String.splitOnce (s: String) (delim: String): Option (String × String) :=
  match s.splitOn delim with
  | [a, b] => some (a, b)
  | _ => none
