import Day12Etc

def main (args: List String) : IO Unit := do
  match args with
  | "12"::"1"::xs => Day12.main false xs
  | "12"::"2"::xs => Day12.main true xs
  | "15"::"1"::xs => Day15.main false xs
  | "15"::"2"::xs => Day15.main false xs
  | "17"::"1"::xs => Day17.main false xs
  | "17"::"2"::xs => Day17.main false xs
  | _ => IO.println "invalid args"
