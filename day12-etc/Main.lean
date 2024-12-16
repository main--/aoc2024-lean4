import Day12Etc

def main (args: List String) : IO Unit := do
  match args with
  | "12_1"::xs => Day12.main false xs
  | "12_2"::xs => Day12.main true xs
  | _ => IO.println "invalid args"
