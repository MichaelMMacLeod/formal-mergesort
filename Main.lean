import «LeanSorting».Total

def getLines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do
    -- Drop trailing newline
    lines := lines.push (currLine.dropRight 1)
    currLine ← stdin.getLine
  pure lines

def mainSort (sort : Array String → Array String) : IO Unit := do
  let lines ← getLines
  for line in sort lines do
    IO.println line

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--msort"] => mainSort Array.mergeSort; pure 0
  | ["--msort-partial"] => mainSort Array.mergeSortPartial; pure 0
  | ["--qsort"] => mainSort (Array.qsort · (· < ·)); pure 0
  | _ =>
    IO.println "Expected single argument, either \"--msort\" or \"--qsort\""
    pure 1
