-- import «LeanSorting».Total
import LeanSorting.PartialFin
import LeanSorting.PartialFinUnsafe
import LeanSorting.PartialUSizeUnsafe

-- def String.splitByLines (s : String) : Array String :=
--   s.split (· == '\n') |>.toArray

#check String.get
#check String.push
#check Lean.TraceData
#check IO.FS.SystemTime.nsec

-- def String.toInt

def main : List String → IO UInt32
  | "--algorithm" :: algorithm :: "--file" :: file :: [] => do
    let lines : Array String ← IO.FS.lines file
    -- let lines : Array UInt64 :=
    --   let nats := (← IO.FS.lines ⟨file⟩).map fun str =>
    --     let nat := str.toNat!
    --     UInt64.ofNat nat
    --   nats
    let start ← IO.monoMsNow
    match algorithm with
    -- | "Array.mergeSort" => sorry
    | "Array.qsortOrd" =>
      let mut sum := 0
      for line in lines.qsortOrd do
        sum := sum + line.length
      println! "sum = {sum}"
    | "Array.mergeSortPartialFin" =>
      let mut sum := 0
      for line in lines.mergeSortPartialFin do
        sum := sum + line.length
      println! "sum = {sum}"
    | "Array.mergeSortPartialFinUnsafe" =>
      let mut sum := 0
      for line in lines.mergeSortPartialFinUnsafe do
        sum := sum + line.length
      println! "sum = {sum}"
    | "Array.mergeSortPartialUSizeUnsafe" =>
      let mut sum := 0
      for line in lines.mergeSortPartialUSizeUnsafe do
        sum := sum + line.length
      println! "sum = {sum}"
    | _ =>
      println! "unknown algorithm: {algorithm}"
      return 1
    let endTime ← IO.monoMsNow
    let elapsed := endTime - start
    println! "elapsed = {elapsed}"
    pure 0
  | _ => do
    println! "Usage: --algorithm <ALGO> --file <FILE>"
    pure 1
