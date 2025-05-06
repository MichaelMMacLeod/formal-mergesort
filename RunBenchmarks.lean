import MergeSort.Benchmark
import MergeSort.ArrayGenerators

def main (args :  List String) : IO Unit := do
  let size := 10 ^ 9
  let seed := 0
  match args with
  | ["mergeSort"] =>
    runOnAllArrayGenerators "Array.mergeSort" size seed Benchmark.Array.mergeSort
  | ["mergeSortA"] =>
    runOnAllArrayGenerators "Array.mergeSortA" size seed Benchmark.Array.mergeSortA
  | _ => panic! "wrong arguments"
  -- runOnAllArrayGenerators "List.mergeSort" size seed Benchmark.List.mergeSort
  -- runOnAllArrayGenerators "Array.qsortOrd" size seed Benchmark.Array.qsortOrd

#check Std.Tactic.BVDecide.LRAT.Internal.DefaultFormula.confirmRupHint
