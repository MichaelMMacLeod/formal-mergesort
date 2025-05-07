import MergeSort.Benchmark
import MergeSort.ArrayGenerators

def main (args :  List String) : IO Unit := do
  let size := 5 * 10 ^ 7
  let seed := 0
  -- match args with
  -- | ["mergeSort"] =>
  --   runOnAllArrayGenerators "Array.mergeSort" size seed Benchmark.Array.mergeSort
  -- | ["mergeSortA"] =>
  --   runOnAllArrayGenerators "Array.mergeSortA" size seed Benchmark.Array.mergeSortA
  -- | _ => panic! "wrong arguments"
  runOnAllArrayGenerators "safe merge sort" size seed Benchmark.Array.mergeSort
  runOnAllArrayGenerators "unsafe merge sort" size seed Benchmark.Array.mergeSortA
  -- runOnAllArrayGenerators "List.mergeSort" size seed Benchmark.List.mergeSort
  -- runOnAllArrayGenerators "Array.qsortOrd" size seed Benchmark.Array.qsortOrd

#check Std.Tactic.BVDecide.LRAT.Internal.DefaultFormula.confirmRupHint
