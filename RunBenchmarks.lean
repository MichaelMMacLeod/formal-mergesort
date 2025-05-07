import MergeSort.Benchmark
import MergeSort.ArrayGenerators

def main (args :  List String) : IO Unit := do
  let size := 10 ^ 5
  let seed := 0
  -- match args with
  -- | ["mergeSort"] =>
  --   runOnAllArrayGenerators "Array.mergeSort" size seed Benchmark.Array.mergeSort
  -- | ["mergeSortA"] =>
  --   runOnAllArrayGenerators "Array.mergeSortA" size seed Benchmark.Array.mergeSortA
  -- | _ => panic! "wrong arguments"
  runOnAllArrayGenerators "custom Array.mergeSort (safe)" size seed Benchmark.Array.mergeSort
  runOnAllArrayGenerators "custom Array.mergeSort (unsafe)" size seed Benchmark.Array.mergeSortA
  runOnAllArrayGenerators "List.mergeSort" size seed Benchmark.List.mergeSort
  runOnAllArrayGenerators "Array.qsortOrd" size seed Benchmark.Array.qsortOrd
