import MergeSort.Benchmark
import MergeSort.ArrayGenerators

def main : IO Unit := do
  let size := 10 ^ 6
  let seed := 0
  runOnAllArrayGenerators "List.mergeSort" size seed Benchmark.List.mergeSort
  runOnAllArrayGenerators "Array.qsortOrd" size seed Benchmark.Array.qsortOrd
  runOnAllArrayGenerators "Array.mergeSort" size seed Benchmark.Array.mergeSort
