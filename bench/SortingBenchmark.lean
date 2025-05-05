-- import SortingBenchmark.Benchmark

import SortingBenchmark.ArrayGenerators

def main : IO Unit := do
  println! "Hello, world!"

-- def main : IO Unit := do
--   let size := 10 ^ 6
--   let seed := 0
--   runOnAllArrayGenerators "Array.mergeSort" size seed Benchmark.Array.mergeSort
--   runOnAllArrayGenerators "Array.qsortOrd" size seed Benchmark.Array.qsortOrd
--   runOnAllArrayGenerators "List.mergeSort" size seed Benchmark.List.mergeSort
