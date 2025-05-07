import MergeSort.Benchmark
import MergeSort.ArrayGenerators

def main (args :  List String) : IO Unit := do
  let size := (args[1]!.toNat!) * 10 ^ 5
  let args := [args[0]!]
  let seed := 0
  match args with
  | ["mergeSort"] =>
    runOnAllArrayGenerators "Array.mergeSort" size seed Benchmark.Array.mergeSort
  | ["mergeSortA"] =>
    runOnAllArrayGenerators "Array.mergeSortA" size seed Benchmark.Array.mergeSortA
  | ["mergeSortF"] =>
    runOnAllArrayGenerators "custom Array.mergeSort (safe, runtime bounds checks for get and set, Nat indexing, no @[specialize], no @[inline])" size seed Benchmark.Array.mergeSortF
  | ["mergeSortG"] =>
    runOnAllArrayGenerators "custom Array.mergeSort (safe, runtime bounds checks for get and set, Nat indexing, no @[specialize], no @[inline], Vector instead of Array)" size seed Benchmark.Array.mergeSortG
  | ["mergeSortCA"] =>
    runOnAllArrayGenerators "custom Array.mergeSort (unsafe, Nat indexing)" size seed Benchmark.Array.mergeSortCA
  | ["mergeSortCB"] =>
    runOnAllArrayGenerators "custom Array.mergeSort (unsafe, Nat indexing, Vector instead of Array)" size seed Benchmark.Array.mergeSortCB
  | _ => panic! "wrong arguments"
  -- runOnAllArrayGenerators "custom Array.mergeSort (safe)" size seed Benchmark.Array.mergeSort
  -- runOnAllArrayGenerators "custom Array.mergeSort (unsafe)" size seed Benchmark.Array.mergeSortA
  -- runOnAllArrayGenerators "custom Array.mergeSort (unsafe, runtime bounds checks for get)" size seed Benchmark.Array.mergeSortB
  -- runOnAllArrayGenerators "custom Array.mergeSort (unsafe, runtime bounds checks for get, Nat indexing)" size seed Benchmark.Array.mergeSortC
  -- runOnAllArrayGenerators "custom Array.mergeSort (safe, runtime bounds checks for get and set, Nat indexing)" size seed Benchmark.Array.mergeSortD
  -- runOnAllArrayGenerators "custom Array.mergeSort (safe, runtime bounds checks for get and set, Nat indexing, no @[specialize])" size seed Benchmark.Array.mergeSortE
  -- runOnAllArrayGenerators "custom Array.mergeSort (safe, runtime bounds checks for get and set, Nat indexing, no @[specialize], no @[inline])" size seed Benchmark.Array.mergeSortF
  -- runOnAllArrayGenerators "custom Array.mergeSort (safe, runtime bounds checks for get and set, Nat indexing, no @[specialize], no @[inline], Vector instead of Array)" size seed Benchmark.Array.mergeSortG
  -- runOnAllArrayGenerators "List.mergeSort" size seed Benchmark.List.mergeSort
  -- runOnAllArrayGenerators "Array.qsortOrd" size seed Benchmark.Array.qsortOrd

#eval [9803575,13173475,16727263,7534294,7192289,8288301,9880508,13054881,16856721,7669630,7262968,8655115,9964135,13479072,17413510,7585957,7301790,8294275,9900114,13020534,17018329,7568895,7269453,8270384,9879744,13296087,17075239,7660529,7226910,8286150].sum
#eval [10072860,12928518,17591244,7642970,7821747,8296616,9862712,12909644,17284459,7558239,7828055,8313341,9858577,12919989,17218563,7546957,7835199,8314155,10061523,12934362,17577950,7634167,7830206,8311367,9977425,13251040,17566946,7626766,7795345,8301889].sum
