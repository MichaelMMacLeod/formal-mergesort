import MergeSort.Implementation
import MergeSort.ArrayGenerators
import MergeSort.PrototypeA

-- set_option trace.compiler.ir.result true

def benchmark
    {data₁ data₂}
    (makeArray : Unit → Array Nat)
    (prepare : Array Nat → data₁)
    (go : data₁ → data₂)
    (finish : data₂ → Nat)
    : IO (Nat × Nat) := do
  let data := prepare <| makeArray ()
  let start ← IO.monoNanosNow
  let result := go data
  let elapsed := (← IO.monoNanosNow) - start
  let optimizationPreventionValue := finish result
  pure (elapsed, optimizationPreventionValue)

def Benchmark.Array.mergeSortGeneric
    (algo : (arr : Array Nat) → arr.size < USize.size → Array Nat)
    (makeArray : Unit → Array Nat)
    : IO (Nat × Nat) :=
  benchmark makeArray prepare go finish
where
  prepare (arr : Array Nat) : Unit → Array Nat :=
    if h : arr.size < USize.size then
        fun () => algo arr h
      else
        panic! "arr ≥ USize.size"
  go := (· ())
  finish (arr : Array Nat) : Nat :=
    match arr[0]? with
    | .none => 0
    | .some v => v

def Benchmark.Array.mergeSort (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  Benchmark.Array.mergeSortGeneric _root_.Array.mergeSort makeArray

def Benchmark.Array.mergeSortA (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  Benchmark.Array.mergeSortGeneric _root_.PrototypeA.Array.mergeSort makeArray

def Benchmark.Array.qsortOrd (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  benchmark makeArray prepare go finish
where
  prepare (arr : Array Nat) : Array Nat := arr
  go arr := arr.qsortOrd
  finish (arr : Array Nat) : Nat :=
    match arr[0]? with
    | .none => 0
    | .some v => v

def Benchmark.List.mergeSort (makeArray : Unit → Array Nat) : IO (Nat × Nat) :=
  benchmark makeArray prepare go finish
where
  prepare (arr : Array Nat) : List Nat := arr.toList
  go (lst : List Nat) : List Nat := lst.mergeSort
  finish (lst : List Nat) : Nat :=
    match lst[0]? with
    | .none => 0
    | .some v => v

def Nat.nsToMs (ns : Nat) : Nat := ns / 10 ^ 6
def Nat.msToS (ms : Nat) : Nat := ms / 10 ^ 3

def runOnAllArrayGenerators
    (algoName : String)
    (size : Nat)
    (seed : Nat)
    (go : (Unit → Array Nat) → IO (Nat × Nat))
    : IO Unit := do
  let printResult (fnName : String) (fn : Unit → Array Nat) : IO Unit := do
    let (time, opv) ← go fn
    println! s!"{opv} → {time.nsToMs.msToS}s\t\t{time.nsToMs}ms\t\t{time}ns\t\t{fnName}"
  println! s!"Testing {algoName} using (size := {size}) (seed := {seed})"
  printResult "mostlyAscending" fun () => Array.mostlyAscending size seed
  printResult "randomWithDuplicates" fun () => Array.randomWithDuplicates size seed
  printResult "random" fun () => Array.random size seed
  printResult "ascending" fun () => Array.ascending size
  printResult "descending" fun () => Array.descending size
  printResult "ascendingWithRandomTail" fun () => Array.ascendingWithRandomTail size seed

#check Array.uget
