import Init.Data.Array.Basic
import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic
import MergeSort.USize.Extras

set_option trace.compiler.ir.result true

def foo (u : USize) (_h : u < 100) : USize := u
def bar (u : USize) : USize := u

namespace PrototypeA

variable
  {α : Type}
  {arr aux : Array α}
  {low mid high ptr₁ ptr₂ i chunkSize : USize}

@[specialize, inline]
partial def mergeAdjacentChunksIntoAux
    [Ord α]
    (arr aux : Array α)
    (low mid high : USize)
    : Array α :=
  let rec @[specialize] loop
      (aux : Array α)
      (ptr₁ ptr₂ i : USize)
      : Array α :=
    if ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high then
      match Ord.compare (arr[ptr₁]'sorry) (arr[ptr₂]'sorry) with
      | .lt | .eq =>
        let aux' := aux.uset i (arr[ptr₁]'sorry) sorry
        loop aux' ptr₁.succ ptr₂ i.succ
      | .gt =>
        let aux' := aux.uset i (arr[ptr₂]'sorry) sorry
        loop aux' ptr₁ ptr₂.succ i.succ
    else
      let rec @[specialize] loopLeft
          (aux : Array α)
          (ptr₁ i : USize)
          : Array α :=
        if ptr₁_lt_mid : ptr₁ < mid then
          let aux' := aux.uset i (arr[ptr₁]'sorry) sorry
          loopLeft aux' ptr₁.succ i.succ
        else
          let rec @[specialize] loopRight
              (aux : Array α)
              (ptr₂ i : USize)
              : Array α :=
            if ptr₂_lt_high : ptr₂ < high then
              let aux' := aux.uset i (arr[ptr₂]'sorry) sorry
              loopRight aux' ptr₂.succ i.succ
            else
              aux
          loopRight aux ptr₂ i
      loopLeft aux ptr₁ i
  loop aux (ptr₁ := low) (ptr₂ := mid) (i := low)

@[specialize, inline]
partial def mergeChunksIntoAux
    [Ord α]
    (arr aux : Array α)
    (chunkSize : USize)
    : Array α :=
  let rec @[specialize] loop
      (aux : Array α)
      (low : USize)
      : Array α :=
    if size_minus_low_gt_chunkSize : chunkSize < arr.usize - low then
      let mid := low + chunkSize
      let high := mid + min (arr.usize - mid) chunkSize
      let aux' := mergeAdjacentChunksIntoAux arr aux low mid high
      loop aux' high
    else
      let rec @[specialize] loopFinal
          (aux : Array α)
          (low : USize)
          : Array α :=
        if low_lt_aux_usize : low < aux.usize then
          let aux' := aux.uset low (arr[low]'sorry) sorry
          loopFinal aux' low.succ
        else
          aux
      loopFinal aux low
  loop aux 0

@[specialize, inline]
partial def Array.mergeSortWithAuxiliary
    [Ord α]
    (arr aux : Array α)
    (_size_eq : arr.size = aux.size)
    (_arr_size_lt_usize_size : arr.size < USize.size)
    : Array α :=
  let rec @[specialize] loop
      (arr aux : Array α)
      (chunkSize : USize)
      : Array α :=
    if _chunkSize_lt_arr_usize : chunkSize < arr.usize then
      let aux' := mergeChunksIntoAux arr aux chunkSize
      let chunkSize' := chunkSize + min (arr.usize - chunkSize) chunkSize
      loop aux' arr chunkSize'
    else
      arr
  loop arr aux 1

@[specialize, inline]
def Array.mergeSort
    [Inhabited α]
    [Ord α]
    (arr : Array α)
    (arr_size_lt_usize_size : arr.size < USize.size)
    : Array α :=
  let aux := .replicate arr.size default
  have size_eq := Eq.symm Array.size_replicate
  mergeSortWithAuxiliary arr aux size_eq arr_size_lt_usize_size

end PrototypeA
