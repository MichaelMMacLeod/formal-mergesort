import Init.Data.Array.Basic
import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic

namespace PrototypeF

variable
  {α : Type}
  {arr aux : Array α}
  {low mid high ptr₁ ptr₂ i chunkSize : Nat}

partial def mergeAdjacentChunksIntoAux
    [Ord α]
    [Inhabited α]
    (arr : Array α)
    (low mid high : Nat)
    (aux : Array α)
    : Array α :=
  let rec loop
      (ptr₁ ptr₂ i : Nat)
      (aux : Array α)
      : Array α :=
    if _ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high then
      match Ord.compare arr[ptr₁]! arr[ptr₂]! with
      | .lt | .eq =>
        let aux' := aux.set! i arr[ptr₁]!
        loop ptr₁.succ ptr₂ i.succ aux'
      | .gt =>
        let aux' := aux.set! i arr[ptr₂]!
        loop ptr₁ ptr₂.succ i.succ aux'
    else
      let rec loopLeft
          (ptr₁ i : Nat)
          (aux : Array α)
          : Array α :=
        if _ptr₁_lt_mid : ptr₁ < mid then
          let aux' := aux.set! i arr[ptr₁]!
          loopLeft ptr₁.succ i.succ aux'
        else
          let rec loopRight
              (ptr₂ i : Nat)
              (aux : Array α)
              : Array α :=
            if _ptr₂_lt_high : ptr₂ < high then
              let aux' := aux.set! i arr[ptr₂]!
              loopRight ptr₂.succ i.succ aux'
            else
              aux
          loopRight ptr₂ i aux
      loopLeft ptr₁ i aux
  loop (ptr₁ := low) (ptr₂ := mid) (i := low) aux

partial def mergeChunksIntoAux
    [Ord α]
    [Inhabited α]
    (arr : Array α)
    (chunkSize : Nat)
    (aux : Array α)
    : Array α :=
  let rec loop
      (low : Nat)
      (aux : Array α)
      : Array α :=
    if _size_minus_low_gt_chunkSize : chunkSize < arr.size - low then
      let mid := low + chunkSize
      let high := mid + min (arr.size - mid) chunkSize
      let aux' := mergeAdjacentChunksIntoAux arr low mid high aux
      loop high aux'
    else
      let rec loopFinal
          (low : Nat)
          (aux : Array α)
          : Array α :=
        if _low_lt_aux_size : low < aux.size then
          let aux' := aux.set! low arr[low]!
          loopFinal low.succ aux'
        else
          aux
      loopFinal low aux
  loop 0 aux

partial def Array.mergeSortWithAuxiliary
    [Ord α]
    [Inhabited α]
    (arr aux : Array α)
    : Array α :=
  let rec loop
      (arr aux : Array α)
      (chunkSize : Nat)
      : Array α :=
    if _chunkSize_lt_arr_Nat : chunkSize < arr.size then
      let aux' := mergeChunksIntoAux arr chunkSize aux
      let chunkSize' := chunkSize + min (arr.size - chunkSize) chunkSize
      loop aux' arr chunkSize'
    else
      arr
  loop arr aux 1

def Array.mergeSort
    [Inhabited α]
    [Ord α]
    (arr : Array α)
    (_arr_size_lt_Nat_size : arr.size < USize.size)
    : Array α :=
  let aux := .replicate arr.size default
  mergeSortWithAuxiliary arr aux

end PrototypeF
