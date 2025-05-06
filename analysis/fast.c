LEAN_EXPORT lean_object* l_Benchmark_Array_mergeSortA(lean_object* x_1, lean_object* x_2) {
 _start:
  {
    lean_object* x_3; lean_object* x_4; lean_object* x_5; 
    x_3 = l_instInhabitedNat;
    x_4 = lean_alloc_closure((void*)(l_PrototypeA_Array_mergeSort___at_Benchmark_Array_mergeSortA___spec__1), 3, 1);
    lean_closure_set(x_4, 0, x_3);
    x_5 = l_Benchmark_Array_mergeSortGeneric(x_4, x_1, x_2);
    return x_5;
  }
}

LEAN_EXPORT lean_object* l_PrototypeA_Array_mergeSort___at_Benchmark_Array_mergeSortA___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
 _start:
  {
    lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; 
    x_4 = lean_array_get_size(x_2);
    x_5 = lean_mk_array(x_4, x_1);
    x_6 = 1;
    x_7 = l_PrototypeA_Array_mergeSortWithAuxiliary_loop___at_Benchmark_Array_mergeSortA___spec__2(x_2, x_5, x_6);
    return x_7;
  }
}

LEAN_EXPORT lean_object* l_PrototypeA_Array_mergeSortWithAuxiliary_loop___at_Benchmark_Array_mergeSortA___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3) {
 _start:
  {
    size_t x_4; uint8_t x_5; 
    x_4 = lean_array_size(x_1);
    x_5 = lean_usize_dec_lt(x_3, x_4);
    if (x_5 == 0)
      {
        lean_dec(x_2);
        return x_1;
      }
    else
      {
        size_t x_6; lean_object* x_7; size_t x_8; uint8_t x_9; 
        x_6 = 0;
        x_7 = l_PrototypeA_mergeChunksIntoAux_loop___at_Benchmark_Array_mergeSortA___spec__3(x_1, x_3, x_2, x_6);
        x_8 = lean_usize_sub(x_4, x_3);
        x_9 = lean_usize_dec_le(x_8, x_3);
        if (x_9 == 0)
          {
            size_t x_10; 
            x_10 = lean_usize_add(x_3, x_3);
            {
              lean_object* _tmp_0 = x_7;
              lean_object* _tmp_1 = x_1;
              size_t _tmp_2 = x_10;
              x_1 = _tmp_0;
              x_2 = _tmp_1;
              x_3 = _tmp_2;
            }
            goto _start;
          }
        else
          {
            size_t x_12; 
            x_12 = lean_usize_add(x_3, x_8);
            {
              lean_object* _tmp_0 = x_7;
              lean_object* _tmp_1 = x_1;
              size_t _tmp_2 = x_12;
              x_1 = _tmp_0;
              x_2 = _tmp_1;
              x_3 = _tmp_2;
            }
            goto _start;
          }
      }
  }
}

