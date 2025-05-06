LEAN_EXPORT size_t l_foo(size_t x_1, lean_object* x_2) {
 _start:
  {
    return x_1;
  }
}

LEAN_EXPORT lean_object* l_foo___boxed(lean_object* x_1, lean_object* x_2) {
 _start:
  {
    size_t x_3; size_t x_4; lean_object* x_5; 
    x_3 = lean_unbox_usize(x_1);
    lean_dec(x_1);
    x_4 = l_foo(x_3, x_2);
    x_5 = lean_box_usize(x_4);
    return x_5;
  }
}

LEAN_EXPORT size_t l_bar(size_t x_1) {
 _start:
  {
    return x_1;
  }
}

LEAN_EXPORT lean_object* l_bar___boxed(lean_object* x_1) {
 _start:
  {
    size_t x_2; size_t x_3; lean_object* x_4; 
    x_2 = lean_unbox_usize(x_1);
    lean_dec(x_1);
    x_3 = l_bar(x_2);
    x_4 = lean_box_usize(x_3);
    return x_4;
  }
}
