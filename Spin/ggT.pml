proctype ggT(int a; int b; chan p) {
  /*communicating via message to parent*/
  int result;
  chan child = [1] of { int };
  
  if
    :: b == 0 -> p!a
    :: b != 0 -> if
      :: a % b == 0 -> p!b
      :: else -> run ggT(b, a % b, child);
          child?result; p!result /*communicating the result*/
    fi
  fi
}

init {
  chan child = [1] of { int };
  int result;
  chan child1 = [1] of { int };
  int result1;
  int a, b;
  select (a : 0 .. 25);
  select (b : 0 .. 25);
  run ggT(a, b, child);
  child?result;
  
  run ggT(b, a, child1);
  child1?result1;
  assert(result == result1);

  if
    :: a >= b -> run ggT(a - b, b, child1); child1?result1;
       assert(result == result1);
  fi
}
