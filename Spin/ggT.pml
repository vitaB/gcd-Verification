proctype ggT(int a; int b; chan p) {
  /*communicating via message to parent*/
  int result;
  chan child = [1] of { int };
  
  if
    :: a == 0 -> p!b
    :: b == 0 -> p!a
    :: else -> int rest = 0; if
      :: rest == 0 -> p!b
      :: else -> run ggT(b, rest, child); child?result; p!result /*communicating the result*/
    fi
  fi
}

init {
  chan child = [1] of { int };
  int result;
  
  run ggT(5, 1, child);
  child?result;
  printf("result: %d\n", result);
  //assert(ggT(a,b) = ggT(b,a));
  // zu Beweisen http://de.wikipedia.org/wiki/Gr%C3%B6%C3%9Fter_gemeinsamer_Teiler#Rechenregeln
}
