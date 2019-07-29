class Bar {
  public Object bar(int j) {
    MyList to_return0;
    to_return0 = org.cprover.CProver.nondetWithoutNull(new MyList());
    Integer to_return1;
    to_return1 = org.cprover.CProver.nondetWithoutNull(new Integer(0));
    Object to_return;
    if(j == 1) {
      to_return = to_return0;
    } else {
      to_return = to_return1;
    }
    return to_return;    
  }
}
