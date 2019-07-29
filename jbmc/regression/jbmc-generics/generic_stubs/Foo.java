
public class Foo {
  Bar b0;
  public String foo(int j1, boolean assertionCheck) {
    MyList i1 = (MyList) b0.bar(j1);
    i1.get(0);
    assert !assertionCheck;
    return "Foo";
  }
}
