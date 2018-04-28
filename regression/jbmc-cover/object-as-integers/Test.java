public class Test {

  public static int check(Object a, Object b) {
    if(a.equals(b))
      return 1;
    return 0;
  }

  public static void main(String args[]) {
    int retval;
    /* Arrange */
     Object arg0a = 1_610_619_925;
     Object arg1a = 1_627_397_141;

     /* Act */
     retval = Test.check(arg0a, arg1a);
     
     /* Assert result */
     System.out.println(retval);
  }
}
