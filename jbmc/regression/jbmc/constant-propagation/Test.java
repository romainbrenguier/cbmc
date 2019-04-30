public class Test {

  public String checkPass() {
    String string = "vVvvVvvVv";
    int[] array = new int[4];
    if(array.length == 4)
    {
      String result = string.toLowerCase();
      assert(result.charAt(0) == 'v');
      return result;
    }
    else
    {
      String result = string.toUpperCase();
      assert(result.charAt(0) == 'V');
      return result;
    }
  }

  static public String checkPass1() {
    int[] array = new int[1];
    array[0] = 23;
    if(array[0] == 92)
    {
      String result = "vVvvVvvVv".toLowerCase();
      assert(result.charAt(0) == 'v');
      return result;
    }
    else
    {
      String result = "vVvvVvvVv".toUpperCase();
      assert(result.charAt(0) == 'V');
      return result;
    }
  }

}
