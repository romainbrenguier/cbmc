public class test_append_char
{
   public static void main(/*String[] args*/)
   {
      Object objectRef = "diff";
      char[] charArray = {'b', 'l', 'u', 'e'};

      StringBuilder buffer = new StringBuilder();

      buffer.append(objectRef)
            .append(charArray);

      String tmp=buffer.toString();
      System.out.println(tmp);
      assert tmp.equals("diffblue");
   }
}
