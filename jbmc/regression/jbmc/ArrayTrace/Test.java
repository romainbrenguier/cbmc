// Interface similar to ArrayList but only for Integer and limited to size 5
class CustomArrayList
{
  int size = 0;
  Integer data[] = new Integer[5];
  public void add(Integer x) { data[size++] = x; }
  public int size() { return size; }
  public Integer get(int i) { return data[i]; }
}

public class Test {
  public static CustomArrayList test(CustomArrayList arrayList, int files, boolean check) {
    if (arrayList == null || arrayList.size() == 0 || arrayList.get(0) == null) {
      return null;
    }
    Integer f0 = new Integer(12);
    arrayList.add(f0);
    assert(!check);
    return arrayList;
  }
}
