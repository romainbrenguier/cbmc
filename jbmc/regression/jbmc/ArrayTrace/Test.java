import java.io.File;
import java.util.ArrayList;

public class Test {
    public static ArrayList<File> test(ArrayList<File> arrayList, int files, boolean check) {
    if (arrayList == null || arrayList.size() == 0 || arrayList.get(0) == null) {
      return null;
    }
    File f0 = new File("/Poath");
    arrayList.add(f0);
    assert(!check);
    return arrayList;
  }
}
