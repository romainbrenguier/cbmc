abstract class AbstractList {
  int size = 0;
}

class MyList extends AbstractList {
  public int[] elementData;
  public int get(int i) {
    return elementData[i];
  }
}
