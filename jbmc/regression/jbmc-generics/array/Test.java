class Generic<T> {
    public T field;
    public Generic(T fieldParam) {
        field = fieldParam;
    }
}

class IntWrapper {
  public int i0;
    public IntWrapper(int intParam) {
    i0 = intParam;
  }
}

public class Test {
    public static int test(Generic<IntWrapper[]> arrayInput, boolean triggerAssertion) {
        if (arrayInput != null
            && arrayInput.field != null
            && arrayInput.field.length > 0
            && arrayInput.field[0] != null) {
            assert(!triggerAssertion);
            return arrayInput.field[0].i0;
        } else {
            return -1;
        }
    }
}
