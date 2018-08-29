// This test uses CProverString so should be compiled with
// javac Test.java ../cprover/CProverString.java

class TestBuiltin {
    public String check1arg(String s, int nondet) {
        // Arrange
        StringBuffer buffer = new StringBuffer();
        for(int i = 0; i < 90; i++) {
            buffer.append('+');
        }
        buffer.append('-');
        buffer.append(s);
        String t = buffer.toString();

        // Act
        for(int i = 0; i < 90; i++) {
            t = org.cprover.CProverString.substring(t, 1);
        }

        // Assert
        if(nondet == 0) {
            assert t.length() == s.length() + 1;
        } else {
            assert t.length() != s.length() + 1;
        }
        return t;
    }

    public String check2args(String s, int nondet) {
        // Arrange
        StringBuffer buffer = new StringBuffer();
        for(int i = 0; i < 90; i++) {
            buffer.append('+');
        }
        buffer.append('-');
        buffer.append(s);
        for(int i = 0; i < 90; i++) {
            buffer.append('+');
        }
        String t = buffer.toString();

        // Act
        for(int i = 0; i < 90; i++) {
            t = org.cprover.CProverString.substring(t, 1, t.length() - 1);
        }

        // Assert
        if(nondet == 0) {
            assert t.length() == s.length() + 1;
        } else {
            assert t.length() != s.length() + 1;
        }
        return t;
    }
}
