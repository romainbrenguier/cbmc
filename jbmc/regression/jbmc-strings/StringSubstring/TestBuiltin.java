// This test uses CProverString so should be compiled with
// javac Test.java ../cprover/CProverString.java

class TestBuiltin {
    public String det1arg(int nondet) {
        // Arrange
        StringBuffer buffer = new StringBuffer();
        for(int i = 0; i < 90; i++) {
            buffer.append('+');
        }
        buffer.append('-');
        String s = buffer.toString();

        // Act
        for(int i = 0; i < 90; i++) {
            s = org.cprover.CProverString.substring(s, 1);
        }

        // Assert
        if(nondet == 0) {
            assert s.length() == 1;
        } else {
            assert s.length() != 1;
        }
        return s;
    }

    public String nondet1arg(String s, int nondet) {
	// Filter
	if (s == null || s.length() < 100) {
	    return "short string";
	}

        // Act
	String t = s;
        for(int i = 0; i < 90; i++) {
            t = org.cprover.CProverString.substring(t, 1);
        }

        // Assert
        if(nondet == 0) {
            assert t.length() == s.length() - 90;
        } else {
            assert t.length() != s.length() - 90;
        }
        return t;
    }

    public String det2args(int nondet) {
        // Arrange
        StringBuffer buffer = new StringBuffer();
        for(int i = 0; i < 90; i++) {
            buffer.append('+');
        }
        buffer.append('-');
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
            assert t.length() == 1;
        } else {
            assert t.length() != 1;
        }
        return t;
    }

    public String nondet2args(String s, int nondet) {
	// Filter
	if (s == null || s.length() < 200) {
	    return "short string";
	}

        // Act
	String t = s;
        for(int i = 0; i < 90; i++) {
            t = org.cprover.CProverString.substring(t, 1, t.length() - 1);
        }

        // Assert
        if(nondet == 0) {
            assert t.length() == s.length() - 180;
        } else {
            assert t.length() != s.length() - 180;
        }
        return t;
    }

}
