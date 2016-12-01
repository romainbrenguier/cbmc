package com.DiffBlue.app;
import java.lang.reflect.*;

/**
 * Look for classes implementing HttpServlet
 *
 */
public class App 
{
    public static void main( String[] args )
    {
        System.out.println( "usage: java -cp target/java-analysis-1.0-SNAPSHOT.jar com.DiffBlue.app.App my.project.prefix");
	System.out.println( "Looking into project: "+args[0]);
	/*
	Reflections reflections = new Reflections(args[1]);
	*/
         try {
            Class c = Class.forName(args[0]);
            Method m[] = c.getDeclaredMethods();
            for (int i = 0; i < m.length; i++)
            System.out.println(m[i].toString());
         }
         catch (Throwable e) {
            System.err.println(e);
         }
    }
}
