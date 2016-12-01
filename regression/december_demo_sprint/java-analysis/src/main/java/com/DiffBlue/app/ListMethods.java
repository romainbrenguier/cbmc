package com.DiffBlue.app;
import java.lang.reflect.*;
import java.util.*;
import java.util.jar.*;
import java.net.*;

/**
 * Look for methods in a class or a jar file
 *
 */
public class ListMethods
{

    public static void methodsOfClass (Class c) throws ClassNotFoundException 
    {
	Method m[] = c.getDeclaredMethods();
	for (int i = 0; i < m.length; i++)
	    System.out.println(m[i].toString());
	
    }

    public static void containsMethod (Class c, String method_name) throws ClassNotFoundException 
    {
	Method m[] = c.getDeclaredMethods();
	for (int i = 0; i < m.length; i++)
	    if(m[i].toString().contains(method_name))
		System.out.println("class "+c.getName()+" contains "+method_name);
	
    }

    
    
    public static void main( String[] args )
    {

	try
	    {
		System.out.println( "usage: java -cp target/java-analysis-1.0-SNAPSHOT.jar com.DiffBlue.app.ListMethods my.project.prefix");
		if(args[0].endsWith(".jar"))
		    {
			String pathToJar = args[0];
			System.out.println( "Opening jar file: "+pathToJar);
			JarFile jarFile = new JarFile(pathToJar);
			Enumeration<JarEntry> e = jarFile.entries();

			URL[] urls = { new URL("jar:file:" + pathToJar+"!/") };
			URLClassLoader cl = URLClassLoader.newInstance(urls);

			while (e.hasMoreElements())
			    {
				
			try
			    {
				JarEntry je = e.nextElement();
				if(je.isDirectory() || !je.getName().endsWith(".class")){
				    continue;
				}
				// -6 because of .class
				String className = je.getName().substring(0,je.getName().length()-6);
				className = className.replace('/', '.');
				System.out.println( "class "+className);
				
				Class c = cl.loadClass(className);
				methodsOfClass(c);
							    }
			catch (Throwable exc)
			    {
				System.err.println(exc);
			    }
			    }


			
		    }
		else
		    {
			System.out.println( "Looking into class: "+args[0]);
			Class c = Class.forName(args[0]);
			methodsOfClass(c);
			
		    }
	    }
	catch (Throwable e1)
	    {
		System.err.println(e1);
	    }


    }
}
