package com.DiffBlue.app;
import java.lang.reflect.*;
import java.util.*;
import java.util.jar.*;
import java.net.*;

/**
 * Look for methods in a class or a jar file
 *
 */
public class ListInterfaces
{

    public static void methodsOfClass (Class c) throws ClassNotFoundException 
    {
	
	Class[] interfaces =  c.getInterfaces();
	for(int i = 0; i < Array.getLength(interfaces); i++)
	    System.out.println( "class "+c.getName() + "implements : "+interfaces[i].getName());
    }
    
    public static void main( String[] args )
    {

	try
	    {
		System.out.println( "usage: java -cp target/java-analysis-1.0-SNAPSHOT.jar com.DiffBlue.app.ListInterfaces my.project.prefix");
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
