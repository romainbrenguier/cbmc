package com.DiffBlue.app;
import java.lang.reflect.*;
import java.util.*;
import java.util.jar.*;
import java.net.*;
import javax.servlet.ServletException;
import javax.servlet.http.*;
import java.io.PrintWriter;


/**
 * Look for methods in a class or a jar file
 *
 */
public class ListInterfaces
{

    public static void methodsOfClass (PrintWriter class_writer, Class c, String interface_name) throws ClassNotFoundException 
    {
	
	Class[] interfaces =  c.getInterfaces();
	for(int i = 0; i < Array.getLength(interfaces); i++)
	    if(interfaces[i].getName() == interface_name)
		{
		    System.out.println( "class "+c.getName() + " implements : "+interfaces[i].getName());
		    class_writer.println(c.getName());
		}
	    else if(interfaces[i].getName().contains(interface_name))
		{
		    System.out.println("class "+c.getName() + " implements : "+interfaces[i].getName());
		    System.out.println("(this is not an exact match so we do not include it in the class list)");
		}
		    
    }
    
    public static void main( String[] args )
    {

	try
	    {
		if(args.length == 0)
		    System.out.println( "usage: java -cp target/java-analysis-1.0-SNAPSHOT.jar com.DiffBlue.app.ListInterfaces my.project.prefix");

		String interface_name = "";
		if(args.length>1)
		    interface_name = args[1];

		PrintWriter class_writer = new PrintWriter("classes.txt", "UTF-8");
		PrintWriter additional_class_writer = new PrintWriter("classes2.txt", "UTF-8");
		System.out.println("Writing list of classes to classes.txt and candidates to classes2.txt");
		
		
		if(args[0].endsWith(".jar"))
		    {
			String pathToJar = args[0];
			System.out.println( "Opening jar file: "+pathToJar);
			JarFile jarFile = new JarFile(pathToJar);
			Enumeration<JarEntry> e = jarFile.entries();

			URL[] urls = { new URL("jar:file:" + pathToJar+"!/") , new URL("file:///usr/share/maven-repo/javax/servlet/servlet-api/2.5/servlet-api-2.5.jar")}; 
			URLClassLoader cl = URLClassLoader.newInstance(urls);
			cl.loadClass("javax.servlet.http.HttpServlet");
			//cl.loadClass("HttpServlet");

			    
			while (e.hasMoreElements())
			    {

				JarEntry je = e.nextElement();
				if(je.isDirectory() || !je.getName().endsWith(".class")){
				    continue;
				}
				// -6 because of .class
				String className = je.getName().substring(0,je.getName().length()-6);
				className = className.replace('/', '.');
				
				try
				    {
					Class c = cl.loadClass(className);
					methodsOfClass(class_writer,c,interface_name);
				    }
				catch (Throwable exc)
				    {
					String failed_class_name = exc.toString();
					if(failed_class_name.contains(interface_name))
					    {
						System.out.println("class " + className + " may implement " + interface_name + "("+exc+")");
						additional_class_writer.println(className);
					    }
				    }
			    }


			
		    }
		else
		    {
			System.out.println( "Looking into class: "+args[0]);
			Class c = Class.forName(args[0]);
			methodsOfClass(class_writer,c,interface_name);
			
		    }
		class_writer.close();
		additional_class_writer.close();
	    }
	catch (Throwable e1)
	    {
		System.err.println(e1);
	    }


    }
}
