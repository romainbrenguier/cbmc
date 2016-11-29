
Building
========

mvn clean package

Usage
=====

Listing methods of a class, example:
> java -cp target/java-analysis-1.0-SNAPSHOT.jar com.DiffBlue.app.ListMethods java.util.Stack

Listing methods of a jar file, example:
> java -cp target/java-analysis-1.0-SNAPSHOT.jar com.DiffBlue.app.ListMethods ../TOY_APPS/mediaManager/BENCHMARK/mediaManager-1.0-SNAPSHOT.jar

Listing interfaces implemented by a jar file, example:
> java -cp target/java-analysis-1.0-SNAPSHOT.jar com.DiffBlue.app.ListInterfaces ../TOY_APPS/mediaManager/BENCHMARK/mediaManager-1.0-SNAPSHOT.jar



