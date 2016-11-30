#!/bin/sh

DIR=$1
echo "############################################################"
echo "------ Looking into jar files ------"

for i in $(find $DIR -name *.jar)
do

    java -jar ~/git/test/java-callgraph/target/javacg-0.1-SNAPSHOT-static.jar $i 
done




