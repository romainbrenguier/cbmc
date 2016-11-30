#!/bin/sh

DIR=$1
echo "############################################################"
echo "------ Looking into jar files ------"

rm $DIR/classes_implementing_servlet.txt

for i in $(find $DIR -name *.jar)
do

    java -jar ~/git/test/java-callgraph/target/javacg-0.1-SNAPSHOT-static.jar $i 
done




