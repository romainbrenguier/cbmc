#!/bin/sh

echo "This script extracts some parts of java files that could be "
echo "interesting for security analysis"
echo "usage ./test.sh DIRECTORY"
DIR=$1
echo "analysing directory " $DIR
echo "############################################################"
#echo "------ Interesting function calls in java file ------"
for i in $(find $DIR -name *.java)
do
    grep -n -H -e "HttpServlet" $i;
    #grep -H -n -e addIntHeader -e addHeader -e addDateHeader -e addCookie -e setHeader -e getWriter -e getOutputStream $i;
done

echo "############################################################"
echo "------ Looking into jar files ------"

for i in $(find $DIR -name *.jar)
do
    java -cp java-analysis/target/java-analysis-1.0-SNAPSHOT.jar com.DiffBlue.app.ListInterfaces $i HttpServlet
    cat classes.txt >>$DIR/classes_implementing_servlet.txt
    rm classes.txt
done


