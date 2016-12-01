#!/bin/sh

echo "Finding java files with requests"
echo "usage ./find_request.sh DIRECTORY"
DIR=$1
echo "analysing directory " $DIR
echo "############################################################"
for i in $(find $DIR -name *.java)
do
    grep -n -H -e "HttpServletResponse" $i;
done

