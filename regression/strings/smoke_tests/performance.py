#!/usr/bin/python
from subprocess import check_output

git_output=check_output(["git", "show", "HEAD"])
commit=git_output.split('\n')[0]

commit_id=commit[7:]

process = check_output(["grep", "^Runtime\ decision\ procedure", "-R"])

file_name='performance_'+commit_id+'.out'
print "writing to file", file_name
f=open(file_name, 'w')

for x in process.split('\n'):
    f.write(x+'\n')

f.close()

print "drawing to file", file_name+".png"

gnuplot_output = check_output(["gnuplot", "-e", "file='"+file_name+"'", "-e", "outputfile='"+file_name+".png'", "performance_draw.gp"])

print gnuplot_output

    
