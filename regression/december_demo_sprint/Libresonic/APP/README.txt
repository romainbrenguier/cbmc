Libresonic
~~~~~~~~~~
Libresonic is a free, web-based media streamer, providing ubiqutious access to music.
Can be used to share music with friends, or to listen to your own music while at work.

91 commits
2 branches
4 releases
12 contributors
GPL-3.0

Website: http://libresonic.org
Repository: https://github.com/Libresonic/libresonic
Note: We use our own fork in which we made some small hacks to accomodate goto-analyzer.
The Hacks are documented at https://github.com/romainbrenguier/libresonic/blob/goto_analyzer_hacks/HACKS.txt

1. Open a terminal in the directory of this readme file and clone:
      git clone https://github.com/romainbrenguier/libresonic
2. Rename the created directory "libresonic" to "Libresonic"
3. Enter the directory "Libresonic" and type there the following:
      git checkout goto_analyzer_hacks
      mvn clean package
4. Copy the resulting files to ../BENCHMARK (relative path to this README.txt
   file):
      cd .. 
      python ./copy_binaries.py


To run goto-analyser on this benchmark, go to goto-analyzer directory
and use the following command line:
python run.py -E ../Libresonic/ --use-pruned-rt --debug --dump-program \
 --dump-html-summaries --dump-html-traces --rebuild
It should give at least one trace with taint issue. It corresponds to a
request parameter being directly used in a request to the database.
