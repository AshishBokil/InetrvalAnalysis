#!/usr/bin/env bash

set -e

#export CLASSPATH=.:pkgs/soot-4.3.0-with-deps.jar

echo === building targets

cd target1-pub;   javac -g *.java;  cd ..
cd target2-mine;  javac -g *.java;  cd ..
cd target3-priv;  javac -g *.java;  cd ..
cd target3B-priv;  javac -g *.java;  cd ..
cd target1B-pub;   javac -g *.java;  cd ..
cd target4-pub;  javac -g *.java;  cd ..
cd target5-mine; javac -g *.java; cd ..




