#!/usr/bin/env bash

set -e

# export CLASSPATH=.:pkgs/soot-4.3.0-20210915.120431-213-jar-with-dependencies.jar
export CLASSPATH=.:pkgs/soot-4.3.0-with-deps.jar


echo === building Lattice.java
javac -g LatticeElement.java
echo === building Analysis.java
javac -g Analysis.java




