#!/usr/bin/env bash

set -e

## ./run-analysis-one.sh  <Dir>  <MainClass>  <TargetClass>  <TargetMethod>


#./run-analysis-one.sh "./target1-pub" "AddNumbers"  "AddNumbers"  "main"
#./run-analysis-one.sh "./target1-pub" "AddNumFun"   "AddNumFun"   "expr"


# XXX you can add / delete / comment / uncomment lines below
# ./run-analysis-one.sh "./target1-pub" "BasicTest1"   "BasicTest1"   "myIncrement"
# ./run-analysis-one.sh "./target1-pub" "BasicTest1"   "BasicTest1"   "mySum"
# ./run-analysis-one.sh "./target1-pub" "BasicTest1"   "BasicTest1"   "add_x"
# ./run-analysis-one.sh "./target1-pub" "BasicTest1"   "BasicTest1"   "myChoose"

#  ./run-analysis-one.sh "./target2-mine" "MyTargetClass1"   "MyTargetClass1"   "test1"
#  ./run-analysis-one.sh "./target2-mine" "MyTargetClass1"   "MyTargetClass1"   "test2"
#  ./run-analysis-one.sh "./target2-mine" "MyTargetClass1"   "MyTargetClass1"   "test3"
#  ./run-analysis-one.sh "./target2-mine" "MyTargetClass1"   "MyTargetClass1"   "test4"

# ./run-analysis-one.sh "./target3B-priv" "PVTTests"   "PVTTests"   "pvttest1"
# ./run-analysis-one.sh "./target3B-priv" "PVTTests"   "PVTTests"   "pvttest2"
## phase2 inter-procedural analysis
 ./run-analysis-one.sh "./target4-pub" "PubTest5"   "PubTest5"   "main"
# ./run-analysis-one.sh "./target5-mine" "MineTest5"   "MineTest5"   "main"

