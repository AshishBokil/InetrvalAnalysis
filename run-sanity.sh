#!/usr/bin/env bash



###########

## check if environ.sh is present
[ -r environ.sh ] ||  "ERROR: environ.sh missing"
[ -r environ.sh ] || exit 1

###########



sanitydir=sanitydir01

rm -rf ./$sanitydir/
mkdir -p ./$sanitydir/

cp target1-pub/BasicTest1.class  $sanitydir/
cp target1-pub/BasicTest1.myIncrement.exp-out.txt  $sanitydir/

./run-analysis-one.sh "./$sanitydir" "BasicTest1"   "BasicTest1"   "myIncrement"
err=$?

[ $err -ne 0 ] && echo "run-analysis FAILED ********************"
[ $err -ne 0 ] && exit 1


[ $err -eq 0 ] && echo "run-analysis PASSED ****"
echo "checking diff"
diff -y  $sanitydir/BasicTest1.myIncrement.exp-out.txt   $sanitydir/BasicTest1.myIncrement.output.txt

err=$?
[ $err -ne 0 ] && echo "diff FAILED ********************"
[ $err -ne 0 ] && exit 1

[ $err -eq 0 ] && echo "diff PASSED ****"

echo "------------------------------------------------------------"
[ $err -ne 0 ] && echo "sanity run FAILED ********************"
[ $err -ne 0 ] && exit 1

[ $err -eq 0 ] && echo "sanity run PASSED ****"
echo "============================================================"

