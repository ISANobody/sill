# Must be used from src directory
# cd's into test dir and then runs all tests comaparing output
cd tests || exit 1
for I in *.sill
do
  if [ -e $I.parse ]
  then
    echo $I parsing
    sill -parseonly $I 2>&1 | diff -q - $I.parse || exit 1
  fi
  if [ -e $I.interp ]
  then
    echo $I interpreting
    sill -evaltrace $I 2>&1 | diff -q - $I.interp || exit 1
  fi
  if [ -e $I.output ]
  then
    echo $I outputing
    sill $I 2>&1 | diff -q - $I.output || exit 1
  fi
done
cd .. || exit 1

echo "Checking parser errors"
./errortester.sh tests/parseerrors

echo "Checking type errors"
./errortester.sh tests/typeerrors
