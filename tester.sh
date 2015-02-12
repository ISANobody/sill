# Must be used from src directory
# cd's into test dir and then runs all tests comaparing output
# If given a particular file the testing function only on that file

basictest () {
  if [ -e $1.parse ]
  then
    echo $1 parsing
    sill -parseonly $I 2>&1 | diff -q - $I.parse || exit 1
  fi
  if [ -e $I.output ]
  then
    echo $1 outputing
    sill $1 2>&1 | diff -q - $1.output || exit 1
  fi
  if [ -e $1.interp ]
  then
    echo $1 interpreting
    sill -evaltrace $1 2>&1 | diff -q - $1.interp || exit 1
  fi
}

if [[ -n $1 ]]
then 
  basictest $1
  exit 0
fi

cd tests || exit 1
for I in *.sill
do
  basictest $I
done
cd .. || exit 1

echo "Checking parser errors"
./errortester.sh tests/parseerrors

echo "Checking type errors"
./errortester.sh tests/typeerrors
