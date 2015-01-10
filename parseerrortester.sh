#!/usr/bin/env bash
TMP=`mktemp -d /tmp/sill.parseerrors.XXXXXX`
cat failures/parseerrors | (
  cd $TMP
  I=0;
  echo -n"">file0.sill;
  while read -r line;
  do
    if [ "$line" == '%%%%' ];
    then
      read -r line;
      echo "$line" > file$I.error;
      sill -parseonly file$I.sill &> file$I.output;
      if ! diff -q file$I.output file$I.error;
      then
        echo "Program:";
        cat file$I.sill;
        echo "";
        echo "Expected output:";
        cat file$I.error;
        echo "";
        echo "SILL's output:";
        cat file$I.output;
        exit 1;
      fi
      I=$[I+1];
      echo -n "" > file$I.sill;
    else
      echo "$line" >> file$I.sill;
    fi;
  done;
)
rm -rf $TMP
