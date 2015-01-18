#!/usr/bin/env bash
cat failures/parseerrors | (
  PROG="";
  while read -r line;
  do
    if [ "$line" == '%%%%' ];
    then
      read -r line;
      ERRR="$line";
      OUTP="$(echo $PROG | sill -parseonly -)";
      if true;
      then
        echo "Program:";
        echo "$PROG"
        echo "";
        echo "Expected output:";
        echo "$ERRR"
        echo "";
        echo "SILL's output:";
        echo "$OUTP"
        exit 1;
      fi
    else
      PROG="$PROG$line";
    fi;
  done;
)
