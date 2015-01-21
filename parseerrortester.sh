#!/usr/bin/env bash
cat failures/parseerrors | (
  PROG="";
  ERRR="";
  OUTP="";
  while IFS='' read -r line;
  do
    if [ "$line" == '%%%%' ];
    then
      while IFS='' read -r line;
      do
        if [ "$line" == '%%%%' ];
        then 
          break;
        else
# silly but gets newlines correct
          ERRR+="$line
";
        fi;
      done;
# silly but gets newlines correct
      OUTP="$(set -f; echo $PROG | sill -parseonly -)
";
      if [ "$OUTP" != "$ERRR" ];
      then
        echo "Program:";
        echo -n "$PROG"
        echo "";
        echo "Expected output:";
        echo -n "$ERRR"
        echo "";
        echo "SILL's output:";
        echo -n "$OUTP"
        exit 1;
      fi
      PROG="";
      ERRR="";
      OUTP="";
    else
# silly but gets newlines correct
      PROG+="$line
";
    fi;
  done;
)
