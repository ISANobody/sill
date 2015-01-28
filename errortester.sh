#!/usr/bin/env bash
cat "$1" | (
  PROG="";
  ERRR="";
  OUTP="";
  N=1;
  PROGN=1;
  while IFS='' read -r line;
  do
    N=$((N+1));
    if [ "$line" == '%%%%' ];
    then
      while IFS='' read -r line;
      do
        N=$((N+1));
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
      OUTP=$(set -f; echo "${PROG}" | sill - 2>&1);
      OUTP+="
";
      if [ "$OUTP" != "$ERRR" ];
      then
        echo "Program starting on line $PROGN:";
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
      PROGN="$N";
    else
# silly but gets newlines correct
      PROG+="$line
";
    fi;
  done;
)
