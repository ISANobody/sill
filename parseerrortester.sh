#!/usr/bin/env bash
cat failures/parseerrors | (
  PROG="";
  ERRR="";
  OUTP="";
  while read -r line;
  do
    if [ "$line" == '%%%%' ];
    then
      while read -r line;
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
      OUTP="$(echo $PROG | sill -parseonly -)
";
      if [ "$OUTP" != "$ERRR" ];
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
