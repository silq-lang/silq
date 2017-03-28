#!/bin/bash
if [ ! -d dmd2 ]; then
    if [[ "$OSTYPE" == "linux-gnu" ]]; then
        FILE="dmd.2.072.2.linux.zip"
        SUM1="c6dc5df0eeac35d37db167b9a80eb08e  $FILE"
        ZIPLINK="http://downloads.dlang.org/releases/2.x/2.072.2/$FILE"
        MD5="md5sum"
    elif [[ "$OSTYPE" == "darwin"* ]]; then
        FILE="dmd.2.072.2.osx.zip"
        SUM1="MD5 ($FILE) = 0844f3218043a21dcc7a3fc76605af5d"
        ZIPLINK="http://downloads.dlang.org/releases/2.x/2.072.2/$FILE"
        MD5="md5"
    else
	>&2 echo "This script does not support your platform at this time."
	>&2 echo "Try to obtain the dmd d compiler manually from:"
	>&2 echo "https://dlang.org"
	>&2 echo "Pull requests for improved build script welcome."
	exit(1);
    fi

    wget $ZIPLINK
    SUM2=`$MD5 $FILE`

    if [[ $SUM1 != $SUM2 ]]; then
	echo "ERROR: md5 sum mismatch"
    else
	unzip $FILE
    fi
fi
