#!/bin/bash

if [ $# != 2 ]; then
    echo "sortdiff file1 file2"
fi

sort $1 > $1.sorted
sort $2 > $2.sorted
diff $1.sorted $2.sorted
/bin/rm $1.sorted $2.sorted
