#!/bin/sh

# remove _CoqProject if it alreqdy exists
[ -e _CoqProject ] && rm _CoqProject

# generate the path for coqide and voqv
for D in $(find * -maxdepth 1 -type d); do
	echo "-Q $D Reciprocity.$D" | sed 's/\//./2'>> _CoqProject
done

echo "" >> _CoqProject

# generate the list of files for coq_makefile
# ls */*.v | egrep -v $filt >> _CoqProject
find * -name "*.v" -print  >> _CoqProject


coq_makefile INSTALLDEFAULTROOT = Reciprocity -f _CoqProject -o Makefile
# coq_makefile -f _CoqProject -o Makefile
