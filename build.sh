#!/bin/sh

# Generate a makefile.
coq_makefile -R "." CoqAlgs -o makefile $(find -name "*.v")

# Build the library.
make -j `nproc`

# Delete the makefile and related files.
rm makefile makefile.conf

# Build the thesis.
cd Thesis
./buildthesis.sh
