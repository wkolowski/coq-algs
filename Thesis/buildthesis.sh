#!/bin/sh

# Compile the thesis.
latexmk -pdf -f -quiet -interaction=nonstopmode Thesis.tex
