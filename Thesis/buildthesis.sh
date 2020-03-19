#!/bin/sh

# Compile the thesis.
latexmk -pdf -f -quiet -interaction=nonstopmode -shell-escape Thesis.tex
