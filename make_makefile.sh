#!/bin/sh

coq_makefile -R "." RandomCoqCode -o makefile RCCBase.v Sorting/*v Reification/*v Trees/* Ord/*
