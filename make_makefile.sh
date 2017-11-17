#!/bin/sh

coq_makefile -R "." RandomCoqCode -o makefile RCCBase.v Reflection/**v Sorting/**v Structures/**v Thrash/**v Trees/**v
