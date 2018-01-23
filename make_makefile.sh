#!/bin/sh

#coq_makefile -R "." RandomCoqCode -o makefile RCCBase.v DS/**v Reflection/**v Sorting/**v Structures/**v Trash/**v
coq_makefile -R "." RandomCoqCode -o makefile *v */*v */*/*v # WEIRD
