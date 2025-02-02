# MPTPTP2078

This MPTPTP2078 package contains a cleansed version of the MPTP2078 problem 
set, new "Pruney" variants of the problems, and solutions to the problems. The 
MPTP2078 problem set is at ...
    https://github.com/JUrban/MPTP2078
... and the components of the MPTP2078 problem set that are included in this
MPTPTP2078 package are governed by the copying and copyright restrictions of 
the MPTP2078 problem set, as provided in the MPTP2078-Documents directory.

+ The Bushy and Chainy problems were "cleansed" by converting all numbers to 
  uninterpreted functions, in compliance with TPTP syntax.
+ The problems have been given TPTP-style names. The mapping from the MPTP2078
  names to the MPTPTP2078 names is provided in MPTP2078-Documents/NameMapping.
+ The Bushy and Chainy problems' solutions are from running E 2.4 and 
  Vampire 4.4 on the problems with a 60s CPU limit, on StarExec Miami.
+ The Pruney problems were formed by looking at which axioms were used in
  the Bushy and Chainy problems' solutions, and from solutions to variants 
  of the Bushy and Chainy problems created using various axiom selection 
  systems. For each solution a corresponding Pruney problem was created with 
  only the axioms used in the proof. If any proof used a subset of the axioms 
  used by another, only the subset was used to form a problem.
+ The Pruney problems' solutions are from running E 2.4 and Vampire 4.4 on the 
  problems with a 300s CPU limit, on StarExec Miami. Strangely, even though the
  Pruney problems should be easier than the corresponding Bushy and Chainy
  problems (that had been solved in 60s), a few were not solved.
