%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:30 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   13 (  19 expanded)
%              Number of clauses        :    6 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  19 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X4,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

fof(t110_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_enumset1)).

fof(t109_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X1,X4,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_enumset1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X4,X1) ),
    inference(assume_negation,[status(cth)],[t117_enumset1])).

fof(c_0_4,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk3_0,esk2_0,esk4_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X9,X10,X11,X12] : k2_enumset1(X9,X10,X11,X12) = k2_enumset1(X10,X11,X9,X12) ),
    inference(variable_rename,[status(thm)],[t110_enumset1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8] : k2_enumset1(X5,X6,X7,X8) = k2_enumset1(X6,X5,X8,X7) ),
    inference(variable_rename,[status(thm)],[t109_enumset1])).

cnf(c_0_7,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk3_0,esk2_0,esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X1,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k2_enumset1(esk3_0,esk1_0,esk2_0,esk4_0) != k2_enumset1(esk3_0,esk2_0,esk4_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_8])).

cnf(c_0_11,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X2,X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n024.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 12:10:36 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.35  # AutoSched0-Mode selected heuristic G_____0014_C11_13_nc_F1_SE_CS_SP_S0Y
% 0.18/0.35  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.35  #
% 0.18/0.35  # Preprocessing time       : 0.026 s
% 0.18/0.35  
% 0.18/0.35  # Proof found!
% 0.18/0.35  # SZS status Theorem
% 0.18/0.35  # SZS output start CNFRefutation
% 0.18/0.35  fof(t117_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X2,X4,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_enumset1)).
% 0.18/0.35  fof(t110_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X1,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_enumset1)).
% 0.18/0.35  fof(t109_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X1,X4,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_enumset1)).
% 0.18/0.35  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X2,X4,X1)), inference(assume_negation,[status(cth)],[t117_enumset1])).
% 0.18/0.35  fof(c_0_4, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk3_0,esk2_0,esk4_0,esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.18/0.35  fof(c_0_5, plain, ![X9, X10, X11, X12]:k2_enumset1(X9,X10,X11,X12)=k2_enumset1(X10,X11,X9,X12), inference(variable_rename,[status(thm)],[t110_enumset1])).
% 0.18/0.35  fof(c_0_6, plain, ![X5, X6, X7, X8]:k2_enumset1(X5,X6,X7,X8)=k2_enumset1(X6,X5,X8,X7), inference(variable_rename,[status(thm)],[t109_enumset1])).
% 0.18/0.35  cnf(c_0_7, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk3_0,esk2_0,esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.18/0.35  cnf(c_0_8, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.35  cnf(c_0_9, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X1,X4,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.35  cnf(c_0_10, negated_conjecture, (k2_enumset1(esk3_0,esk1_0,esk2_0,esk4_0)!=k2_enumset1(esk3_0,esk2_0,esk4_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_8]), c_0_8])).
% 0.18/0.35  cnf(c_0_11, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X2,X3)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.18/0.35  cnf(c_0_12, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11])]), ['proof']).
% 0.18/0.35  # SZS output end CNFRefutation
% 0.18/0.35  # Proof object total steps             : 13
% 0.18/0.35  # Proof object clause steps            : 6
% 0.18/0.35  # Proof object formula steps           : 7
% 0.18/0.35  # Proof object conjectures             : 6
% 0.18/0.35  # Proof object clause conjectures      : 3
% 0.18/0.35  # Proof object formula conjectures     : 3
% 0.18/0.35  # Proof object initial clauses used    : 3
% 0.18/0.35  # Proof object initial formulas used   : 3
% 0.18/0.35  # Proof object generating inferences   : 1
% 0.18/0.35  # Proof object simplifying inferences  : 4
% 0.18/0.35  # Training examples: 0 positive, 0 negative
% 0.18/0.35  # Parsed axioms                        : 3
% 0.18/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.35  # Initial clauses                      : 3
% 0.18/0.35  # Removed in clause preprocessing      : 0
% 0.18/0.35  # Initial clauses in saturation        : 3
% 0.18/0.35  # Processed clauses                    : 6
% 0.18/0.35  # ...of these trivial                  : 0
% 0.18/0.35  # ...subsumed                          : 2
% 0.18/0.35  # ...remaining for further processing  : 4
% 0.18/0.35  # Other redundant clauses eliminated   : 0
% 0.18/0.35  # Clauses deleted for lack of memory   : 0
% 0.18/0.35  # Backward-subsumed                    : 0
% 0.18/0.35  # Backward-rewritten                   : 1
% 0.18/0.35  # Generated clauses                    : 16
% 0.18/0.35  # ...of the previous two non-trivial   : 6
% 0.18/0.35  # Contextual simplify-reflections      : 0
% 0.18/0.35  # Paramodulations                      : 16
% 0.18/0.35  # Factorizations                       : 0
% 0.18/0.35  # Equation resolutions                 : 0
% 0.18/0.35  # Propositional unsat checks           : 0
% 0.18/0.35  #    Propositional check models        : 0
% 0.18/0.35  #    Propositional check unsatisfiable : 0
% 0.18/0.35  #    Propositional clauses             : 0
% 0.18/0.35  #    Propositional clauses after purity: 0
% 0.18/0.35  #    Propositional unsat core size     : 0
% 0.18/0.35  #    Propositional preprocessing time  : 0.000
% 0.18/0.35  #    Propositional encoding time       : 0.000
% 0.18/0.35  #    Propositional solver time         : 0.000
% 0.18/0.35  #    Success case prop preproc time    : 0.000
% 0.18/0.35  #    Success case prop encoding time   : 0.000
% 0.18/0.35  #    Success case prop solver time     : 0.000
% 0.18/0.35  # Current number of processed clauses  : 3
% 0.18/0.35  #    Positive orientable unit clauses  : 0
% 0.18/0.35  #    Positive unorientable unit clauses: 3
% 0.18/0.35  #    Negative unit clauses             : 0
% 0.18/0.35  #    Non-unit-clauses                  : 0
% 0.18/0.35  # Current number of unprocessed clauses: 3
% 0.18/0.35  # ...number of literals in the above   : 3
% 0.18/0.35  # Current number of archived formulas  : 0
% 0.18/0.35  # Current number of archived clauses   : 1
% 0.18/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.35  # Unit Clause-clause subsumption calls : 3
% 0.18/0.35  # Rewrite failures with RHS unbound    : 0
% 0.18/0.35  # BW rewrite match attempts            : 14
% 0.18/0.35  # BW rewrite match successes           : 14
% 0.18/0.35  # Condensation attempts                : 0
% 0.18/0.35  # Condensation successes               : 0
% 0.18/0.35  # Termbank termtop insertions          : 222
% 0.18/0.35  
% 0.18/0.35  # -------------------------------------------------
% 0.18/0.35  # User time                : 0.026 s
% 0.18/0.35  # System time              : 0.003 s
% 0.18/0.35  # Total time               : 0.029 s
% 0.18/0.35  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
