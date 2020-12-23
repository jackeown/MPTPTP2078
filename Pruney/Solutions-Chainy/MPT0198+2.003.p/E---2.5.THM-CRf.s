%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:31 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
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
fof(t119_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

fof(t111_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

fof(l123_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X2,X1) ),
    inference(assume_negation,[status(cth)],[t119_enumset1])).

fof(c_0_4,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk3_0,esk4_0,esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X9,X10,X11,X12] : k2_enumset1(X9,X10,X11,X12) = k2_enumset1(X10,X11,X12,X9) ),
    inference(variable_rename,[status(thm)],[t111_enumset1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8] : k2_enumset1(X5,X6,X7,X8) = k2_enumset1(X6,X7,X5,X8) ),
    inference(variable_rename,[status(thm)],[l123_enumset1])).

cnf(c_0_7,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk3_0,esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k2_enumset1(esk3_0,esk4_0,esk1_0,esk2_0) != k2_enumset1(esk3_0,esk4_0,esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_8])).

cnf(c_0_11,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.31  % Computer   : n014.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 13:14:07 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  # Version: 2.5pre002
% 0.10/0.31  # No SInE strategy applied
% 0.10/0.31  # Trying AutoSched0 for 299 seconds
% 0.17/0.34  # AutoSched0-Mode selected heuristic G_____0014_C11_13_nc_F1_SE_CS_SP_S0Y
% 0.17/0.34  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.17/0.34  #
% 0.17/0.34  # Preprocessing time       : 0.026 s
% 0.17/0.34  
% 0.17/0.34  # Proof found!
% 0.17/0.34  # SZS status Theorem
% 0.17/0.34  # SZS output start CNFRefutation
% 0.17/0.34  fof(t119_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X4,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_enumset1)).
% 0.17/0.34  fof(t111_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X4,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_enumset1)).
% 0.17/0.34  fof(l123_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X1,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l123_enumset1)).
% 0.17/0.34  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X4,X2,X1)), inference(assume_negation,[status(cth)],[t119_enumset1])).
% 0.17/0.34  fof(c_0_4, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk3_0,esk4_0,esk2_0,esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.17/0.34  fof(c_0_5, plain, ![X9, X10, X11, X12]:k2_enumset1(X9,X10,X11,X12)=k2_enumset1(X10,X11,X12,X9), inference(variable_rename,[status(thm)],[t111_enumset1])).
% 0.17/0.34  fof(c_0_6, plain, ![X5, X6, X7, X8]:k2_enumset1(X5,X6,X7,X8)=k2_enumset1(X6,X7,X5,X8), inference(variable_rename,[status(thm)],[l123_enumset1])).
% 0.17/0.34  cnf(c_0_7, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk3_0,esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.17/0.34  cnf(c_0_8, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.17/0.34  cnf(c_0_9, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.17/0.34  cnf(c_0_10, negated_conjecture, (k2_enumset1(esk3_0,esk4_0,esk1_0,esk2_0)!=k2_enumset1(esk3_0,esk4_0,esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_8]), c_0_8])).
% 0.17/0.34  cnf(c_0_11, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X2,X4,X3)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.17/0.34  cnf(c_0_12, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11])]), ['proof']).
% 0.17/0.34  # SZS output end CNFRefutation
% 0.17/0.34  # Proof object total steps             : 13
% 0.17/0.34  # Proof object clause steps            : 6
% 0.17/0.34  # Proof object formula steps           : 7
% 0.17/0.34  # Proof object conjectures             : 6
% 0.17/0.34  # Proof object clause conjectures      : 3
% 0.17/0.34  # Proof object formula conjectures     : 3
% 0.17/0.34  # Proof object initial clauses used    : 3
% 0.17/0.34  # Proof object initial formulas used   : 3
% 0.17/0.34  # Proof object generating inferences   : 1
% 0.17/0.34  # Proof object simplifying inferences  : 4
% 0.17/0.34  # Training examples: 0 positive, 0 negative
% 0.17/0.34  # Parsed axioms                        : 3
% 0.17/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.34  # Initial clauses                      : 3
% 0.17/0.34  # Removed in clause preprocessing      : 0
% 0.17/0.34  # Initial clauses in saturation        : 3
% 0.17/0.34  # Processed clauses                    : 9
% 0.17/0.34  # ...of these trivial                  : 0
% 0.17/0.34  # ...subsumed                          : 2
% 0.17/0.34  # ...remaining for further processing  : 7
% 0.17/0.34  # Other redundant clauses eliminated   : 0
% 0.17/0.34  # Clauses deleted for lack of memory   : 0
% 0.17/0.34  # Backward-subsumed                    : 0
% 0.17/0.34  # Backward-rewritten                   : 1
% 0.17/0.34  # Generated clauses                    : 66
% 0.17/0.34  # ...of the previous two non-trivial   : 46
% 0.17/0.34  # Contextual simplify-reflections      : 0
% 0.17/0.34  # Paramodulations                      : 66
% 0.17/0.34  # Factorizations                       : 0
% 0.17/0.34  # Equation resolutions                 : 0
% 0.17/0.34  # Propositional unsat checks           : 0
% 0.17/0.34  #    Propositional check models        : 0
% 0.17/0.34  #    Propositional check unsatisfiable : 0
% 0.17/0.34  #    Propositional clauses             : 0
% 0.17/0.34  #    Propositional clauses after purity: 0
% 0.17/0.34  #    Propositional unsat core size     : 0
% 0.17/0.34  #    Propositional preprocessing time  : 0.000
% 0.17/0.34  #    Propositional encoding time       : 0.000
% 0.17/0.34  #    Propositional solver time         : 0.000
% 0.17/0.34  #    Success case prop preproc time    : 0.000
% 0.17/0.34  #    Success case prop encoding time   : 0.000
% 0.17/0.34  #    Success case prop solver time     : 0.000
% 0.17/0.34  # Current number of processed clauses  : 6
% 0.17/0.34  #    Positive orientable unit clauses  : 0
% 0.17/0.34  #    Positive unorientable unit clauses: 6
% 0.17/0.34  #    Negative unit clauses             : 0
% 0.17/0.34  #    Non-unit-clauses                  : 0
% 0.17/0.34  # Current number of unprocessed clauses: 40
% 0.17/0.34  # ...number of literals in the above   : 40
% 0.17/0.34  # Current number of archived formulas  : 0
% 0.17/0.34  # Current number of archived clauses   : 1
% 0.17/0.34  # Clause-clause subsumption calls (NU) : 0
% 0.17/0.34  # Rec. Clause-clause subsumption calls : 0
% 0.17/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.17/0.34  # Unit Clause-clause subsumption calls : 15
% 0.17/0.34  # Rewrite failures with RHS unbound    : 0
% 0.17/0.34  # BW rewrite match attempts            : 56
% 0.17/0.34  # BW rewrite match successes           : 56
% 0.17/0.34  # Condensation attempts                : 0
% 0.17/0.34  # Condensation successes               : 0
% 0.17/0.34  # Termbank termtop insertions          : 354
% 0.17/0.34  
% 0.17/0.34  # -------------------------------------------------
% 0.17/0.34  # User time                : 0.024 s
% 0.17/0.34  # System time              : 0.005 s
% 0.17/0.34  # Total time               : 0.029 s
% 0.17/0.34  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
