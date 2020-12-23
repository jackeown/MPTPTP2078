%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   11 (  11 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

fof(t118_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).

fof(t112_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    inference(assume_negation,[status(cth)],[t123_enumset1])).

fof(c_0_4,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X9,X10,X11,X12] : k2_enumset1(X9,X10,X11,X12) = k2_enumset1(X11,X12,X9,X10) ),
    inference(variable_rename,[status(thm)],[t118_enumset1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8] : k2_enumset1(X5,X6,X7,X8) = k2_enumset1(X6,X8,X5,X7) ),
    inference(variable_rename,[status(thm)],[t112_enumset1])).

cnf(c_0_7,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:31:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_____0014_C11_13_nc_F1_SE_CS_SP_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.038 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t123_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X2,X3,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 0.20/0.38  fof(t118_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X4,X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_enumset1)).
% 0.20/0.38  fof(t112_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X1,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_enumset1)).
% 0.20/0.38  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X2,X3,X1)), inference(assume_negation,[status(cth)],[t123_enumset1])).
% 0.20/0.38  fof(c_0_4, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.20/0.38  fof(c_0_5, plain, ![X9, X10, X11, X12]:k2_enumset1(X9,X10,X11,X12)=k2_enumset1(X11,X12,X9,X10), inference(variable_rename,[status(thm)],[t118_enumset1])).
% 0.20/0.38  fof(c_0_6, plain, ![X5, X6, X7, X8]:k2_enumset1(X5,X6,X7,X8)=k2_enumset1(X6,X8,X5,X7), inference(variable_rename,[status(thm)],[t112_enumset1])).
% 0.20/0.38  cnf(c_0_7, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_8, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X4,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_9, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_10, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_8]), c_0_9])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 11
% 0.20/0.38  # Proof object clause steps            : 4
% 0.20/0.38  # Proof object formula steps           : 7
% 0.20/0.38  # Proof object conjectures             : 5
% 0.20/0.38  # Proof object clause conjectures      : 2
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 3
% 0.20/0.38  # Proof object initial formulas used   : 3
% 0.20/0.38  # Proof object generating inferences   : 0
% 0.20/0.38  # Proof object simplifying inferences  : 3
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 3
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 3
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 3
% 0.20/0.38  # Processed clauses                    : 3
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 2
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 6
% 0.20/0.38  # ...of the previous two non-trivial   : 6
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 6
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 2
% 0.20/0.38  #    Positive orientable unit clauses  : 0
% 0.20/0.38  #    Positive unorientable unit clauses: 2
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 0
% 0.20/0.38  # Current number of unprocessed clauses: 6
% 0.20/0.38  # ...number of literals in the above   : 6
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 0
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 1
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 4
% 0.20/0.38  # BW rewrite match successes           : 4
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 192
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.038 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.042 s
% 0.20/0.38  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
