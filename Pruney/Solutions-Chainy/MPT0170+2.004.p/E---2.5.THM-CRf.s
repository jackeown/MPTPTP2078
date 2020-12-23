%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:55 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   11 (  11 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t81_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(assume_negation,[status(cth)],[t86_enumset1])).

fof(c_0_4,negated_conjecture,(
    k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X7,X8,X9,X10,X11] : k4_enumset1(X7,X7,X8,X9,X10,X11) = k3_enumset1(X7,X8,X9,X10,X11) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_6,plain,(
    ! [X12,X13,X14,X15,X16,X17] : k6_enumset1(X12,X12,X12,X13,X14,X15,X16,X17) = k4_enumset1(X12,X13,X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t81_enumset1])).

cnf(c_0_7,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:44:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_____0014_C11_13_nc_F1_SE_CS_SP_S0Y
% 0.14/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.039 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t86_enumset1, conjecture, ![X1, X2, X3, X4, X5]:k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_enumset1)).
% 0.14/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.39  fof(t81_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 0.14/0.39  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(assume_negation,[status(cth)],[t86_enumset1])).
% 0.14/0.39  fof(c_0_4, negated_conjecture, k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.14/0.39  fof(c_0_5, plain, ![X7, X8, X9, X10, X11]:k4_enumset1(X7,X7,X8,X9,X10,X11)=k3_enumset1(X7,X8,X9,X10,X11), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.39  fof(c_0_6, plain, ![X12, X13, X14, X15, X16, X17]:k6_enumset1(X12,X12,X12,X13,X14,X15,X16,X17)=k4_enumset1(X12,X13,X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t81_enumset1])).
% 0.14/0.39  cnf(c_0_7, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.39  cnf(c_0_8, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  cnf(c_0_9, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_10, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_8]), c_0_9])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 11
% 0.14/0.39  # Proof object clause steps            : 4
% 0.14/0.39  # Proof object formula steps           : 7
% 0.14/0.39  # Proof object conjectures             : 5
% 0.14/0.39  # Proof object clause conjectures      : 2
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 3
% 0.14/0.39  # Proof object initial formulas used   : 3
% 0.14/0.39  # Proof object generating inferences   : 0
% 0.14/0.39  # Proof object simplifying inferences  : 3
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 3
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 3
% 0.14/0.39  # Removed in clause preprocessing      : 2
% 0.14/0.39  # Initial clauses in saturation        : 1
% 0.14/0.39  # Processed clauses                    : 1
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 0
% 0.14/0.39  # ...remaining for further processing  : 0
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 0
% 0.14/0.39  # Generated clauses                    : 0
% 0.14/0.39  # ...of the previous two non-trivial   : 0
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 0
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 0
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 0
% 0.14/0.39  #    Positive orientable unit clauses  : 0
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 0
% 0.14/0.39  #    Non-unit-clauses                  : 0
% 0.14/0.39  # Current number of unprocessed clauses: 0
% 0.14/0.39  # ...number of literals in the above   : 0
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 2
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.39  # Unit Clause-clause subsumption calls : 0
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 0
% 0.14/0.39  # BW rewrite match successes           : 0
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 182
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.039 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.042 s
% 0.14/0.39  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
