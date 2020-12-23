%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:12 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   13 (  19 expanded)
%              Number of clauses        :    6 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  19 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t102_enumset1,conjecture,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(t100_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(t99_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    inference(assume_negation,[status(cth)],[t102_enumset1])).

fof(c_0_4,negated_conjecture,(
    k1_enumset1(esk1_0,esk2_0,esk3_0) != k1_enumset1(esk3_0,esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X4,X5,X6] : k1_enumset1(X4,X5,X6) = k1_enumset1(X5,X6,X4) ),
    inference(variable_rename,[status(thm)],[t100_enumset1])).

fof(c_0_6,plain,(
    ! [X7,X8,X9] : k1_enumset1(X7,X8,X9) = k1_enumset1(X8,X7,X9) ),
    inference(variable_rename,[status(thm)],[t99_enumset1])).

cnf(c_0_7,negated_conjecture,
    ( k1_enumset1(esk1_0,esk2_0,esk3_0) != k1_enumset1(esk3_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k1_enumset1(esk3_0,esk1_0,esk2_0) != k1_enumset1(esk3_0,esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_8])).

cnf(c_0_11,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n006.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 20:10:22 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  # Version: 2.5pre002
% 0.06/0.25  # No SInE strategy applied
% 0.06/0.25  # Trying AutoSched0 for 299 seconds
% 0.10/0.28  # AutoSched0-Mode selected heuristic G_____0014_C11_13_nc_F1_SE_CS_SP_S0Y
% 0.10/0.28  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.10/0.28  #
% 0.10/0.28  # Preprocessing time       : 0.025 s
% 0.10/0.28  
% 0.10/0.28  # Proof found!
% 0.10/0.28  # SZS status Theorem
% 0.10/0.28  # SZS output start CNFRefutation
% 0.10/0.28  fof(t102_enumset1, conjecture, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 0.10/0.28  fof(t100_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 0.10/0.28  fof(t99_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X1,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 0.10/0.28  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(assume_negation,[status(cth)],[t102_enumset1])).
% 0.10/0.28  fof(c_0_4, negated_conjecture, k1_enumset1(esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk3_0,esk2_0,esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.10/0.28  fof(c_0_5, plain, ![X4, X5, X6]:k1_enumset1(X4,X5,X6)=k1_enumset1(X5,X6,X4), inference(variable_rename,[status(thm)],[t100_enumset1])).
% 0.10/0.28  fof(c_0_6, plain, ![X7, X8, X9]:k1_enumset1(X7,X8,X9)=k1_enumset1(X8,X7,X9), inference(variable_rename,[status(thm)],[t99_enumset1])).
% 0.10/0.28  cnf(c_0_7, negated_conjecture, (k1_enumset1(esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk3_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.10/0.28  cnf(c_0_8, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.10/0.28  cnf(c_0_9, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.10/0.28  cnf(c_0_10, negated_conjecture, (k1_enumset1(esk3_0,esk1_0,esk2_0)!=k1_enumset1(esk3_0,esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_8]), c_0_8])).
% 0.10/0.28  cnf(c_0_11, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.10/0.28  cnf(c_0_12, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11])]), ['proof']).
% 0.10/0.28  # SZS output end CNFRefutation
% 0.10/0.28  # Proof object total steps             : 13
% 0.10/0.28  # Proof object clause steps            : 6
% 0.10/0.28  # Proof object formula steps           : 7
% 0.10/0.28  # Proof object conjectures             : 6
% 0.10/0.28  # Proof object clause conjectures      : 3
% 0.10/0.28  # Proof object formula conjectures     : 3
% 0.10/0.28  # Proof object initial clauses used    : 3
% 0.10/0.28  # Proof object initial formulas used   : 3
% 0.10/0.28  # Proof object generating inferences   : 1
% 0.10/0.28  # Proof object simplifying inferences  : 4
% 0.10/0.28  # Training examples: 0 positive, 0 negative
% 0.10/0.28  # Parsed axioms                        : 3
% 0.10/0.28  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.28  # Initial clauses                      : 3
% 0.10/0.28  # Removed in clause preprocessing      : 0
% 0.10/0.28  # Initial clauses in saturation        : 3
% 0.10/0.28  # Processed clauses                    : 6
% 0.10/0.28  # ...of these trivial                  : 0
% 0.10/0.28  # ...subsumed                          : 2
% 0.10/0.28  # ...remaining for further processing  : 4
% 0.10/0.28  # Other redundant clauses eliminated   : 0
% 0.10/0.28  # Clauses deleted for lack of memory   : 0
% 0.10/0.28  # Backward-subsumed                    : 0
% 0.10/0.28  # Backward-rewritten                   : 1
% 0.10/0.28  # Generated clauses                    : 14
% 0.10/0.28  # ...of the previous two non-trivial   : 6
% 0.10/0.28  # Contextual simplify-reflections      : 0
% 0.10/0.28  # Paramodulations                      : 14
% 0.10/0.28  # Factorizations                       : 0
% 0.10/0.28  # Equation resolutions                 : 0
% 0.10/0.28  # Propositional unsat checks           : 0
% 0.10/0.28  #    Propositional check models        : 0
% 0.10/0.28  #    Propositional check unsatisfiable : 0
% 0.10/0.28  #    Propositional clauses             : 0
% 0.10/0.28  #    Propositional clauses after purity: 0
% 0.10/0.28  #    Propositional unsat core size     : 0
% 0.10/0.28  #    Propositional preprocessing time  : 0.000
% 0.10/0.28  #    Propositional encoding time       : 0.000
% 0.10/0.28  #    Propositional solver time         : 0.000
% 0.10/0.28  #    Success case prop preproc time    : 0.000
% 0.10/0.28  #    Success case prop encoding time   : 0.000
% 0.10/0.28  #    Success case prop solver time     : 0.000
% 0.10/0.28  # Current number of processed clauses  : 3
% 0.10/0.28  #    Positive orientable unit clauses  : 0
% 0.10/0.28  #    Positive unorientable unit clauses: 3
% 0.10/0.28  #    Negative unit clauses             : 0
% 0.10/0.28  #    Non-unit-clauses                  : 0
% 0.10/0.28  # Current number of unprocessed clauses: 3
% 0.10/0.28  # ...number of literals in the above   : 3
% 0.10/0.28  # Current number of archived formulas  : 0
% 0.10/0.28  # Current number of archived clauses   : 1
% 0.10/0.28  # Clause-clause subsumption calls (NU) : 0
% 0.10/0.28  # Rec. Clause-clause subsumption calls : 0
% 0.10/0.28  # Non-unit clause-clause subsumptions  : 0
% 0.10/0.28  # Unit Clause-clause subsumption calls : 3
% 0.10/0.28  # Rewrite failures with RHS unbound    : 0
% 0.10/0.28  # BW rewrite match attempts            : 14
% 0.10/0.28  # BW rewrite match successes           : 14
% 0.10/0.28  # Condensation attempts                : 0
% 0.10/0.28  # Condensation successes               : 0
% 0.10/0.28  # Termbank termtop insertions          : 196
% 0.10/0.28  
% 0.10/0.28  # -------------------------------------------------
% 0.10/0.28  # User time                : 0.026 s
% 0.10/0.28  # System time              : 0.002 s
% 0.10/0.28  # Total time               : 0.028 s
% 0.10/0.28  # Maximum resident set size: 1548 pages
%------------------------------------------------------------------------------
