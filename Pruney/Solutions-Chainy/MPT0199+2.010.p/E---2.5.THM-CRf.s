%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   21 (  51 expanded)
%              Number of clauses        :   10 (  20 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  51 expanded)
%              Number of equality atoms :   20 (  50 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t113_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    inference(assume_negation,[status(cth)],[t123_enumset1])).

fof(c_0_6,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_8,plain,(
    ! [X18,X19,X20,X21,X22] : k4_enumset1(X18,X18,X19,X20,X21,X22) = k3_enumset1(X18,X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13] : k2_enumset1(X10,X11,X12,X13) = k2_enumset1(X11,X13,X12,X10) ),
    inference(variable_rename,[status(thm)],[t113_enumset1])).

cnf(c_0_10,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9] : k2_enumset1(X6,X7,X8,X9) = k2_enumset1(X6,X9,X8,X7) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

cnf(c_0_15,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk2_0,esk3_0,esk1_0) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11]),c_0_12]),c_0_12])).

cnf(c_0_16,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X2,X2,X2,X4,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_11]),c_0_11]),c_0_12]),c_0_12])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk1_0,esk3_0,esk2_0) != k4_enumset1(esk4_0,esk4_0,esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X1,X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_11]),c_0_11]),c_0_12]),c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:52:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.35  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.35  #
% 0.13/0.35  # Preprocessing time       : 0.017 s
% 0.13/0.35  # Presaturation interreduction done
% 0.13/0.35  
% 0.13/0.35  # Proof found!
% 0.13/0.35  # SZS status Theorem
% 0.13/0.35  # SZS output start CNFRefutation
% 0.13/0.35  fof(t123_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X2,X3,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 0.13/0.35  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.35  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.35  fof(t113_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 0.13/0.35  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 0.13/0.35  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X2,X3,X1)), inference(assume_negation,[status(cth)],[t123_enumset1])).
% 0.13/0.35  fof(c_0_6, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.13/0.35  fof(c_0_7, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.35  fof(c_0_8, plain, ![X18, X19, X20, X21, X22]:k4_enumset1(X18,X18,X19,X20,X21,X22)=k3_enumset1(X18,X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.35  fof(c_0_9, plain, ![X10, X11, X12, X13]:k2_enumset1(X10,X11,X12,X13)=k2_enumset1(X11,X13,X12,X10), inference(variable_rename,[status(thm)],[t113_enumset1])).
% 0.13/0.35  cnf(c_0_10, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.35  cnf(c_0_11, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.35  cnf(c_0_12, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.35  cnf(c_0_13, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.35  fof(c_0_14, plain, ![X6, X7, X8, X9]:k2_enumset1(X6,X7,X8,X9)=k2_enumset1(X6,X9,X8,X7), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 0.13/0.35  cnf(c_0_15, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk2_0,esk3_0,esk1_0)!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_11]), c_0_12]), c_0_12])).
% 0.13/0.35  cnf(c_0_16, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X2,X2,X2,X4,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_11]), c_0_11]), c_0_12]), c_0_12])).
% 0.13/0.35  cnf(c_0_17, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.35  cnf(c_0_18, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk1_0,esk3_0,esk2_0)!=k4_enumset1(esk4_0,esk4_0,esk4_0,esk2_0,esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.35  cnf(c_0_19, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X1,X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_11]), c_0_11]), c_0_12]), c_0_12])).
% 0.13/0.35  cnf(c_0_20, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19])]), ['proof']).
% 0.13/0.35  # SZS output end CNFRefutation
% 0.13/0.35  # Proof object total steps             : 21
% 0.13/0.35  # Proof object clause steps            : 10
% 0.13/0.35  # Proof object formula steps           : 11
% 0.13/0.35  # Proof object conjectures             : 7
% 0.13/0.35  # Proof object clause conjectures      : 4
% 0.13/0.35  # Proof object formula conjectures     : 3
% 0.13/0.35  # Proof object initial clauses used    : 5
% 0.13/0.35  # Proof object initial formulas used   : 5
% 0.13/0.35  # Proof object generating inferences   : 0
% 0.13/0.35  # Proof object simplifying inferences  : 15
% 0.13/0.35  # Training examples: 0 positive, 0 negative
% 0.13/0.35  # Parsed axioms                        : 5
% 0.13/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.35  # Initial clauses                      : 5
% 0.13/0.35  # Removed in clause preprocessing      : 2
% 0.13/0.35  # Initial clauses in saturation        : 3
% 0.13/0.35  # Processed clauses                    : 4
% 0.13/0.35  # ...of these trivial                  : 0
% 0.13/0.35  # ...subsumed                          : 0
% 0.13/0.35  # ...remaining for further processing  : 4
% 0.13/0.35  # Other redundant clauses eliminated   : 0
% 0.13/0.35  # Clauses deleted for lack of memory   : 0
% 0.13/0.35  # Backward-subsumed                    : 0
% 0.13/0.35  # Backward-rewritten                   : 2
% 0.13/0.35  # Generated clauses                    : 0
% 0.13/0.35  # ...of the previous two non-trivial   : 1
% 0.13/0.35  # Contextual simplify-reflections      : 0
% 0.13/0.35  # Paramodulations                      : 0
% 0.13/0.35  # Factorizations                       : 0
% 0.13/0.35  # Equation resolutions                 : 0
% 0.13/0.35  # Propositional unsat checks           : 0
% 0.13/0.35  #    Propositional check models        : 0
% 0.13/0.35  #    Propositional check unsatisfiable : 0
% 0.13/0.35  #    Propositional clauses             : 0
% 0.13/0.35  #    Propositional clauses after purity: 0
% 0.13/0.35  #    Propositional unsat core size     : 0
% 0.13/0.35  #    Propositional preprocessing time  : 0.000
% 0.13/0.35  #    Propositional encoding time       : 0.000
% 0.13/0.35  #    Propositional solver time         : 0.000
% 0.13/0.35  #    Success case prop preproc time    : 0.000
% 0.13/0.35  #    Success case prop encoding time   : 0.000
% 0.13/0.35  #    Success case prop solver time     : 0.000
% 0.13/0.35  # Current number of processed clauses  : 2
% 0.13/0.35  #    Positive orientable unit clauses  : 0
% 0.13/0.35  #    Positive unorientable unit clauses: 2
% 0.13/0.35  #    Negative unit clauses             : 0
% 0.13/0.35  #    Non-unit-clauses                  : 0
% 0.13/0.35  # Current number of unprocessed clauses: 0
% 0.13/0.35  # ...number of literals in the above   : 0
% 0.13/0.35  # Current number of archived formulas  : 0
% 0.13/0.35  # Current number of archived clauses   : 4
% 0.13/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.35  # Unit Clause-clause subsumption calls : 1
% 0.13/0.35  # Rewrite failures with RHS unbound    : 0
% 0.13/0.35  # BW rewrite match attempts            : 12
% 0.13/0.35  # BW rewrite match successes           : 12
% 0.13/0.35  # Condensation attempts                : 0
% 0.13/0.35  # Condensation successes               : 0
% 0.13/0.35  # Termbank termtop insertions          : 268
% 0.13/0.35  
% 0.13/0.35  # -------------------------------------------------
% 0.13/0.35  # User time                : 0.018 s
% 0.13/0.35  # System time              : 0.002 s
% 0.13/0.35  # Total time               : 0.020 s
% 0.13/0.35  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
