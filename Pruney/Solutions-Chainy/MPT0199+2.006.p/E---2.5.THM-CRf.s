%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   23 (  44 expanded)
%              Number of clauses        :   12 (  19 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  44 expanded)
%              Number of equality atoms :   22 (  43 expanded)
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

fof(t117_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X4,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    inference(assume_negation,[status(cth)],[t123_enumset1])).

fof(c_0_6,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16] : k2_enumset1(X13,X14,X15,X16) = k2_enumset1(X15,X14,X16,X13) ),
    inference(variable_rename,[status(thm)],[t117_enumset1])).

fof(c_0_9,plain,(
    ! [X9,X10,X11,X12] : k2_enumset1(X9,X10,X11,X12) = k2_enumset1(X9,X12,X11,X10) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8] : k2_enumset1(X5,X6,X7,X8) = k2_enumset1(X5,X7,X8,X6) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

cnf(c_0_11,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0) != k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_17,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X3,X3,X2,X4,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_12]),c_0_12])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_12]),c_0_12])).

cnf(c_0_19,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_12]),c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk2_0,esk1_0,esk3_0) != k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t123_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X2,X3,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 0.13/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(t117_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X2,X4,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 0.13/0.37  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 0.13/0.37  fof(t105_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X2,X3,X1)), inference(assume_negation,[status(cth)],[t123_enumset1])).
% 0.13/0.37  fof(c_0_6, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.13/0.37  fof(c_0_7, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.37  fof(c_0_8, plain, ![X13, X14, X15, X16]:k2_enumset1(X13,X14,X15,X16)=k2_enumset1(X15,X14,X16,X13), inference(variable_rename,[status(thm)],[t117_enumset1])).
% 0.13/0.37  fof(c_0_9, plain, ![X9, X10, X11, X12]:k2_enumset1(X9,X10,X11,X12)=k2_enumset1(X9,X12,X11,X10), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 0.13/0.37  fof(c_0_10, plain, ![X5, X6, X7, X8]:k2_enumset1(X5,X6,X7,X8)=k2_enumset1(X5,X7,X8,X6), inference(variable_rename,[status(thm)],[t105_enumset1])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_12, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_13, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X2,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_14, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_15, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0)!=k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 0.13/0.37  cnf(c_0_17, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X3,X3,X2,X4,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_12]), c_0_12])).
% 0.13/0.37  cnf(c_0_18, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_12]), c_0_12])).
% 0.13/0.37  cnf(c_0_19, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_12]), c_0_12])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk2_0,esk1_0,esk3_0)!=k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X2,X4,X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 23
% 0.13/0.37  # Proof object clause steps            : 12
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 7
% 0.13/0.37  # Proof object clause conjectures      : 4
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 5
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 1
% 0.13/0.37  # Proof object simplifying inferences  : 11
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 5
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 4
% 0.13/0.37  # Processed clauses                    : 16
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 4
% 0.13/0.37  # ...remaining for further processing  : 12
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 2
% 0.13/0.37  # Generated clauses                    : 68
% 0.13/0.37  # ...of the previous two non-trivial   : 49
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 68
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 6
% 0.13/0.37  #    Positive orientable unit clauses  : 0
% 0.13/0.37  #    Positive unorientable unit clauses: 6
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 0
% 0.13/0.37  # Current number of unprocessed clauses: 41
% 0.13/0.37  # ...number of literals in the above   : 41
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 7
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 18
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 78
% 0.13/0.37  # BW rewrite match successes           : 78
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 454
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.025 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.029 s
% 0.13/0.37  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
