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
% DateTime   : Thu Dec  3 10:36:33 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   25 (  96 expanded)
%              Number of clauses        :   14 (  41 expanded)
%              Number of leaves         :    5 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   25 (  96 expanded)
%              Number of equality atoms :   24 (  95 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(l123_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

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
    ! [X5,X6,X7,X8] : k2_enumset1(X5,X6,X7,X8) = k2_enumset1(X6,X7,X5,X8) ),
    inference(variable_rename,[status(thm)],[l123_enumset1])).

cnf(c_0_9,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X13,X14,X15,X16] : k2_enumset1(X13,X14,X15,X16) = k2_enumset1(X13,X16,X15,X14) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

cnf(c_0_13,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0) != k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_10])).

cnf(c_0_14,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X2,X2,X3,X1,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_10]),c_0_10])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X9,X10,X11,X12] : k2_enumset1(X9,X10,X11,X12) = k2_enumset1(X9,X11,X12,X10) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

cnf(c_0_17,negated_conjecture,
    ( k3_enumset1(esk2_0,esk2_0,esk3_0,esk1_0,esk4_0) != k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_10]),c_0_10])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk3_0,esk2_0,esk1_0) != k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_14]),c_0_18])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_10]),c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk2_0,esk1_0,esk3_0) != k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:05:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.36  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.026 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t123_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X2,X3,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 0.18/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.36  fof(l123_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X1,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l123_enumset1)).
% 0.18/0.36  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 0.18/0.36  fof(t105_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 0.18/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X2,X3,X1)), inference(assume_negation,[status(cth)],[t123_enumset1])).
% 0.18/0.36  fof(c_0_6, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.18/0.36  fof(c_0_7, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.36  fof(c_0_8, plain, ![X5, X6, X7, X8]:k2_enumset1(X5,X6,X7,X8)=k2_enumset1(X6,X7,X5,X8), inference(variable_rename,[status(thm)],[l123_enumset1])).
% 0.18/0.36  cnf(c_0_9, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.36  cnf(c_0_10, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.36  cnf(c_0_11, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  fof(c_0_12, plain, ![X13, X14, X15, X16]:k2_enumset1(X13,X14,X15,X16)=k2_enumset1(X13,X16,X15,X14), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 0.18/0.36  cnf(c_0_13, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0)!=k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10]), c_0_10])).
% 0.18/0.36  cnf(c_0_14, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X2,X2,X3,X1,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_10]), c_0_10])).
% 0.18/0.36  cnf(c_0_15, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  fof(c_0_16, plain, ![X9, X10, X11, X12]:k2_enumset1(X9,X10,X11,X12)=k2_enumset1(X9,X11,X12,X10), inference(variable_rename,[status(thm)],[t105_enumset1])).
% 0.18/0.36  cnf(c_0_17, negated_conjecture, (k3_enumset1(esk2_0,esk2_0,esk3_0,esk1_0,esk4_0)!=k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14])).
% 0.18/0.36  cnf(c_0_18, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_10]), c_0_10])).
% 0.18/0.36  cnf(c_0_19, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_20, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk3_0,esk2_0,esk1_0)!=k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_14]), c_0_18])).
% 0.18/0.36  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_10]), c_0_10])).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk2_0,esk1_0,esk3_0)!=k3_enumset1(esk4_0,esk4_0,esk2_0,esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.36  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X2,X4,X3)), inference(spm,[status(thm)],[c_0_18, c_0_21])).
% 0.18/0.36  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 25
% 0.18/0.36  # Proof object clause steps            : 14
% 0.18/0.36  # Proof object formula steps           : 11
% 0.18/0.36  # Proof object conjectures             : 9
% 0.18/0.36  # Proof object clause conjectures      : 6
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 5
% 0.18/0.36  # Proof object initial formulas used   : 5
% 0.18/0.36  # Proof object generating inferences   : 1
% 0.18/0.36  # Proof object simplifying inferences  : 16
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 5
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 5
% 0.18/0.36  # Removed in clause preprocessing      : 1
% 0.18/0.36  # Initial clauses in saturation        : 4
% 0.18/0.36  # Processed clauses                    : 19
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 4
% 0.18/0.36  # ...remaining for further processing  : 15
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 4
% 0.18/0.36  # Generated clauses                    : 92
% 0.18/0.36  # ...of the previous two non-trivial   : 71
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 92
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 0
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 7
% 0.18/0.36  #    Positive orientable unit clauses  : 0
% 0.18/0.36  #    Positive unorientable unit clauses: 7
% 0.18/0.36  #    Negative unit clauses             : 0
% 0.18/0.36  #    Non-unit-clauses                  : 0
% 0.18/0.36  # Current number of unprocessed clauses: 60
% 0.18/0.36  # ...number of literals in the above   : 60
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 9
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.36  # Unit Clause-clause subsumption calls : 24
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 104
% 0.18/0.36  # BW rewrite match successes           : 104
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 520
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.029 s
% 0.18/0.36  # System time              : 0.001 s
% 0.18/0.36  # Total time               : 0.030 s
% 0.18/0.36  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
