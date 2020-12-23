%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:45 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   21 (  51 expanded)
%              Number of clauses        :   10 (  22 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  51 expanded)
%              Number of equality atoms :   20 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t74_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(c_0_5,plain,(
    ! [X8,X9,X10,X11,X12,X13] : k4_enumset1(X8,X9,X10,X11,X12,X13) = k2_xboole_0(k1_enumset1(X8,X9,X10),k1_enumset1(X11,X12,X13)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

fof(c_0_6,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(assume_negation,[status(cth)],[t74_enumset1])).

fof(c_0_8,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27] : k5_enumset1(X21,X22,X23,X24,X25,X26,X27) = k2_xboole_0(k1_tarski(X21),k4_enumset1(X22,X23,X24,X25,X26,X27)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

cnf(c_0_9,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,(
    k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_10])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20] : k5_enumset1(X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k1_enumset1(X18,X19,X20)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

cnf(c_0_15,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X5,X5,X6,X7))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0))) != k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_13]),c_0_16])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X5,X5,X6,X7))) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X5,X6,X7)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_10]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:57:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.36  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.026 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 0.12/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.36  fof(t74_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.36  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 0.12/0.37  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 0.12/0.37  fof(c_0_5, plain, ![X8, X9, X10, X11, X12, X13]:k4_enumset1(X8,X9,X10,X11,X12,X13)=k2_xboole_0(k1_enumset1(X8,X9,X10),k1_enumset1(X11,X12,X13)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 0.12/0.37  fof(c_0_6, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(assume_negation,[status(cth)],[t74_enumset1])).
% 0.12/0.37  fof(c_0_8, plain, ![X21, X22, X23, X24, X25, X26, X27]:k5_enumset1(X21,X22,X23,X24,X25,X26,X27)=k2_xboole_0(k1_tarski(X21),k4_enumset1(X22,X23,X24,X25,X26,X27)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 0.12/0.37  cnf(c_0_9, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_10, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  fof(c_0_11, negated_conjecture, k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.37  cnf(c_0_12, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_13, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10]), c_0_10])).
% 0.12/0.37  fof(c_0_14, plain, ![X14, X15, X16, X17, X18, X19, X20]:k5_enumset1(X14,X15,X16,X17,X18,X19,X20)=k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k1_enumset1(X18,X19,X20)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_16, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X5,X5,X6,X7)))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.37  cnf(c_0_17, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0)))!=k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_13]), c_0_16])).
% 0.12/0.37  cnf(c_0_19, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X5,X5,X6,X7)))=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X5,X6,X7))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_10]), c_0_16])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 21
% 0.12/0.37  # Proof object clause steps            : 10
% 0.12/0.37  # Proof object formula steps           : 11
% 0.12/0.37  # Proof object conjectures             : 6
% 0.12/0.37  # Proof object clause conjectures      : 3
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 5
% 0.12/0.37  # Proof object initial formulas used   : 5
% 0.12/0.37  # Proof object generating inferences   : 0
% 0.12/0.37  # Proof object simplifying inferences  : 9
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 5
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 5
% 0.12/0.37  # Removed in clause preprocessing      : 3
% 0.12/0.37  # Initial clauses in saturation        : 2
% 0.12/0.37  # Processed clauses                    : 2
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 2
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 1
% 0.12/0.37  # Generated clauses                    : 0
% 0.12/0.37  # ...of the previous two non-trivial   : 0
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 0
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 1
% 0.12/0.37  #    Positive orientable unit clauses  : 1
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 0
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 4
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 392
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.025 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.029 s
% 0.12/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
