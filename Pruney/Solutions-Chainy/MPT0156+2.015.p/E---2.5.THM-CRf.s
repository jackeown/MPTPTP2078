%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:42 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  30 expanded)
%              Number of clauses        :   11 (  13 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(assume_negation,[status(cth)],[t72_enumset1])).

fof(c_0_7,plain,(
    ! [X19,X20,X21,X22,X23] : k3_enumset1(X19,X20,X21,X22,X23) = k2_xboole_0(k2_enumset1(X19,X20,X21,X22),k1_tarski(X23)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14] : k2_enumset1(X11,X12,X13,X14) = k2_xboole_0(k1_tarski(X11),k1_enumset1(X12,X13,X14)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_9,negated_conjecture,(
    k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k1_tarski(X5)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_14,plain,(
    ! [X6,X7,X8] : k2_xboole_0(k2_xboole_0(X6,X7),X8) = k2_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_15,plain,(
    ! [X15,X16,X17,X18] : k2_enumset1(X15,X16,X17,X18) = k2_xboole_0(k1_enumset1(X15,X16,X17),k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)),k1_tarski(esk4_0)) != k2_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_11]),c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k2_xboole_0(X9,X10)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0))) != k2_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:08:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.35  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.35  #
% 0.13/0.35  # Preprocessing time       : 0.013 s
% 0.13/0.35  # Presaturation interreduction done
% 0.13/0.35  
% 0.13/0.35  # Proof found!
% 0.13/0.35  # SZS status Theorem
% 0.13/0.35  # SZS output start CNFRefutation
% 0.13/0.35  fof(t72_enumset1, conjecture, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.35  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.13/0.35  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.13/0.35  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.13/0.35  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.13/0.35  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.13/0.35  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(assume_negation,[status(cth)],[t72_enumset1])).
% 0.13/0.35  fof(c_0_7, plain, ![X19, X20, X21, X22, X23]:k3_enumset1(X19,X20,X21,X22,X23)=k2_xboole_0(k2_enumset1(X19,X20,X21,X22),k1_tarski(X23)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.13/0.35  fof(c_0_8, plain, ![X11, X12, X13, X14]:k2_enumset1(X11,X12,X13,X14)=k2_xboole_0(k1_tarski(X11),k1_enumset1(X12,X13,X14)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.13/0.35  fof(c_0_9, negated_conjecture, k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.35  cnf(c_0_10, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.35  cnf(c_0_11, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.35  cnf(c_0_12, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.35  cnf(c_0_13, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k1_tarski(X5))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.35  fof(c_0_14, plain, ![X6, X7, X8]:k2_xboole_0(k2_xboole_0(X6,X7),X8)=k2_xboole_0(X6,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.13/0.35  fof(c_0_15, plain, ![X15, X16, X17, X18]:k2_enumset1(X15,X16,X17,X18)=k2_xboole_0(k1_enumset1(X15,X16,X17),k1_tarski(X18)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.13/0.35  cnf(c_0_16, negated_conjecture, (k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)),k1_tarski(esk4_0))!=k2_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_11]), c_0_13])).
% 0.13/0.35  cnf(c_0_17, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.35  cnf(c_0_18, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.35  fof(c_0_19, plain, ![X9, X10]:k2_xboole_0(X9,k2_xboole_0(X9,X10))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.13/0.35  cnf(c_0_20, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0)))!=k2_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.35  cnf(c_0_21, plain, (k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(rw,[status(thm)],[c_0_18, c_0_11])).
% 0.13/0.35  cnf(c_0_22, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.35  cnf(c_0_23, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])]), ['proof']).
% 0.13/0.35  # SZS output end CNFRefutation
% 0.13/0.35  # Proof object total steps             : 24
% 0.13/0.35  # Proof object clause steps            : 11
% 0.13/0.35  # Proof object formula steps           : 13
% 0.13/0.35  # Proof object conjectures             : 7
% 0.13/0.35  # Proof object clause conjectures      : 4
% 0.13/0.35  # Proof object formula conjectures     : 3
% 0.13/0.35  # Proof object initial clauses used    : 6
% 0.13/0.35  # Proof object initial formulas used   : 6
% 0.13/0.35  # Proof object generating inferences   : 0
% 0.13/0.35  # Proof object simplifying inferences  : 8
% 0.13/0.35  # Training examples: 0 positive, 0 negative
% 0.13/0.35  # Parsed axioms                        : 6
% 0.13/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.35  # Initial clauses                      : 6
% 0.13/0.35  # Removed in clause preprocessing      : 2
% 0.13/0.35  # Initial clauses in saturation        : 4
% 0.13/0.35  # Processed clauses                    : 5
% 0.13/0.35  # ...of these trivial                  : 0
% 0.13/0.35  # ...subsumed                          : 0
% 0.13/0.35  # ...remaining for further processing  : 5
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
% 0.13/0.35  # Current number of processed clauses  : 3
% 0.13/0.35  #    Positive orientable unit clauses  : 3
% 0.13/0.35  #    Positive unorientable unit clauses: 0
% 0.13/0.35  #    Negative unit clauses             : 0
% 0.13/0.35  #    Non-unit-clauses                  : 0
% 0.13/0.35  # Current number of unprocessed clauses: 0
% 0.13/0.35  # ...number of literals in the above   : 0
% 0.13/0.35  # Current number of archived formulas  : 0
% 0.13/0.35  # Current number of archived clauses   : 4
% 0.13/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.35  # Unit Clause-clause subsumption calls : 0
% 0.13/0.35  # Rewrite failures with RHS unbound    : 0
% 0.13/0.35  # BW rewrite match attempts            : 2
% 0.13/0.35  # BW rewrite match successes           : 2
% 0.13/0.35  # Condensation attempts                : 0
% 0.13/0.35  # Condensation successes               : 0
% 0.13/0.35  # Termbank termtop insertions          : 371
% 0.13/0.35  
% 0.13/0.35  # -------------------------------------------------
% 0.13/0.35  # User time                : 0.012 s
% 0.13/0.35  # System time              : 0.003 s
% 0.13/0.35  # Total time               : 0.016 s
% 0.13/0.35  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
