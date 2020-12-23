%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:37 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   23 (  67 expanded)
%              Number of clauses        :   12 (  30 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  67 expanded)
%              Number of equality atoms :   22 (  66 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t71_enumset1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8] : k2_enumset1(X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X8)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_7,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_8,negated_conjecture,(
    k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] : k1_enumset1(X9,X10,X11) = k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_12,plain,(
    ! [X12,X13,X14,X15] : k2_enumset1(X12,X13,X14,X15) = k2_xboole_0(k1_enumset1(X12,X13,X14),k1_tarski(X15)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_13,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_10])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk3_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_enumset1(X1,X1,X2),k1_tarski(X3)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4)) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k2_xboole_0(k1_enumset1(esk2_0,esk2_0,esk2_0),k1_tarski(esk3_0))) != k2_xboole_0(k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_tarski(esk2_0)),k1_tarski(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k1_enumset1(X1,X1,X2),k2_xboole_0(k1_enumset1(X3,X3,X3),k1_tarski(X4))) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:04:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.19/0.36  # and selection function SelectNewComplexAHP.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.026 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t71_enumset1, conjecture, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.36  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.19/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.36  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.19/0.36  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.19/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t71_enumset1])).
% 0.19/0.36  fof(c_0_6, plain, ![X5, X6, X7, X8]:k2_enumset1(X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X8)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.19/0.36  fof(c_0_7, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.36  fof(c_0_8, negated_conjecture, k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.19/0.36  cnf(c_0_9, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  cnf(c_0_10, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.36  fof(c_0_11, plain, ![X9, X10, X11]:k1_enumset1(X9,X10,X11)=k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.19/0.36  fof(c_0_12, plain, ![X12, X13, X14, X15]:k2_enumset1(X12,X13,X14,X15)=k2_xboole_0(k1_enumset1(X12,X13,X14),k1_tarski(X15)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.19/0.36  cnf(c_0_13, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.36  cnf(c_0_14, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10]), c_0_10])).
% 0.19/0.36  cnf(c_0_15, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_16, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  cnf(c_0_17, negated_conjecture, (k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk3_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.36  cnf(c_0_18, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_enumset1(X1,X1,X2),k1_tarski(X3))), inference(rw,[status(thm)],[c_0_15, c_0_10])).
% 0.19/0.36  cnf(c_0_19, plain, (k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4))=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(rw,[status(thm)],[c_0_16, c_0_14])).
% 0.19/0.36  cnf(c_0_20, negated_conjecture, (k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k2_xboole_0(k1_enumset1(esk2_0,esk2_0,esk2_0),k1_tarski(esk3_0)))!=k2_xboole_0(k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_tarski(esk2_0)),k1_tarski(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18]), c_0_18])).
% 0.19/0.36  cnf(c_0_21, plain, (k2_xboole_0(k1_enumset1(X1,X1,X2),k2_xboole_0(k1_enumset1(X3,X3,X3),k1_tarski(X4)))=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.19/0.36  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_18])]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 23
% 0.19/0.36  # Proof object clause steps            : 12
% 0.19/0.36  # Proof object formula steps           : 11
% 0.19/0.36  # Proof object conjectures             : 7
% 0.19/0.36  # Proof object clause conjectures      : 4
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 5
% 0.19/0.36  # Proof object initial formulas used   : 5
% 0.19/0.36  # Proof object generating inferences   : 1
% 0.19/0.36  # Proof object simplifying inferences  : 11
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 5
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 5
% 0.19/0.36  # Removed in clause preprocessing      : 2
% 0.19/0.36  # Initial clauses in saturation        : 3
% 0.19/0.36  # Processed clauses                    : 23
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 11
% 0.19/0.36  # ...remaining for further processing  : 12
% 0.19/0.36  # Other redundant clauses eliminated   : 0
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 2
% 0.19/0.36  # Generated clauses                    : 52
% 0.19/0.36  # ...of the previous two non-trivial   : 41
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 52
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 0
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 7
% 0.19/0.36  #    Positive orientable unit clauses  : 0
% 0.19/0.36  #    Positive unorientable unit clauses: 7
% 0.19/0.36  #    Negative unit clauses             : 0
% 0.19/0.36  #    Non-unit-clauses                  : 0
% 0.19/0.36  # Current number of unprocessed clauses: 24
% 0.19/0.36  # ...number of literals in the above   : 24
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 7
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.36  # Unit Clause-clause subsumption calls : 3
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 44
% 0.19/0.36  # BW rewrite match successes           : 43
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 908
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.027 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.030 s
% 0.19/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
