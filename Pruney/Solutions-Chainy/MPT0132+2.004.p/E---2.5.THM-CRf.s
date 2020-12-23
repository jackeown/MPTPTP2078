%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:06 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   20 (  42 expanded)
%              Number of clauses        :    9 (  17 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  42 expanded)
%              Number of equality atoms :   19 (  41 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t48_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_5,plain,(
    ! [X16,X17,X18] : k1_enumset1(X16,X17,X18) = k2_xboole_0(k2_tarski(X16,X17),k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_6,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k2_xboole_0(k1_tarski(X14),k1_tarski(X15)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(assume_negation,[status(cth)],[t48_enumset1])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12,X13] : k3_enumset1(X9,X10,X11,X12,X13) = k2_xboole_0(k1_enumset1(X9,X10,X11),k2_tarski(X12,X13)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

cnf(c_0_9,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,(
    k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_enumset1(esk3_0,esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_enumset1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_10]),c_0_13])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] : k2_xboole_0(k2_xboole_0(X6,X7),X8) = k2_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_17,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_tarski(esk3_0)),k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))) != k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_xboole_0(k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)),k1_tarski(esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_10]),c_0_13]),c_0_15])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_18]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.20/0.40  # and selection function SelectNewComplexAHP.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.049 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 0.20/0.40  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.40  fof(t48_enumset1, conjecture, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 0.20/0.40  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 0.20/0.40  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.40  fof(c_0_5, plain, ![X16, X17, X18]:k1_enumset1(X16,X17,X18)=k2_xboole_0(k2_tarski(X16,X17),k1_tarski(X18)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.20/0.40  fof(c_0_6, plain, ![X14, X15]:k2_tarski(X14,X15)=k2_xboole_0(k1_tarski(X14),k1_tarski(X15)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.40  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(assume_negation,[status(cth)],[t48_enumset1])).
% 0.20/0.40  fof(c_0_8, plain, ![X9, X10, X11, X12, X13]:k3_enumset1(X9,X10,X11,X12,X13)=k2_xboole_0(k1_enumset1(X9,X10,X11),k2_tarski(X12,X13)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.20/0.40  cnf(c_0_9, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.40  cnf(c_0_10, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.40  fof(c_0_11, negated_conjecture, k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_enumset1(esk3_0,esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.40  cnf(c_0_12, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_13, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.40  cnf(c_0_14, negated_conjecture, (k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_enumset1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_15, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_10]), c_0_13])).
% 0.20/0.40  fof(c_0_16, plain, ![X6, X7, X8]:k2_xboole_0(k2_xboole_0(X6,X7),X8)=k2_xboole_0(X6,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, (k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_tarski(esk3_0)),k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)))!=k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_xboole_0(k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)),k1_tarski(esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_10]), c_0_13]), c_0_15])).
% 0.20/0.40  cnf(c_0_18, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18]), c_0_18]), c_0_18])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 20
% 0.20/0.40  # Proof object clause steps            : 9
% 0.20/0.40  # Proof object formula steps           : 11
% 0.20/0.40  # Proof object conjectures             : 6
% 0.20/0.40  # Proof object clause conjectures      : 3
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 5
% 0.20/0.40  # Proof object initial formulas used   : 5
% 0.20/0.40  # Proof object generating inferences   : 0
% 0.20/0.40  # Proof object simplifying inferences  : 11
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 5
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 5
% 0.20/0.40  # Removed in clause preprocessing      : 3
% 0.20/0.40  # Initial clauses in saturation        : 2
% 0.20/0.40  # Processed clauses                    : 2
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 0
% 0.20/0.40  # ...remaining for further processing  : 2
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 1
% 0.20/0.40  # Generated clauses                    : 0
% 0.20/0.40  # ...of the previous two non-trivial   : 0
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 0
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 0
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 1
% 0.20/0.40  #    Positive orientable unit clauses  : 1
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 0
% 0.20/0.40  #    Non-unit-clauses                  : 0
% 0.20/0.40  # Current number of unprocessed clauses: 0
% 0.20/0.40  # ...number of literals in the above   : 0
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 4
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.40  # Unit Clause-clause subsumption calls : 0
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 4
% 0.20/0.40  # BW rewrite match successes           : 4
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 349
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.049 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.053 s
% 0.20/0.40  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
