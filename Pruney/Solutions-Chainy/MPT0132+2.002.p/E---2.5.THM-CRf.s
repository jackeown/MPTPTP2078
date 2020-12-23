%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:06 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  36 expanded)
%              Number of clauses        :   11 (  15 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  36 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t48_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_6,plain,(
    ! [X26,X27,X28,X29] : k2_enumset1(X26,X27,X28,X29) = k2_xboole_0(k2_tarski(X26,X27),k2_tarski(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_7,plain,(
    ! [X21,X22] : k2_tarski(X21,X22) = k2_xboole_0(k1_tarski(X21),k1_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(assume_negation,[status(cth)],[t48_enumset1])).

fof(c_0_9,plain,(
    ! [X23,X24,X25] : k1_enumset1(X23,X24,X25) = k2_xboole_0(k1_tarski(X23),k2_tarski(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_10,plain,(
    ! [X34,X35,X36,X37,X38] : k3_enumset1(X34,X35,X36,X37,X38) = k2_xboole_0(k1_tarski(X34),k2_enumset1(X35,X36,X37,X38)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_11,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,negated_conjecture,(
    k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k2_tarski(esk2_0,esk3_0),k1_enumset1(esk4_0,esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k2_tarski(esk2_0,esk3_0),k1_enumset1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_19,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] : k2_xboole_0(k2_xboole_0(X6,X7),X8) = k2_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)))) != k2_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_12]),c_0_18]),c_0_19])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:35:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.026 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t45_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 0.21/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.21/0.38  fof(t48_enumset1, conjecture, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 0.21/0.38  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.21/0.38  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.21/0.38  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.21/0.38  fof(c_0_6, plain, ![X26, X27, X28, X29]:k2_enumset1(X26,X27,X28,X29)=k2_xboole_0(k2_tarski(X26,X27),k2_tarski(X28,X29)), inference(variable_rename,[status(thm)],[t45_enumset1])).
% 0.21/0.38  fof(c_0_7, plain, ![X21, X22]:k2_tarski(X21,X22)=k2_xboole_0(k1_tarski(X21),k1_tarski(X22)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.21/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(assume_negation,[status(cth)],[t48_enumset1])).
% 0.21/0.38  fof(c_0_9, plain, ![X23, X24, X25]:k1_enumset1(X23,X24,X25)=k2_xboole_0(k1_tarski(X23),k2_tarski(X24,X25)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.21/0.38  fof(c_0_10, plain, ![X34, X35, X36, X37, X38]:k3_enumset1(X34,X35,X36,X37,X38)=k2_xboole_0(k1_tarski(X34),k2_enumset1(X35,X36,X37,X38)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.21/0.38  cnf(c_0_11, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.38  cnf(c_0_12, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.38  fof(c_0_13, negated_conjecture, k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k2_xboole_0(k2_tarski(esk2_0,esk3_0),k1_enumset1(esk4_0,esk5_0,esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.21/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_15, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_16, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 0.21/0.38  cnf(c_0_17, negated_conjecture, (k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k2_xboole_0(k2_tarski(esk2_0,esk3_0),k1_enumset1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.38  cnf(c_0_18, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))), inference(rw,[status(thm)],[c_0_14, c_0_12])).
% 0.21/0.38  cnf(c_0_19, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.38  fof(c_0_20, plain, ![X6, X7, X8]:k2_xboole_0(k2_xboole_0(X6,X7),X8)=k2_xboole_0(X6,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.21/0.38  cnf(c_0_21, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))))!=k2_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_12]), c_0_18]), c_0_19])).
% 0.21/0.38  cnf(c_0_22, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_23, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 24
% 0.21/0.38  # Proof object clause steps            : 11
% 0.21/0.38  # Proof object formula steps           : 13
% 0.21/0.38  # Proof object conjectures             : 6
% 0.21/0.38  # Proof object clause conjectures      : 3
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 6
% 0.21/0.38  # Proof object initial formulas used   : 6
% 0.21/0.38  # Proof object generating inferences   : 0
% 0.21/0.38  # Proof object simplifying inferences  : 10
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 9
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 12
% 0.21/0.38  # Removed in clause preprocessing      : 4
% 0.21/0.38  # Initial clauses in saturation        : 8
% 0.21/0.38  # Processed clauses                    : 2
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 1
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 0
% 0.21/0.38  # Generated clauses                    : 0
% 0.21/0.38  # ...of the previous two non-trivial   : 0
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 0
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 0
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 1
% 0.21/0.38  #    Positive orientable unit clauses  : 1
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 0
% 0.21/0.38  #    Non-unit-clauses                  : 0
% 0.21/0.38  # Current number of unprocessed clauses: 6
% 0.21/0.38  # ...number of literals in the above   : 14
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 4
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.38  # Unit Clause-clause subsumption calls : 0
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 0
% 0.21/0.38  # BW rewrite match successes           : 0
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 781
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.025 s
% 0.21/0.38  # System time              : 0.004 s
% 0.21/0.38  # Total time               : 0.029 s
% 0.21/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
