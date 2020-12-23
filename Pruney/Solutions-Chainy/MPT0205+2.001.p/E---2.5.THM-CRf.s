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
% DateTime   : Thu Dec  3 10:36:39 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   22 (  34 expanded)
%              Number of clauses        :   11 (  15 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t131_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(assume_negation,[status(cth)],[t131_enumset1])).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20,X21] : k7_enumset1(X13,X14,X15,X16,X17,X18,X19,X20,X21) = k2_xboole_0(k2_enumset1(X13,X14,X15,X16),k3_enumset1(X17,X18,X19,X20,X21)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

fof(c_0_7,plain,(
    ! [X22,X23,X24,X25,X26] : k3_enumset1(X22,X23,X24,X25,X26) = k2_xboole_0(k1_tarski(X22),k2_enumset1(X23,X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_8,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X27,X28,X29,X30,X31] : k3_enumset1(X27,X28,X29,X30,X31) = k2_xboole_0(k2_enumset1(X27,X28,X29,X30),k1_tarski(X31)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

cnf(c_0_12,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_enumset1(X6,X7,X8,X9))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_14,plain,(
    ! [X10,X11,X12] : k2_xboole_0(k2_xboole_0(X10,X11),X12) = k2_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_15,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0))) != k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0)),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_10]),c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0))) != k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6)) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),X6)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.31  % Computer   : n019.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 14:07:22 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  # Version: 2.5pre002
% 0.10/0.31  # No SInE strategy applied
% 0.10/0.31  # Trying AutoSched0 for 299 seconds
% 0.15/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.15/0.34  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.15/0.34  #
% 0.15/0.34  # Preprocessing time       : 0.025 s
% 0.15/0.34  # Presaturation interreduction done
% 0.15/0.34  
% 0.15/0.34  # Proof found!
% 0.15/0.34  # SZS status Theorem
% 0.15/0.34  # SZS output start CNFRefutation
% 0.15/0.34  fof(t131_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_enumset1)).
% 0.15/0.34  fof(l142_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l142_enumset1)).
% 0.15/0.34  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.15/0.34  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 0.15/0.34  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.15/0.34  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(assume_negation,[status(cth)],[t131_enumset1])).
% 0.15/0.34  fof(c_0_6, plain, ![X13, X14, X15, X16, X17, X18, X19, X20, X21]:k7_enumset1(X13,X14,X15,X16,X17,X18,X19,X20,X21)=k2_xboole_0(k2_enumset1(X13,X14,X15,X16),k3_enumset1(X17,X18,X19,X20,X21)), inference(variable_rename,[status(thm)],[l142_enumset1])).
% 0.15/0.34  fof(c_0_7, plain, ![X22, X23, X24, X25, X26]:k3_enumset1(X22,X23,X24,X25,X26)=k2_xboole_0(k1_tarski(X22),k2_enumset1(X23,X24,X25,X26)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.15/0.34  fof(c_0_8, negated_conjecture, k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.15/0.34  cnf(c_0_9, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.15/0.34  cnf(c_0_10, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.34  fof(c_0_11, plain, ![X27, X28, X29, X30, X31]:k3_enumset1(X27,X28,X29,X30,X31)=k2_xboole_0(k2_enumset1(X27,X28,X29,X30),k1_tarski(X31)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.15/0.34  cnf(c_0_12, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.34  cnf(c_0_13, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_enumset1(X6,X7,X8,X9)))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.15/0.34  fof(c_0_14, plain, ![X10, X11, X12]:k2_xboole_0(k2_xboole_0(X10,X11),X12)=k2_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.15/0.34  cnf(c_0_15, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  cnf(c_0_16, negated_conjecture, (k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0)))!=k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0)),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_10]), c_0_13])).
% 0.15/0.34  cnf(c_0_17, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.34  cnf(c_0_18, plain, (k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(rw,[status(thm)],[c_0_15, c_0_10])).
% 0.15/0.34  cnf(c_0_19, negated_conjecture, (k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0)))!=k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),k2_enumset1(esk6_0,esk7_0,esk8_0,esk9_0)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.15/0.34  cnf(c_0_20, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6))=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),X6))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_17])).
% 0.15/0.34  cnf(c_0_21, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])]), ['proof']).
% 0.15/0.34  # SZS output end CNFRefutation
% 0.15/0.34  # Proof object total steps             : 22
% 0.15/0.34  # Proof object clause steps            : 11
% 0.15/0.34  # Proof object formula steps           : 11
% 0.15/0.34  # Proof object conjectures             : 7
% 0.15/0.34  # Proof object clause conjectures      : 4
% 0.15/0.34  # Proof object formula conjectures     : 3
% 0.15/0.34  # Proof object initial clauses used    : 5
% 0.15/0.34  # Proof object initial formulas used   : 5
% 0.15/0.34  # Proof object generating inferences   : 1
% 0.15/0.34  # Proof object simplifying inferences  : 8
% 0.15/0.34  # Training examples: 0 positive, 0 negative
% 0.15/0.34  # Parsed axioms                        : 5
% 0.15/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.34  # Initial clauses                      : 5
% 0.15/0.34  # Removed in clause preprocessing      : 2
% 0.15/0.34  # Initial clauses in saturation        : 3
% 0.15/0.34  # Processed clauses                    : 7
% 0.15/0.34  # ...of these trivial                  : 0
% 0.15/0.34  # ...subsumed                          : 0
% 0.15/0.34  # ...remaining for further processing  : 7
% 0.15/0.34  # Other redundant clauses eliminated   : 0
% 0.15/0.34  # Clauses deleted for lack of memory   : 0
% 0.15/0.34  # Backward-subsumed                    : 0
% 0.15/0.34  # Backward-rewritten                   : 1
% 0.15/0.34  # Generated clauses                    : 3
% 0.15/0.34  # ...of the previous two non-trivial   : 1
% 0.15/0.34  # Contextual simplify-reflections      : 0
% 0.15/0.34  # Paramodulations                      : 3
% 0.15/0.34  # Factorizations                       : 0
% 0.15/0.34  # Equation resolutions                 : 0
% 0.15/0.34  # Propositional unsat checks           : 0
% 0.15/0.34  #    Propositional check models        : 0
% 0.15/0.34  #    Propositional check unsatisfiable : 0
% 0.15/0.34  #    Propositional clauses             : 0
% 0.15/0.34  #    Propositional clauses after purity: 0
% 0.15/0.34  #    Propositional unsat core size     : 0
% 0.15/0.34  #    Propositional preprocessing time  : 0.000
% 0.15/0.34  #    Propositional encoding time       : 0.000
% 0.15/0.34  #    Propositional solver time         : 0.000
% 0.15/0.34  #    Success case prop preproc time    : 0.000
% 0.15/0.34  #    Success case prop encoding time   : 0.000
% 0.15/0.34  #    Success case prop solver time     : 0.000
% 0.15/0.34  # Current number of processed clauses  : 3
% 0.15/0.34  #    Positive orientable unit clauses  : 3
% 0.15/0.34  #    Positive unorientable unit clauses: 0
% 0.15/0.34  #    Negative unit clauses             : 0
% 0.15/0.34  #    Non-unit-clauses                  : 0
% 0.15/0.34  # Current number of unprocessed clauses: 0
% 0.15/0.34  # ...number of literals in the above   : 0
% 0.15/0.34  # Current number of archived formulas  : 0
% 0.15/0.34  # Current number of archived clauses   : 6
% 0.15/0.34  # Clause-clause subsumption calls (NU) : 0
% 0.15/0.34  # Rec. Clause-clause subsumption calls : 0
% 0.15/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.34  # Unit Clause-clause subsumption calls : 0
% 0.15/0.34  # Rewrite failures with RHS unbound    : 0
% 0.15/0.34  # BW rewrite match attempts            : 1
% 0.15/0.34  # BW rewrite match successes           : 1
% 0.15/0.34  # Condensation attempts                : 0
% 0.15/0.34  # Condensation successes               : 0
% 0.15/0.34  # Termbank termtop insertions          : 533
% 0.15/0.34  
% 0.15/0.34  # -------------------------------------------------
% 0.15/0.34  # User time                : 0.026 s
% 0.15/0.34  # System time              : 0.003 s
% 0.15/0.34  # Total time               : 0.029 s
% 0.15/0.34  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
