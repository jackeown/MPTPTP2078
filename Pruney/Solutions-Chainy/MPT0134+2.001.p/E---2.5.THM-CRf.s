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
% DateTime   : Thu Dec  3 10:35:07 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  40 expanded)
%              Number of clauses        :   14 (  19 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  40 expanded)
%              Number of equality atoms :   28 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t50_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_7,plain,(
    ! [X13,X14,X15] : k1_enumset1(X13,X14,X15) = k2_xboole_0(k1_tarski(X13),k2_tarski(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_8,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_xboole_0(k1_tarski(X11),k1_tarski(X12)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_9,plain,(
    ! [X16,X17,X18,X19] : k2_enumset1(X16,X17,X18,X19) = k2_xboole_0(k1_tarski(X16),k1_enumset1(X17,X18,X19)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_10,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(assume_negation,[status(cth)],[t50_enumset1])).

fof(c_0_13,plain,(
    ! [X20,X21,X22,X23,X24] : k3_enumset1(X20,X21,X22,X23,X24) = k2_xboole_0(k1_tarski(X20),k2_enumset1(X21,X22,X23,X24)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_16,negated_conjecture,(
    k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_20,plain,(
    ! [X8,X9,X10] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_21,negated_conjecture,
    ( k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))))) != k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)))),k1_tarski(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_18]),c_0_22])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    c_0_23).

cnf(c_0_27,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    c_0_24).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(ar,[status(thm)],[c_0_25,c_0_26,c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.20/0.37  # and selection function SelectNewComplexAHP.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.026 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.20/0.37  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.37  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.20/0.37  fof(t50_enumset1, conjecture, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.20/0.37  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.20/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.37  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.37  fof(c_0_7, plain, ![X13, X14, X15]:k1_enumset1(X13,X14,X15)=k2_xboole_0(k1_tarski(X13),k2_tarski(X14,X15)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.20/0.37  fof(c_0_8, plain, ![X11, X12]:k2_tarski(X11,X12)=k2_xboole_0(k1_tarski(X11),k1_tarski(X12)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.37  fof(c_0_9, plain, ![X16, X17, X18, X19]:k2_enumset1(X16,X17,X18,X19)=k2_xboole_0(k1_tarski(X16),k1_enumset1(X17,X18,X19)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.20/0.37  cnf(c_0_10, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_11, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(assume_negation,[status(cth)],[t50_enumset1])).
% 0.20/0.37  fof(c_0_13, plain, ![X20, X21, X22, X23, X24]:k3_enumset1(X20,X21,X22,X23,X24)=k2_xboole_0(k1_tarski(X20),k2_enumset1(X21,X22,X23,X24)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.20/0.37  cnf(c_0_14, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_15, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.37  fof(c_0_16, negated_conjecture, k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.37  cnf(c_0_17, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_18, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.37  fof(c_0_19, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.37  fof(c_0_20, plain, ![X8, X9, X10]:k2_xboole_0(k2_xboole_0(X8,X9),X10)=k2_xboole_0(X8,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_22, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.37  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_24, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)))))!=k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)))),k1_tarski(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_18]), c_0_22])).
% 0.20/0.37  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), c_0_23).
% 0.20/0.37  cnf(c_0_27, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), c_0_24).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, ($false), inference(ar,[status(thm)],[c_0_25, c_0_26, c_0_27]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 29
% 0.20/0.37  # Proof object clause steps            : 14
% 0.20/0.37  # Proof object formula steps           : 15
% 0.20/0.37  # Proof object conjectures             : 6
% 0.20/0.37  # Proof object clause conjectures      : 3
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 7
% 0.20/0.37  # Proof object initial formulas used   : 7
% 0.20/0.37  # Proof object generating inferences   : 0
% 0.20/0.37  # Proof object simplifying inferences  : 6
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 7
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 7
% 0.20/0.37  # Removed in clause preprocessing      : 4
% 0.20/0.37  # Initial clauses in saturation        : 3
% 0.20/0.37  # Processed clauses                    : 1
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 0
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 0
% 0.20/0.37  # ...of the previous two non-trivial   : 0
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 0
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 0
% 0.20/0.37  #    Positive orientable unit clauses  : 0
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 0
% 0.20/0.37  #    Non-unit-clauses                  : 0
% 0.20/0.37  # Current number of unprocessed clauses: 2
% 0.20/0.37  # ...number of literals in the above   : 2
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 4
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 407
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.027 s
% 0.20/0.37  # System time              : 0.002 s
% 0.20/0.37  # Total time               : 0.029 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
