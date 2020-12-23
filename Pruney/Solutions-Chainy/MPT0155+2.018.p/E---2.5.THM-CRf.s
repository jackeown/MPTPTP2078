%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:37 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   29 (  44 expanded)
%              Number of clauses        :   14 (  19 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  44 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(c_0_7,plain,(
    ! [X18,X19,X20,X21,X22] : k3_enumset1(X18,X19,X20,X21,X22) = k2_xboole_0(k2_tarski(X18,X19),k1_enumset1(X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_8,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t71_enumset1])).

fof(c_0_10,plain,(
    ! [X14,X15,X16,X17] : k2_enumset1(X14,X15,X16,X17) = k2_xboole_0(k1_tarski(X14),k1_enumset1(X15,X16,X17)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_11,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X11,X12,X13] : k1_enumset1(X11,X12,X13) = k2_xboole_0(k1_tarski(X11),k2_tarski(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_13,plain,(
    ! [X6,X7,X8,X9,X10] : k3_enumset1(X6,X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_tarski(X9,X10)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

cnf(c_0_14,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,negated_conjecture,(
    k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_15])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18]),c_0_15]),c_0_15])).

cnf(c_0_25,plain,
    ( k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_15]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X2,X3)) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.30  % Computer   : n007.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % WCLimit    : 600
% 0.09/0.30  % DateTime   : Tue Dec  1 09:43:36 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.30  # Version: 2.5pre002
% 0.09/0.30  # No SInE strategy applied
% 0.09/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.33  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.15/0.33  # and selection function SelectNewComplexAHP.
% 0.15/0.33  #
% 0.15/0.33  # Preprocessing time       : 0.026 s
% 0.15/0.33  # Presaturation interreduction done
% 0.15/0.33  
% 0.15/0.33  # Proof found!
% 0.15/0.33  # SZS status Theorem
% 0.15/0.33  # SZS output start CNFRefutation
% 0.15/0.33  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 0.15/0.33  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.15/0.33  fof(t71_enumset1, conjecture, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.15/0.33  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.15/0.33  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.33  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.15/0.33  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 0.15/0.33  fof(c_0_7, plain, ![X18, X19, X20, X21, X22]:k3_enumset1(X18,X19,X20,X21,X22)=k2_xboole_0(k2_tarski(X18,X19),k1_enumset1(X20,X21,X22)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.15/0.33  fof(c_0_8, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.15/0.33  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t71_enumset1])).
% 0.15/0.33  fof(c_0_10, plain, ![X14, X15, X16, X17]:k2_enumset1(X14,X15,X16,X17)=k2_xboole_0(k1_tarski(X14),k1_enumset1(X15,X16,X17)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.15/0.33  fof(c_0_11, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.15/0.33  fof(c_0_12, plain, ![X11, X12, X13]:k1_enumset1(X11,X12,X13)=k2_xboole_0(k1_tarski(X11),k2_tarski(X12,X13)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.15/0.33  fof(c_0_13, plain, ![X6, X7, X8, X9, X10]:k3_enumset1(X6,X7,X8,X9,X10)=k2_xboole_0(k1_enumset1(X6,X7,X8),k2_tarski(X9,X10)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.15/0.33  cnf(c_0_14, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.33  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.33  fof(c_0_16, negated_conjecture, k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.15/0.33  cnf(c_0_17, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.33  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.33  cnf(c_0_19, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.33  cnf(c_0_20, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.33  cnf(c_0_21, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X4,X5))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.15/0.33  cnf(c_0_22, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.33  cnf(c_0_23, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_15])).
% 0.15/0.33  cnf(c_0_24, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_18]), c_0_15]), c_0_15])).
% 0.15/0.33  cnf(c_0_25, plain, (k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X4,X5))=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_15]), c_0_21])).
% 0.15/0.33  cnf(c_0_26, negated_conjecture, (k2_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.15/0.33  cnf(c_0_27, plain, (k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X2,X3))=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.15/0.33  cnf(c_0_28, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])]), ['proof']).
% 0.15/0.33  # SZS output end CNFRefutation
% 0.15/0.33  # Proof object total steps             : 29
% 0.15/0.33  # Proof object clause steps            : 14
% 0.15/0.33  # Proof object formula steps           : 15
% 0.15/0.33  # Proof object conjectures             : 6
% 0.15/0.33  # Proof object clause conjectures      : 3
% 0.15/0.33  # Proof object formula conjectures     : 3
% 0.15/0.33  # Proof object initial clauses used    : 7
% 0.15/0.33  # Proof object initial formulas used   : 7
% 0.15/0.33  # Proof object generating inferences   : 1
% 0.15/0.33  # Proof object simplifying inferences  : 11
% 0.15/0.33  # Training examples: 0 positive, 0 negative
% 0.15/0.33  # Parsed axioms                        : 7
% 0.15/0.33  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.33  # Initial clauses                      : 7
% 0.15/0.33  # Removed in clause preprocessing      : 4
% 0.15/0.33  # Initial clauses in saturation        : 3
% 0.15/0.33  # Processed clauses                    : 7
% 0.15/0.33  # ...of these trivial                  : 0
% 0.15/0.33  # ...subsumed                          : 0
% 0.15/0.33  # ...remaining for further processing  : 7
% 0.15/0.33  # Other redundant clauses eliminated   : 0
% 0.15/0.33  # Clauses deleted for lack of memory   : 0
% 0.15/0.33  # Backward-subsumed                    : 0
% 0.15/0.33  # Backward-rewritten                   : 1
% 0.15/0.33  # Generated clauses                    : 9
% 0.15/0.33  # ...of the previous two non-trivial   : 6
% 0.15/0.33  # Contextual simplify-reflections      : 0
% 0.15/0.33  # Paramodulations                      : 9
% 0.15/0.33  # Factorizations                       : 0
% 0.15/0.33  # Equation resolutions                 : 0
% 0.15/0.33  # Propositional unsat checks           : 0
% 0.15/0.33  #    Propositional check models        : 0
% 0.15/0.33  #    Propositional check unsatisfiable : 0
% 0.15/0.33  #    Propositional clauses             : 0
% 0.15/0.33  #    Propositional clauses after purity: 0
% 0.15/0.33  #    Propositional unsat core size     : 0
% 0.15/0.33  #    Propositional preprocessing time  : 0.000
% 0.15/0.33  #    Propositional encoding time       : 0.000
% 0.15/0.33  #    Propositional solver time         : 0.000
% 0.15/0.33  #    Success case prop preproc time    : 0.000
% 0.15/0.33  #    Success case prop encoding time   : 0.000
% 0.15/0.33  #    Success case prop solver time     : 0.000
% 0.15/0.33  # Current number of processed clauses  : 3
% 0.15/0.33  #    Positive orientable unit clauses  : 1
% 0.15/0.33  #    Positive unorientable unit clauses: 2
% 0.15/0.33  #    Negative unit clauses             : 0
% 0.15/0.33  #    Non-unit-clauses                  : 0
% 0.15/0.33  # Current number of unprocessed clauses: 5
% 0.15/0.33  # ...number of literals in the above   : 5
% 0.15/0.33  # Current number of archived formulas  : 0
% 0.15/0.33  # Current number of archived clauses   : 8
% 0.15/0.33  # Clause-clause subsumption calls (NU) : 0
% 0.15/0.33  # Rec. Clause-clause subsumption calls : 0
% 0.15/0.33  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.33  # Unit Clause-clause subsumption calls : 0
% 0.15/0.33  # Rewrite failures with RHS unbound    : 0
% 0.15/0.33  # BW rewrite match attempts            : 18
% 0.15/0.33  # BW rewrite match successes           : 11
% 0.15/0.33  # Condensation attempts                : 0
% 0.15/0.33  # Condensation successes               : 0
% 0.15/0.33  # Termbank termtop insertions          : 466
% 0.15/0.33  
% 0.15/0.33  # -------------------------------------------------
% 0.15/0.33  # User time                : 0.026 s
% 0.15/0.33  # System time              : 0.002 s
% 0.15/0.33  # Total time               : 0.028 s
% 0.15/0.33  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
