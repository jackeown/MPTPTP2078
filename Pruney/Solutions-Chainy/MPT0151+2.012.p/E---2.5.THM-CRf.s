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
% DateTime   : Thu Dec  3 10:35:27 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  50 expanded)
%              Number of clauses        :   12 (  21 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  50 expanded)
%              Number of equality atoms :   24 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(assume_negation,[status(cth)],[t67_enumset1])).

fof(c_0_7,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33] : k6_enumset1(X26,X27,X28,X29,X30,X31,X32,X33) = k2_xboole_0(k2_tarski(X26,X27),k4_enumset1(X28,X29,X30,X31,X32,X33)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

fof(c_0_8,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_xboole_0(k1_tarski(X12),k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_9,plain,(
    ! [X14,X15,X16,X17,X18,X19] : k4_enumset1(X14,X15,X16,X17,X18,X19) = k2_xboole_0(k1_tarski(X14),k3_enumset1(X15,X16,X17,X18,X19)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_10,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X20,X21,X22,X23,X24,X25] : k4_enumset1(X20,X21,X22,X23,X24,X25) = k2_xboole_0(k3_enumset1(X20,X21,X22,X23,X24),k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_15,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k3_enumset1(X4,X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

fof(c_0_17,plain,(
    ! [X9,X10,X11] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_18,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_xboole_0(k1_tarski(esk3_0),k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))) != k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_12]),c_0_13]),c_0_16])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0)))) != k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_xboole_0(k1_tarski(X6),X7)) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),X7)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:49:11 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.026 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t67_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 0.21/0.39  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 0.21/0.39  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.21/0.39  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 0.21/0.39  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.21/0.39  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.21/0.39  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(assume_negation,[status(cth)],[t67_enumset1])).
% 0.21/0.39  fof(c_0_7, plain, ![X26, X27, X28, X29, X30, X31, X32, X33]:k6_enumset1(X26,X27,X28,X29,X30,X31,X32,X33)=k2_xboole_0(k2_tarski(X26,X27),k4_enumset1(X28,X29,X30,X31,X32,X33)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 0.21/0.39  fof(c_0_8, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_xboole_0(k1_tarski(X12),k1_tarski(X13)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.21/0.39  fof(c_0_9, plain, ![X14, X15, X16, X17, X18, X19]:k4_enumset1(X14,X15,X16,X17,X18,X19)=k2_xboole_0(k1_tarski(X14),k3_enumset1(X15,X16,X17,X18,X19)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.21/0.39  fof(c_0_10, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.21/0.39  cnf(c_0_11, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_12, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_13, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  fof(c_0_14, plain, ![X20, X21, X22, X23, X24, X25]:k4_enumset1(X20,X21,X22,X23,X24,X25)=k2_xboole_0(k3_enumset1(X20,X21,X22,X23,X24),k1_tarski(X25)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.21/0.39  cnf(c_0_15, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_16, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k3_enumset1(X4,X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.21/0.39  fof(c_0_17, plain, ![X9, X10, X11]:k2_xboole_0(k2_xboole_0(X9,X10),X11)=k2_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.21/0.39  cnf(c_0_18, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_xboole_0(k1_tarski(esk3_0),k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)))!=k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_12]), c_0_13]), c_0_16])).
% 0.21/0.39  cnf(c_0_20, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_21, plain, (k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(rw,[status(thm)],[c_0_18, c_0_13])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0))))!=k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20])).
% 0.21/0.39  cnf(c_0_23, plain, (k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_xboole_0(k1_tarski(X6),X7))=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),X7))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_20])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_21])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 25
% 0.21/0.39  # Proof object clause steps            : 12
% 0.21/0.39  # Proof object formula steps           : 13
% 0.21/0.39  # Proof object conjectures             : 7
% 0.21/0.39  # Proof object clause conjectures      : 4
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 6
% 0.21/0.39  # Proof object initial formulas used   : 6
% 0.21/0.39  # Proof object generating inferences   : 1
% 0.21/0.39  # Proof object simplifying inferences  : 12
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 6
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 6
% 0.21/0.39  # Removed in clause preprocessing      : 3
% 0.21/0.39  # Initial clauses in saturation        : 3
% 0.21/0.39  # Processed clauses                    : 7
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 0
% 0.21/0.39  # ...remaining for further processing  : 7
% 0.21/0.39  # Other redundant clauses eliminated   : 0
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 1
% 0.21/0.39  # Generated clauses                    : 3
% 0.21/0.39  # ...of the previous two non-trivial   : 1
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 3
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 0
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 3
% 0.21/0.39  #    Positive orientable unit clauses  : 3
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 0
% 0.21/0.39  #    Non-unit-clauses                  : 0
% 0.21/0.39  # Current number of unprocessed clauses: 0
% 0.21/0.39  # ...number of literals in the above   : 0
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 7
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.39  # Unit Clause-clause subsumption calls : 0
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 1
% 0.21/0.39  # BW rewrite match successes           : 1
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 582
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.024 s
% 0.21/0.39  # System time              : 0.005 s
% 0.21/0.39  # Total time               : 0.029 s
% 0.21/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
