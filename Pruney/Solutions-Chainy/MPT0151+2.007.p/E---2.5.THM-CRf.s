%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:27 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   27 (  68 expanded)
%              Number of clauses        :   14 (  29 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  68 expanded)
%              Number of equality atoms :   26 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t67_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(t54_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(t113_xboole_1,axiom,(
    ! [X1,X2,X3,X4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16] : k2_enumset1(X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X16)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_7,plain,(
    ! [X17,X18] : k2_tarski(X17,X18) = k2_xboole_0(k1_tarski(X17),k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(assume_negation,[status(cth)],[t67_enumset1])).

fof(c_0_9,plain,(
    ! [X19,X20,X21,X22,X23,X24] : k4_enumset1(X19,X20,X21,X22,X23,X24) = k2_xboole_0(k2_enumset1(X19,X20,X21,X22),k2_tarski(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t54_enumset1])).

cnf(c_0_10,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

fof(c_0_15,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32] : k6_enumset1(X25,X26,X27,X28,X29,X30,X31,X32) = k2_xboole_0(k2_tarski(X25,X26),k4_enumset1(X27,X28,X29,X30,X31,X32)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

cnf(c_0_16,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_11]),c_0_14])).

fof(c_0_18,plain,(
    ! [X9,X10,X11,X12] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X9,X10),X11),X12) = k2_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) ),
    inference(variable_rename,[status(thm)],[t113_xboole_1])).

cnf(c_0_19,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_11]),c_0_17])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_11]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)))),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0))) != k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)),X5) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X3,X4),X5)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_21])).

cnf(c_0_25,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))),k2_xboole_0(k1_tarski(X7),k1_tarski(X8))))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_21]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.07/0.27  % Computer   : n005.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 14:59:02 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.11/0.27  # Version: 2.5pre002
% 0.11/0.27  # No SInE strategy applied
% 0.11/0.27  # Trying AutoSched0 for 299 seconds
% 0.11/0.28  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.28  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.28  #
% 0.11/0.28  # Preprocessing time       : 0.015 s
% 0.11/0.28  # Presaturation interreduction done
% 0.11/0.28  
% 0.11/0.28  # Proof found!
% 0.11/0.28  # SZS status Theorem
% 0.11/0.28  # SZS output start CNFRefutation
% 0.11/0.28  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.11/0.28  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.11/0.28  fof(t67_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 0.11/0.28  fof(t54_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 0.11/0.28  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 0.11/0.28  fof(t113_xboole_1, axiom, ![X1, X2, X3, X4]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_xboole_1)).
% 0.11/0.28  fof(c_0_6, plain, ![X13, X14, X15, X16]:k2_enumset1(X13,X14,X15,X16)=k2_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X16)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.11/0.28  fof(c_0_7, plain, ![X17, X18]:k2_tarski(X17,X18)=k2_xboole_0(k1_tarski(X17),k1_tarski(X18)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.11/0.28  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(assume_negation,[status(cth)],[t67_enumset1])).
% 0.11/0.28  fof(c_0_9, plain, ![X19, X20, X21, X22, X23, X24]:k4_enumset1(X19,X20,X21,X22,X23,X24)=k2_xboole_0(k2_enumset1(X19,X20,X21,X22),k2_tarski(X23,X24)), inference(variable_rename,[status(thm)],[t54_enumset1])).
% 0.11/0.28  cnf(c_0_10, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.28  cnf(c_0_11, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.28  fof(c_0_12, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.11/0.28  cnf(c_0_13, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.28  cnf(c_0_14, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_11])).
% 0.11/0.28  fof(c_0_15, plain, ![X25, X26, X27, X28, X29, X30, X31, X32]:k6_enumset1(X25,X26,X27,X28,X29,X30,X31,X32)=k2_xboole_0(k2_tarski(X25,X26),k4_enumset1(X27,X28,X29,X30,X31,X32)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 0.11/0.28  cnf(c_0_16, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.28  cnf(c_0_17, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_11]), c_0_14])).
% 0.11/0.28  fof(c_0_18, plain, ![X9, X10, X11, X12]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X9,X10),X11),X12)=k2_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)), inference(variable_rename,[status(thm)],[t113_xboole_1])).
% 0.11/0.28  cnf(c_0_19, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.28  cnf(c_0_20, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_11]), c_0_17])).
% 0.11/0.28  cnf(c_0_21, plain, (k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.11/0.28  cnf(c_0_22, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))),k2_xboole_0(k1_tarski(X7),k1_tarski(X8))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_11]), c_0_17])).
% 0.11/0.28  cnf(c_0_23, negated_conjecture, (k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)))),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0)))!=k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.11/0.28  cnf(c_0_24, plain, (k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)),X5)=k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X3,X4),X5))), inference(spm,[status(thm)],[c_0_21, c_0_21])).
% 0.11/0.28  cnf(c_0_25, plain, (k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.11/0.28  cnf(c_0_26, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_21]), c_0_25])]), ['proof']).
% 0.11/0.28  # SZS output end CNFRefutation
% 0.11/0.28  # Proof object total steps             : 27
% 0.11/0.28  # Proof object clause steps            : 14
% 0.11/0.28  # Proof object formula steps           : 13
% 0.11/0.28  # Proof object conjectures             : 7
% 0.11/0.28  # Proof object clause conjectures      : 4
% 0.11/0.28  # Proof object formula conjectures     : 3
% 0.11/0.28  # Proof object initial clauses used    : 6
% 0.11/0.28  # Proof object initial formulas used   : 6
% 0.11/0.28  # Proof object generating inferences   : 1
% 0.11/0.28  # Proof object simplifying inferences  : 14
% 0.11/0.28  # Training examples: 0 positive, 0 negative
% 0.11/0.28  # Parsed axioms                        : 6
% 0.11/0.28  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.28  # Initial clauses                      : 6
% 0.11/0.28  # Removed in clause preprocessing      : 3
% 0.11/0.28  # Initial clauses in saturation        : 3
% 0.11/0.28  # Processed clauses                    : 7
% 0.11/0.28  # ...of these trivial                  : 0
% 0.11/0.28  # ...subsumed                          : 0
% 0.11/0.28  # ...remaining for further processing  : 7
% 0.11/0.28  # Other redundant clauses eliminated   : 0
% 0.11/0.28  # Clauses deleted for lack of memory   : 0
% 0.11/0.28  # Backward-subsumed                    : 0
% 0.11/0.28  # Backward-rewritten                   : 1
% 0.11/0.28  # Generated clauses                    : 15
% 0.11/0.28  # ...of the previous two non-trivial   : 4
% 0.11/0.28  # Contextual simplify-reflections      : 0
% 0.11/0.28  # Paramodulations                      : 15
% 0.11/0.28  # Factorizations                       : 0
% 0.11/0.28  # Equation resolutions                 : 0
% 0.11/0.28  # Propositional unsat checks           : 0
% 0.11/0.28  #    Propositional check models        : 0
% 0.11/0.28  #    Propositional check unsatisfiable : 0
% 0.11/0.28  #    Propositional clauses             : 0
% 0.11/0.28  #    Propositional clauses after purity: 0
% 0.11/0.28  #    Propositional unsat core size     : 0
% 0.11/0.28  #    Propositional preprocessing time  : 0.000
% 0.11/0.28  #    Propositional encoding time       : 0.000
% 0.11/0.28  #    Propositional solver time         : 0.000
% 0.11/0.28  #    Success case prop preproc time    : 0.000
% 0.11/0.28  #    Success case prop encoding time   : 0.000
% 0.11/0.28  #    Success case prop solver time     : 0.000
% 0.11/0.28  # Current number of processed clauses  : 3
% 0.11/0.28  #    Positive orientable unit clauses  : 3
% 0.11/0.28  #    Positive unorientable unit clauses: 0
% 0.11/0.28  #    Negative unit clauses             : 0
% 0.11/0.28  #    Non-unit-clauses                  : 0
% 0.11/0.28  # Current number of unprocessed clauses: 3
% 0.11/0.28  # ...number of literals in the above   : 3
% 0.11/0.28  # Current number of archived formulas  : 0
% 0.11/0.28  # Current number of archived clauses   : 7
% 0.11/0.28  # Clause-clause subsumption calls (NU) : 0
% 0.11/0.28  # Rec. Clause-clause subsumption calls : 0
% 0.11/0.28  # Non-unit clause-clause subsumptions  : 0
% 0.11/0.28  # Unit Clause-clause subsumption calls : 0
% 0.11/0.28  # Rewrite failures with RHS unbound    : 0
% 0.11/0.28  # BW rewrite match attempts            : 3
% 0.11/0.28  # BW rewrite match successes           : 1
% 0.11/0.28  # Condensation attempts                : 0
% 0.11/0.28  # Condensation successes               : 0
% 0.11/0.28  # Termbank termtop insertions          : 870
% 0.11/0.28  
% 0.11/0.28  # -------------------------------------------------
% 0.11/0.28  # User time                : 0.015 s
% 0.11/0.28  # System time              : 0.002 s
% 0.11/0.28  # Total time               : 0.018 s
% 0.11/0.28  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
