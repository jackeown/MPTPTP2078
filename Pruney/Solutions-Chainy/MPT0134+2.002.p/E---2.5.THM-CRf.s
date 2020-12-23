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
% DateTime   : Thu Dec  3 10:35:07 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 238 expanded)
%              Number of clauses        :   18 (  97 expanded)
%              Number of leaves         :    7 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 ( 238 expanded)
%              Number of equality atoms :   32 ( 237 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_xboole_1,axiom,(
    ! [X1,X2,X3,X4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t50_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(c_0_7,plain,(
    ! [X6,X7,X8,X9] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X6,X7),X8),X9) = k2_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X8),X9)) ),
    inference(variable_rename,[status(thm)],[t113_xboole_1])).

fof(c_0_8,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X10,X11),k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] : k1_enumset1(X14,X15,X16) = k2_xboole_0(k2_tarski(X14,X15),k1_tarski(X16)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_10,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_xboole_0(k1_tarski(X12),k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(assume_negation,[status(cth)],[t50_enumset1])).

fof(c_0_12,plain,(
    ! [X17,X18,X19,X20] : k2_enumset1(X17,X18,X19,X20) = k2_xboole_0(k1_enumset1(X17,X18,X19),k1_tarski(X20)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X26,X27,X28,X29,X30] : k3_enumset1(X26,X27,X28,X29,X30) = k2_xboole_0(k2_tarski(X26,X27),k1_enumset1(X28,X29,X30)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_18,negated_conjecture,(
    k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))),k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14]),c_0_14]),c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_14]),c_0_14])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_25,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))) = k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_16]),c_0_14]),c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0)),k3_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0))),k1_tarski(esk5_0)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0)),k3_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0))),k1_tarski(esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_14]),c_0_24]),c_0_24])).

cnf(c_0_28,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5))) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)),k3_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0))),k1_tarski(esk5_0)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)),k3_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0))),k1_tarski(esk5_0))) != k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_tarski(X5))) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___300_C01_F1_SE_CS_SP_S0Y
% 0.12/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.026 s
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t113_xboole_1, axiom, ![X1, X2, X3, X4]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_xboole_1)).
% 0.12/0.38  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.12/0.38  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 0.12/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.12/0.38  fof(t50_enumset1, conjecture, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.12/0.38  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.12/0.38  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 0.12/0.38  fof(c_0_7, plain, ![X6, X7, X8, X9]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X6,X7),X8),X9)=k2_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X8),X9)), inference(variable_rename,[status(thm)],[t113_xboole_1])).
% 0.12/0.38  fof(c_0_8, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k5_xboole_0(k5_xboole_0(X10,X11),k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.12/0.38  fof(c_0_9, plain, ![X14, X15, X16]:k1_enumset1(X14,X15,X16)=k2_xboole_0(k2_tarski(X14,X15),k1_tarski(X16)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.12/0.38  fof(c_0_10, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_xboole_0(k1_tarski(X12),k1_tarski(X13)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.12/0.38  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(assume_negation,[status(cth)],[t50_enumset1])).
% 0.12/0.38  fof(c_0_12, plain, ![X17, X18, X19, X20]:k2_enumset1(X17,X18,X19,X20)=k2_xboole_0(k1_enumset1(X17,X18,X19),k1_tarski(X20)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.12/0.38  cnf(c_0_13, plain, (k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_15, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_16, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  fof(c_0_17, plain, ![X26, X27, X28, X29, X30]:k3_enumset1(X26,X27,X28,X29,X30)=k2_xboole_0(k2_tarski(X26,X27),k1_enumset1(X28,X29,X30)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.12/0.38  fof(c_0_18, negated_conjecture, k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.12/0.38  cnf(c_0_19, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_20, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4))=k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))),k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14]), c_0_14]), c_0_14]), c_0_14]), c_0_14])).
% 0.12/0.38  cnf(c_0_21, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_14]), c_0_14])).
% 0.12/0.38  cnf(c_0_22, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_24, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)))), inference(rw,[status(thm)],[c_0_19, c_0_14])).
% 0.12/0.38  cnf(c_0_25, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))=k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.38  cnf(c_0_26, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_16]), c_0_14]), c_0_14])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0)),k3_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0))),k1_tarski(esk5_0)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0)),k3_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0))),k1_tarski(esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_14]), c_0_24]), c_0_24])).
% 0.12/0.38  cnf(c_0_28, plain, (k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)))=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)))), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.12/0.38  cnf(c_0_29, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)))=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_26])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)),k3_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0))),k1_tarski(esk5_0)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)),k3_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0))),k1_tarski(esk5_0)))!=k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 0.12/0.38  cnf(c_0_31, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_tarski(X5)))=k3_enumset1(X1,X2,X3,X4,X5)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 33
% 0.12/0.38  # Proof object clause steps            : 18
% 0.12/0.38  # Proof object formula steps           : 15
% 0.12/0.38  # Proof object conjectures             : 7
% 0.12/0.38  # Proof object clause conjectures      : 4
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 7
% 0.12/0.38  # Proof object initial formulas used   : 7
% 0.12/0.38  # Proof object generating inferences   : 4
% 0.12/0.38  # Proof object simplifying inferences  : 21
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 8
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 8
% 0.12/0.38  # Removed in clause preprocessing      : 3
% 0.12/0.38  # Initial clauses in saturation        : 5
% 0.12/0.38  # Processed clauses                    : 16
% 0.12/0.38  # ...of these trivial                  : 3
% 0.12/0.38  # ...subsumed                          : 1
% 0.12/0.38  # ...remaining for further processing  : 12
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 2
% 0.12/0.38  # Generated clauses                    : 131
% 0.12/0.38  # ...of the previous two non-trivial   : 120
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 131
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 10
% 0.12/0.38  #    Positive orientable unit clauses  : 8
% 0.12/0.38  #    Positive unorientable unit clauses: 2
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 0
% 0.12/0.38  # Current number of unprocessed clauses: 109
% 0.12/0.38  # ...number of literals in the above   : 109
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 5
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.38  # Unit Clause-clause subsumption calls : 1
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 19
% 0.12/0.38  # BW rewrite match successes           : 3
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 15202
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.033 s
% 0.12/0.38  # System time              : 0.003 s
% 0.12/0.38  # Total time               : 0.037 s
% 0.12/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
