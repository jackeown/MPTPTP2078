%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:26 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 200 expanded)
%              Number of clauses        :   23 (  89 expanded)
%              Number of leaves         :    9 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :   42 ( 200 expanded)
%              Number of equality atoms :   41 ( 199 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t55_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(c_0_9,plain,(
    ! [X20,X21] : k2_xboole_0(k3_xboole_0(X20,X21),k4_xboole_0(X20,X21)) = X20 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_10,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_11,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X22,X23,X24] : k4_xboole_0(X22,k4_xboole_0(X23,X24)) = k2_xboole_0(k4_xboole_0(X22,X23),k3_xboole_0(X22,X24)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_14,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_15]),c_0_18]),c_0_12])).

fof(c_0_23,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),X9) = k4_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_21]),c_0_12]),c_0_22])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_25]),c_0_18])).

fof(c_0_28,plain,(
    ! [X10,X11,X12] : k4_xboole_0(k2_xboole_0(X10,X11),X12) = k2_xboole_0(k4_xboole_0(X10,X12),k4_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

fof(c_0_29,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k3_xboole_0(X13,X14)) = k4_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_26]),c_0_27])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t55_xboole_1])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_24])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_19])).

fof(c_0_36,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k3_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X3,X1),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_12])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_12]),c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.19/0.44  # and selection function SelectNewComplexAHP.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.027 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.19/0.44  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.44  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.19/0.44  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.44  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.44  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.19/0.44  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.19/0.44  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.44  fof(t55_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 0.19/0.44  fof(c_0_9, plain, ![X20, X21]:k2_xboole_0(k3_xboole_0(X20,X21),k4_xboole_0(X20,X21))=X20, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.19/0.44  fof(c_0_10, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.44  cnf(c_0_11, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.44  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.44  fof(c_0_13, plain, ![X22, X23, X24]:k4_xboole_0(X22,k4_xboole_0(X23,X24))=k2_xboole_0(k4_xboole_0(X22,X23),k3_xboole_0(X22,X24)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.19/0.44  cnf(c_0_14, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.44  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  fof(c_0_16, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.44  fof(c_0_17, plain, ![X6, X7]:k2_xboole_0(X6,k4_xboole_0(X7,X6))=k2_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.44  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.44  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_20, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_21, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.44  cnf(c_0_22, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_19]), c_0_15]), c_0_18]), c_0_12])).
% 0.19/0.44  fof(c_0_23, plain, ![X8, X9]:k4_xboole_0(k2_xboole_0(X8,X9),X9)=k4_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.19/0.44  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_21]), c_0_12]), c_0_22])).
% 0.19/0.44  cnf(c_0_25, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.44  cnf(c_0_26, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_19, c_0_24])).
% 0.19/0.44  cnf(c_0_27, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_25]), c_0_18])).
% 0.19/0.44  fof(c_0_28, plain, ![X10, X11, X12]:k4_xboole_0(k2_xboole_0(X10,X11),X12)=k2_xboole_0(k4_xboole_0(X10,X12),k4_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.19/0.44  fof(c_0_29, plain, ![X13, X14]:k4_xboole_0(X13,k3_xboole_0(X13,X14))=k4_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.44  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_26]), c_0_27])).
% 0.19/0.44  fof(c_0_31, negated_conjecture, ~(![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t55_xboole_1])).
% 0.19/0.44  cnf(c_0_32, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_33, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  cnf(c_0_34, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_24])).
% 0.19/0.44  cnf(c_0_35, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_19])).
% 0.19/0.44  fof(c_0_36, negated_conjecture, k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.19/0.44  cnf(c_0_37, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k3_xboole_0(X1,X2)))=k4_xboole_0(k2_xboole_0(X3,X1),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_12])).
% 0.19/0.44  cnf(c_0_38, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.44  cnf(c_0_40, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_12]), c_0_20])).
% 0.19/0.44  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 42
% 0.19/0.44  # Proof object clause steps            : 23
% 0.19/0.44  # Proof object formula steps           : 19
% 0.19/0.44  # Proof object conjectures             : 5
% 0.19/0.44  # Proof object clause conjectures      : 2
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 9
% 0.19/0.44  # Proof object initial formulas used   : 9
% 0.19/0.44  # Proof object generating inferences   : 11
% 0.19/0.44  # Proof object simplifying inferences  : 14
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 10
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 10
% 0.19/0.44  # Removed in clause preprocessing      : 0
% 0.19/0.44  # Initial clauses in saturation        : 10
% 0.19/0.44  # Processed clauses                    : 709
% 0.19/0.44  # ...of these trivial                  : 177
% 0.19/0.44  # ...subsumed                          : 376
% 0.19/0.44  # ...remaining for further processing  : 156
% 0.19/0.44  # Other redundant clauses eliminated   : 0
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 0
% 0.19/0.44  # Backward-rewritten                   : 37
% 0.19/0.44  # Generated clauses                    : 9714
% 0.19/0.44  # ...of the previous two non-trivial   : 5556
% 0.19/0.44  # Contextual simplify-reflections      : 0
% 0.19/0.44  # Paramodulations                      : 9714
% 0.19/0.44  # Factorizations                       : 0
% 0.19/0.44  # Equation resolutions                 : 0
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 109
% 0.19/0.44  #    Positive orientable unit clauses  : 104
% 0.19/0.44  #    Positive unorientable unit clauses: 5
% 0.19/0.44  #    Negative unit clauses             : 0
% 0.19/0.44  #    Non-unit-clauses                  : 0
% 0.19/0.44  # Current number of unprocessed clauses: 4725
% 0.19/0.44  # ...number of literals in the above   : 4725
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 47
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.44  # Unit Clause-clause subsumption calls : 24
% 0.19/0.44  # Rewrite failures with RHS unbound    : 48
% 0.19/0.44  # BW rewrite match attempts            : 268
% 0.19/0.44  # BW rewrite match successes           : 128
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 74467
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.099 s
% 0.19/0.44  # System time              : 0.005 s
% 0.19/0.44  # Total time               : 0.104 s
% 0.19/0.44  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
