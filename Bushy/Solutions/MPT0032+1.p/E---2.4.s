%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t25_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:24 EDT 2019

% Result     : Theorem 151.27s
% Output     : CNFRefutation 151.27s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 537 expanded)
%              Number of clauses        :   33 ( 246 expanded)
%              Number of leaves         :    9 ( 145 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 537 expanded)
%              Number of equality atoms :   51 ( 536 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',t4_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',idempotence_k2_xboole_0)).

fof(t25_xboole_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)),k3_xboole_0(X3,X1)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)),k2_xboole_0(X3,X1)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',t25_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',commutativity_k2_xboole_0)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',t22_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',commutativity_k3_xboole_0)).

fof(t24_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',t24_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',t16_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t25_xboole_1.p',idempotence_k3_xboole_0)).

fof(c_0_9,plain,(
    ! [X21,X22,X23] : k2_xboole_0(k2_xboole_0(X21,X22),X23) = k2_xboole_0(X21,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_10,plain,(
    ! [X11] : k2_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)),k3_xboole_0(X3,X1)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)),k2_xboole_0(X3,X1)) ),
    inference(assume_negation,[status(cth)],[t25_xboole_1])).

cnf(c_0_12,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_15,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k3_xboole_0(X16,X17)) = X16 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_16,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_17,negated_conjecture,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(esk3_0,esk1_0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk2_0,esk3_0)),k2_xboole_0(esk3_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_18,plain,(
    ! [X18,X19,X20] : k2_xboole_0(X18,k3_xboole_0(X19,X20)) = k3_xboole_0(k2_xboole_0(X18,X19),k2_xboole_0(X18,X20)) ),
    inference(variable_rename,[status(thm)],[t24_xboole_1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(esk3_0,esk1_0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk2_0,esk3_0)),k2_xboole_0(esk3_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X13,X14,X15] : k3_xboole_0(k3_xboole_0(X13,X14),X15) = k3_xboole_0(X13,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(esk3_0,esk1_0),k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk2_0,esk3_0))) != k2_xboole_0(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_22]),c_0_22])).

cnf(c_0_29,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_13]),c_0_27]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(esk1_0,esk3_0),k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk2_0,esk3_0))) != k2_xboole_0(k3_xboole_0(esk1_0,esk3_0),k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_20]),c_0_20])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_22]),c_0_29])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_27])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_26]),c_0_12]),c_0_12])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_30])).

cnf(c_0_37,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(k2_xboole_0(esk1_0,esk3_0),k2_xboole_0(esk2_0,esk3_0))) != k2_xboole_0(k3_xboole_0(esk1_0,esk3_0),k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_12]),c_0_12]),c_0_35])).

cnf(c_0_41,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_37])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3)) = k3_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(k2_xboole_0(esk1_0,esk3_0),k2_xboole_0(esk2_0,esk3_0))) != k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k2_xboole_0(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k2_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_42])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_25])).

fof(c_0_47,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0))) != k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k2_xboole_0(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_21]),c_0_46])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_33]),c_0_22]),c_0_49]),c_0_50]),c_0_22]),c_0_27]),c_0_22]),c_0_49]),c_0_22]),c_0_22]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
