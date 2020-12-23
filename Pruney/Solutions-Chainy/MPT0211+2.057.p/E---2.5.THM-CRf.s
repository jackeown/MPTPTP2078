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
% DateTime   : Thu Dec  3 10:36:49 EST 2020

% Result     : Theorem 22.92s
% Output     : CNFRefutation 22.92s
% Verified   : 
% Statistics : Number of formulae       :   58 (1210 expanded)
%              Number of clauses        :   37 ( 493 expanded)
%              Number of leaves         :   10 ( 358 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 (1210 expanded)
%              Number of equality atoms :   57 (1209 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(l129_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X1,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_11,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_14,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X30,X31,X32,X33] : k3_enumset1(X30,X30,X31,X32,X33) = k2_enumset1(X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X21,X22,X23,X24] : k2_enumset1(X21,X22,X23,X24) = k2_enumset1(X21,X24,X23,X22) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12] : k2_enumset1(X9,X10,X11,X12) = k2_enumset1(X11,X10,X9,X12) ),
    inference(variable_rename,[status(thm)],[l129_enumset1])).

fof(c_0_21,plain,(
    ! [X17,X18,X19,X20] : k2_enumset1(X17,X18,X19,X20) = k2_enumset1(X17,X19,X20,X18) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

cnf(c_0_22,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X13,X14,X15,X16] : k2_enumset1(X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X16)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_31,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26]),c_0_26])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X3,X3,X2,X1,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_26]),c_0_26])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_26]),c_0_26])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk1_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk1_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk1_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk1_0,esk2_0,esk2_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X2,X2,X4,X1,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_23]),c_0_23]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X3,X3,X4,X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X4,X4,X3,X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))) = k3_enumset1(X3,X3,X2,X1,X4) ),
    inference(spm,[status(thm)],[c_0_33,c_0_38])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X2,X2,X1,X1,X1),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X2,X2,X1,X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40])).

cnf(c_0_45,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))) != k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_32]),c_0_37]),c_0_32]),c_0_37])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X2,X2,X2)))) = k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_enumset1(X3,X3,X3,X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X4,X4,X3,X3,X3),k3_xboole_0(k3_enumset1(X4,X4,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X3),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X3),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_45])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_enumset1(X3,X3,X3,X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X4,X4,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))) != k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_32]),c_0_37]),c_0_32]),c_0_37])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X4,X4,X3,X3,X3),k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_enumset1(X4,X4,X3,X3,X3)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))) != k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X4,X4,X3,X3,X3),k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k3_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k3_enumset1(X4,X4,X3,X3,X3)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_32]),c_0_42]),c_0_32]),c_0_37]),c_0_32]),c_0_37]),c_0_47]),c_0_32]),c_0_37]),c_0_32]),c_0_37]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:26:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 22.92/23.10  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 22.92/23.10  # and selection function SelectNewComplexAHP.
% 22.92/23.10  #
% 22.92/23.10  # Preprocessing time       : 0.026 s
% 22.92/23.10  # Presaturation interreduction done
% 22.92/23.10  
% 22.92/23.10  # Proof found!
% 22.92/23.10  # SZS status Theorem
% 22.92/23.10  # SZS output start CNFRefutation
% 22.92/23.10  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 22.92/23.10  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 22.92/23.10  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 22.92/23.10  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 22.92/23.10  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 22.92/23.10  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 22.92/23.10  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 22.92/23.10  fof(l129_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X2,X1,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l129_enumset1)).
% 22.92/23.10  fof(t105_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 22.92/23.10  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 22.92/23.10  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 22.92/23.10  fof(c_0_11, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k5_xboole_0(X7,k4_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 22.92/23.10  fof(c_0_12, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 22.92/23.10  fof(c_0_13, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 22.92/23.10  fof(c_0_14, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 22.92/23.10  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 22.92/23.10  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 22.92/23.10  fof(c_0_17, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 22.92/23.10  fof(c_0_18, plain, ![X30, X31, X32, X33]:k3_enumset1(X30,X30,X31,X32,X33)=k2_enumset1(X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 22.92/23.10  fof(c_0_19, plain, ![X21, X22, X23, X24]:k2_enumset1(X21,X22,X23,X24)=k2_enumset1(X21,X24,X23,X22), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 22.92/23.10  fof(c_0_20, plain, ![X9, X10, X11, X12]:k2_enumset1(X9,X10,X11,X12)=k2_enumset1(X11,X10,X9,X12), inference(variable_rename,[status(thm)],[l129_enumset1])).
% 22.92/23.10  fof(c_0_21, plain, ![X17, X18, X19, X20]:k2_enumset1(X17,X18,X19,X20)=k2_enumset1(X17,X19,X20,X18), inference(variable_rename,[status(thm)],[t105_enumset1])).
% 22.92/23.10  cnf(c_0_22, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 22.92/23.10  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 22.92/23.10  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 22.92/23.10  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 22.92/23.10  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 22.92/23.10  cnf(c_0_27, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 22.92/23.10  cnf(c_0_28, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X2,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 22.92/23.10  cnf(c_0_29, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 22.92/23.10  fof(c_0_30, plain, ![X13, X14, X15, X16]:k2_enumset1(X13,X14,X15,X16)=k2_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X16)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 22.92/23.10  cnf(c_0_31, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 22.92/23.10  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_26]), c_0_26])).
% 22.92/23.10  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X3,X3,X2,X1,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_26]), c_0_26])).
% 22.92/23.10  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_26]), c_0_26])).
% 22.92/23.10  cnf(c_0_35, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 22.92/23.10  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk1_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk1_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk1_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk1_0,esk2_0,esk2_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 22.92/23.10  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X2,X2,X4,X1,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 22.92/23.10  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_23]), c_0_23]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 22.92/23.10  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X3,X3,X4,X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_32])).
% 22.92/23.10  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X4,X4,X3,X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 22.92/23.10  cnf(c_0_41, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 22.92/23.10  cnf(c_0_42, plain, (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))))=k3_enumset1(X3,X3,X2,X1,X4)), inference(spm,[status(thm)],[c_0_33, c_0_38])).
% 22.92/23.10  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 22.92/23.10  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X2,X2,X1,X1,X1),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X2,X2,X1,X1,X1))))), inference(spm,[status(thm)],[c_0_38, c_0_40])).
% 22.92/23.10  cnf(c_0_45, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X2,X4,X3)), inference(spm,[status(thm)],[c_0_32, c_0_34])).
% 22.92/23.10  cnf(c_0_46, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))))!=k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_32]), c_0_37]), c_0_32]), c_0_37])).
% 22.92/23.10  cnf(c_0_47, plain, (k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X2,X2,X2))))=k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_enumset1(X3,X3,X3,X3,X4))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 22.92/23.10  cnf(c_0_48, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X4,X4,X3,X3,X3),k3_xboole_0(k3_enumset1(X4,X4,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X2))))), inference(spm,[status(thm)],[c_0_38, c_0_40])).
% 22.92/23.10  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X3),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X3),k3_enumset1(X1,X1,X1,X1,X2))))), inference(spm,[status(thm)],[c_0_38, c_0_45])).
% 22.92/23.10  cnf(c_0_50, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_enumset1(X3,X3,X3,X3,X4))))), inference(spm,[status(thm)],[c_0_38, c_0_40])).
% 22.92/23.10  cnf(c_0_51, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X4,X4,X1,X2,X3)), inference(spm,[status(thm)],[c_0_34, c_0_40])).
% 22.92/23.10  cnf(c_0_52, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))))!=k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_32]), c_0_37]), c_0_32]), c_0_37])).
% 22.92/23.10  cnf(c_0_53, plain, (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))))=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_enumset1(X1,X1,X1,X1,X2))))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 22.92/23.10  cnf(c_0_54, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X4,X4,X3,X3,X3),k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k3_enumset1(X4,X4,X3,X3,X3))))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 22.92/23.10  cnf(c_0_55, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))))!=k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))))), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 22.92/23.10  cnf(c_0_56, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X4,X4,X3,X3,X3),k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k3_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k3_enumset1(X4,X4,X3,X3,X3))))), inference(spm,[status(thm)],[c_0_54, c_0_51])).
% 22.92/23.10  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_32]), c_0_42]), c_0_32]), c_0_37]), c_0_32]), c_0_37]), c_0_47]), c_0_32]), c_0_37]), c_0_32]), c_0_37]), c_0_53])]), ['proof']).
% 22.92/23.10  # SZS output end CNFRefutation
% 22.92/23.10  # Proof object total steps             : 58
% 22.92/23.10  # Proof object clause steps            : 37
% 22.92/23.10  # Proof object formula steps           : 21
% 22.92/23.10  # Proof object conjectures             : 11
% 22.92/23.10  # Proof object clause conjectures      : 8
% 22.92/23.10  # Proof object formula conjectures     : 3
% 22.92/23.10  # Proof object initial clauses used    : 10
% 22.92/23.10  # Proof object initial formulas used   : 10
% 22.92/23.10  # Proof object generating inferences   : 15
% 22.92/23.10  # Proof object simplifying inferences  : 65
% 22.92/23.10  # Training examples: 0 positive, 0 negative
% 22.92/23.10  # Parsed axioms                        : 10
% 22.92/23.10  # Removed by relevancy pruning/SinE    : 0
% 22.92/23.10  # Initial clauses                      : 10
% 22.92/23.10  # Removed in clause preprocessing      : 5
% 22.92/23.10  # Initial clauses in saturation        : 5
% 22.92/23.10  # Processed clauses                    : 103510
% 22.92/23.10  # ...of these trivial                  : 0
% 22.92/23.10  # ...subsumed                          : 102333
% 22.92/23.10  # ...remaining for further processing  : 1177
% 22.92/23.10  # Other redundant clauses eliminated   : 0
% 22.92/23.10  # Clauses deleted for lack of memory   : 0
% 22.92/23.10  # Backward-subsumed                    : 0
% 22.92/23.10  # Backward-rewritten                   : 6
% 22.92/23.10  # Generated clauses                    : 4612949
% 22.92/23.10  # ...of the previous two non-trivial   : 4605264
% 22.92/23.10  # Contextual simplify-reflections      : 0
% 22.92/23.10  # Paramodulations                      : 4612949
% 22.92/23.10  # Factorizations                       : 0
% 22.92/23.10  # Equation resolutions                 : 0
% 22.92/23.10  # Propositional unsat checks           : 0
% 22.92/23.10  #    Propositional check models        : 0
% 22.92/23.10  #    Propositional check unsatisfiable : 0
% 22.92/23.10  #    Propositional clauses             : 0
% 22.92/23.10  #    Propositional clauses after purity: 0
% 22.92/23.10  #    Propositional unsat core size     : 0
% 22.92/23.10  #    Propositional preprocessing time  : 0.000
% 22.92/23.10  #    Propositional encoding time       : 0.000
% 22.92/23.10  #    Propositional solver time         : 0.000
% 22.92/23.10  #    Success case prop preproc time    : 0.000
% 22.92/23.10  #    Success case prop encoding time   : 0.000
% 22.92/23.10  #    Success case prop solver time     : 0.000
% 22.92/23.10  # Current number of processed clauses  : 1166
% 22.92/23.10  #    Positive orientable unit clauses  : 0
% 22.92/23.10  #    Positive unorientable unit clauses: 1166
% 22.92/23.10  #    Negative unit clauses             : 0
% 22.92/23.10  #    Non-unit-clauses                  : 0
% 22.92/23.10  # Current number of unprocessed clauses: 2840623
% 22.92/23.10  # ...number of literals in the above   : 2840623
% 22.92/23.10  # Current number of archived formulas  : 0
% 22.92/23.10  # Current number of archived clauses   : 16
% 22.92/23.10  # Clause-clause subsumption calls (NU) : 0
% 22.92/23.10  # Rec. Clause-clause subsumption calls : 0
% 22.92/23.10  # Non-unit clause-clause subsumptions  : 0
% 22.92/23.10  # Unit Clause-clause subsumption calls : 370372
% 22.92/23.10  # Rewrite failures with RHS unbound    : 0
% 22.92/23.10  # BW rewrite match attempts            : 371535
% 22.92/23.10  # BW rewrite match successes           : 65184
% 22.92/23.10  # Condensation attempts                : 0
% 22.92/23.10  # Condensation successes               : 0
% 22.92/23.10  # Termbank termtop insertions          : 76164197
% 22.95/23.17  
% 22.95/23.17  # -------------------------------------------------
% 22.95/23.17  # User time                : 22.068 s
% 22.95/23.17  # System time              : 0.737 s
% 22.95/23.17  # Total time               : 22.805 s
% 22.95/23.17  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
