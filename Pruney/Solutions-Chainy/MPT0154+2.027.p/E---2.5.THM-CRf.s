%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 (10677 expanded)
%              Number of clauses        :   32 (4710 expanded)
%              Number of leaves         :   11 (2983 expanded)
%              Depth                    :   14
%              Number of atoms          :   55 (10677 expanded)
%              Number of equality atoms :   54 (10676 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t70_enumset1,conjecture,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_11,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k5_xboole_0(X13,k4_xboole_0(X14,X13)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X26,X27,X28] : k1_enumset1(X26,X27,X28) = k2_xboole_0(k1_tarski(X26),k2_tarski(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_14,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X15,X16,X17,X18] : k2_enumset1(X15,X16,X17,X18) = k2_xboole_0(k2_tarski(X15,X16),k2_tarski(X17,X18)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_18,plain,(
    ! [X19,X20,X21,X22,X23] : k3_enumset1(X19,X20,X21,X22,X23) = k2_xboole_0(k1_enumset1(X19,X20,X21),k2_tarski(X22,X23)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,plain,(
    ! [X33,X34,X35,X36] : k2_enumset1(X33,X34,X35,X36) = k2_xboole_0(k1_enumset1(X33,X34,X35),k1_tarski(X36)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_26,plain,(
    ! [X10,X11,X12] : k5_xboole_0(k5_xboole_0(X10,X11),X12) = k5_xboole_0(X10,k5_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_21])).

fof(c_0_29,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_xboole_0(k1_tarski(X24),k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_21]),c_0_25]),c_0_25])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_20]),c_0_21]),c_0_25]),c_0_25]),c_0_28])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_31])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_31]),c_0_31])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t70_enumset1])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_20]),c_0_20]),c_0_21])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X2,X3,X4,X4) = k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_39,negated_conjecture,(
    k1_enumset1(esk1_0,esk1_0,esk2_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X2) = k3_enumset1(X1,X1,X2,X2,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_41,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_42,negated_conjecture,
    ( k1_enumset1(esk1_0,esk1_0,esk2_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X2,X3,X4,X4) = k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_enumset1(X1,X1,X2,X2,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk2_0),k2_tarski(esk1_0,esk1_0)))) != k2_tarski(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X2,X3,X4,X4) = k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k3_enumset1(X3,X3,X4,X4,X4)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk2_0)))) != k2_tarski(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X4),X5) = k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k5_xboole_0(k3_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k3_enumset1(X3,X3,X4,X4,X4)),X5))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_46]),c_0_31])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k5_xboole_0(k3_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X1)),k5_xboole_0(k3_enumset1(X4,X4,X5,X5,X5),k3_xboole_0(k3_enumset1(X4,X4,X5,X5,X5),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k3_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X1))))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))) != k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k3_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X1)))) = k3_enumset1(X1,X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_46])).

cnf(c_0_53,plain,
    ( k3_enumset1(X1,X1,X2,X3,X3) = k3_enumset1(X1,X1,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.19/0.47  # and selection function SelectNewComplexAHP.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.043 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.47  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.47  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.19/0.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.47  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.19/0.47  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 0.19/0.47  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.19/0.47  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.47  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.19/0.47  fof(t70_enumset1, conjecture, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.47  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.47  fof(c_0_11, plain, ![X13, X14]:k2_xboole_0(X13,X14)=k5_xboole_0(X13,k4_xboole_0(X14,X13)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.47  fof(c_0_12, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.47  fof(c_0_13, plain, ![X26, X27, X28]:k1_enumset1(X26,X27,X28)=k2_xboole_0(k1_tarski(X26),k2_tarski(X27,X28)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.19/0.47  fof(c_0_14, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.47  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.47  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.47  fof(c_0_17, plain, ![X15, X16, X17, X18]:k2_enumset1(X15,X16,X17,X18)=k2_xboole_0(k2_tarski(X15,X16),k2_tarski(X17,X18)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.19/0.47  fof(c_0_18, plain, ![X19, X20, X21, X22, X23]:k3_enumset1(X19,X20,X21,X22,X23)=k2_xboole_0(k1_enumset1(X19,X20,X21),k2_tarski(X22,X23)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.19/0.47  cnf(c_0_19, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.47  fof(c_0_22, plain, ![X33, X34, X35, X36]:k2_enumset1(X33,X34,X35,X36)=k2_xboole_0(k1_enumset1(X33,X34,X35),k1_tarski(X36)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.19/0.47  cnf(c_0_23, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_24, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.47  cnf(c_0_25, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.47  fof(c_0_26, plain, ![X10, X11, X12]:k5_xboole_0(k5_xboole_0(X10,X11),X12)=k5_xboole_0(X10,k5_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.47  cnf(c_0_27, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_28, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))), inference(rw,[status(thm)],[c_0_23, c_0_21])).
% 0.19/0.47  fof(c_0_29, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_xboole_0(k1_tarski(X24),k1_tarski(X25)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.19/0.47  cnf(c_0_30, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_21]), c_0_25]), c_0_25])).
% 0.19/0.47  cnf(c_0_31, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  cnf(c_0_32, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))=k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_20]), c_0_21]), c_0_25]), c_0_25]), c_0_28])).
% 0.19/0.47  cnf(c_0_33, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.47  cnf(c_0_34, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)),k5_xboole_0(k2_tarski(X4,X5),k3_xboole_0(k2_tarski(X4,X5),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_31])).
% 0.19/0.47  cnf(c_0_35, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_31]), c_0_31])).
% 0.19/0.47  fof(c_0_36, negated_conjecture, ~(![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t70_enumset1])).
% 0.19/0.47  cnf(c_0_37, plain, (k2_tarski(X1,X2)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_20]), c_0_20]), c_0_21])).
% 0.19/0.47  cnf(c_0_38, plain, (k3_enumset1(X1,X2,X3,X4,X4)=k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.47  fof(c_0_39, negated_conjecture, k1_enumset1(esk1_0,esk1_0,esk2_0)!=k2_tarski(esk1_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.19/0.47  cnf(c_0_40, plain, (k2_tarski(X1,X2)=k3_enumset1(X1,X1,X2,X2,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.47  fof(c_0_41, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.47  cnf(c_0_42, negated_conjecture, (k1_enumset1(esk1_0,esk1_0,esk2_0)!=k2_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.47  cnf(c_0_43, plain, (k3_enumset1(X1,X2,X3,X4,X4)=k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_enumset1(X1,X1,X2,X2,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.19/0.47  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.47  cnf(c_0_45, negated_conjecture, (k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk2_0),k2_tarski(esk1_0,esk1_0))))!=k2_tarski(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_42, c_0_25])).
% 0.19/0.47  cnf(c_0_46, plain, (k3_enumset1(X1,X2,X3,X4,X4)=k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k3_enumset1(X3,X3,X4,X4,X4))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.47  cnf(c_0_47, negated_conjecture, (k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk2_0))))!=k2_tarski(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_45, c_0_44])).
% 0.19/0.47  cnf(c_0_48, plain, (k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X4),X5)=k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k5_xboole_0(k3_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k3_enumset1(X3,X3,X4,X4,X4)),X5)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_46]), c_0_31])).
% 0.19/0.47  cnf(c_0_49, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k5_xboole_0(k3_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X1)),k5_xboole_0(k3_enumset1(X4,X4,X5,X5,X5),k3_xboole_0(k3_enumset1(X4,X4,X5,X5,X5),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k3_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X1)))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.19/0.47  cnf(c_0_50, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))))!=k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.19/0.47  cnf(c_0_51, plain, (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k3_xboole_0(k3_enumset1(X2,X2,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X1))))=k3_enumset1(X1,X1,X1,X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_46])).
% 0.19/0.47  cnf(c_0_52, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_50, c_0_46])).
% 0.19/0.47  cnf(c_0_53, plain, (k3_enumset1(X1,X1,X2,X3,X3)=k3_enumset1(X1,X1,X1,X2,X3)), inference(spm,[status(thm)],[c_0_43, c_0_51])).
% 0.19/0.47  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53]), c_0_53])]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 55
% 0.19/0.47  # Proof object clause steps            : 32
% 0.19/0.47  # Proof object formula steps           : 23
% 0.19/0.47  # Proof object conjectures             : 9
% 0.19/0.47  # Proof object clause conjectures      : 6
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 11
% 0.19/0.47  # Proof object initial formulas used   : 11
% 0.19/0.47  # Proof object generating inferences   : 6
% 0.19/0.47  # Proof object simplifying inferences  : 47
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 13
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 13
% 0.19/0.47  # Removed in clause preprocessing      : 5
% 0.19/0.47  # Initial clauses in saturation        : 8
% 0.19/0.47  # Processed clauses                    : 238
% 0.19/0.47  # ...of these trivial                  : 13
% 0.19/0.47  # ...subsumed                          : 173
% 0.19/0.47  # ...remaining for further processing  : 52
% 0.19/0.47  # Other redundant clauses eliminated   : 0
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 1
% 0.19/0.47  # Backward-rewritten                   : 11
% 0.19/0.47  # Generated clauses                    : 2329
% 0.19/0.47  # ...of the previous two non-trivial   : 2064
% 0.19/0.47  # Contextual simplify-reflections      : 0
% 0.19/0.47  # Paramodulations                      : 2329
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 0
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 32
% 0.19/0.47  #    Positive orientable unit clauses  : 2
% 0.19/0.47  #    Positive unorientable unit clauses: 30
% 0.19/0.47  #    Negative unit clauses             : 0
% 0.19/0.47  #    Non-unit-clauses                  : 0
% 0.19/0.47  # Current number of unprocessed clauses: 1752
% 0.19/0.47  # ...number of literals in the above   : 1752
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 25
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.47  # Unit Clause-clause subsumption calls : 146
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 976
% 0.19/0.47  # BW rewrite match successes           : 478
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 65224
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.121 s
% 0.19/0.47  # System time              : 0.006 s
% 0.19/0.47  # Total time               : 0.127 s
% 0.19/0.47  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
