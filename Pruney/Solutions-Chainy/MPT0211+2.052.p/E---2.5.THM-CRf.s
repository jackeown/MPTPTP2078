%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:49 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   60 (1496 expanded)
%              Number of clauses        :   29 ( 551 expanded)
%              Number of leaves         :   15 ( 472 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 (1496 expanded)
%              Number of equality atoms :   59 (1495 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(t54_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(c_0_15,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_18,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(k5_xboole_0(X14,X15),k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_22,plain,(
    ! [X45,X46] : k1_enumset1(X45,X45,X46) = k2_tarski(X45,X46) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X47,X48,X49] : k2_enumset1(X47,X47,X48,X49) = k1_enumset1(X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X50,X51,X52,X53] : k3_enumset1(X50,X50,X51,X52,X53) = k2_enumset1(X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X54,X55,X56,X57,X58] : k4_enumset1(X54,X54,X55,X56,X57,X58) = k3_enumset1(X54,X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_28,plain,(
    ! [X11,X12,X13] : k5_xboole_0(k5_xboole_0(X11,X12),X13) = k5_xboole_0(X11,k5_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_29,plain,(
    ! [X30,X31,X32,X33] : k2_enumset1(X30,X31,X32,X33) = k2_enumset1(X33,X32,X31,X30) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_30,plain,(
    ! [X38,X39,X40,X41,X42,X43] : k4_enumset1(X38,X39,X40,X41,X42,X43) = k2_xboole_0(k2_enumset1(X38,X39,X40,X41),k2_tarski(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t54_enumset1])).

fof(c_0_31,plain,(
    ! [X34,X35,X36,X37] : k2_enumset1(X34,X35,X36,X37) = k2_xboole_0(k1_enumset1(X34,X35,X36),k1_tarski(X37)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_32,plain,(
    ! [X44] : k2_tarski(X44,X44) = k1_tarski(X44) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X22,X23,X24,X25] : k2_enumset1(X22,X23,X24,X25) = k2_enumset1(X22,X25,X24,X23) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

cnf(c_0_45,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_27]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_48,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X1,X1,X1,X2,X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_34]),c_0_27]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_49,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_34]),c_0_27]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_51,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k5_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47])).

cnf(c_0_53,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X4) = k4_enumset1(X1,X1,X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X1,X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) != k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X4),k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X4),k4_enumset1(X1,X1,X1,X1,X1,X2)))) = k4_enumset1(X1,X1,X1,X4,X3,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_48])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_55]),c_0_39])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_47]),c_0_53]),c_0_53]),c_0_47]),c_0_53]),c_0_53]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.39/1.57  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 1.39/1.57  # and selection function SelectNewComplexAHP.
% 1.39/1.57  #
% 1.39/1.57  # Preprocessing time       : 0.022 s
% 1.39/1.57  # Presaturation interreduction done
% 1.39/1.57  
% 1.39/1.57  # Proof found!
% 1.39/1.57  # SZS status Theorem
% 1.39/1.57  # SZS output start CNFRefutation
% 1.39/1.57  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.39/1.57  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.39/1.57  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 1.39/1.57  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 1.39/1.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.39/1.57  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.39/1.57  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.39/1.57  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.39/1.57  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 1.39/1.57  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 1.39/1.57  fof(t54_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 1.39/1.57  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 1.39/1.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.39/1.57  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 1.39/1.57  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.39/1.57  fof(c_0_15, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 1.39/1.57  fof(c_0_16, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.39/1.57  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 1.39/1.57  fof(c_0_18, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(k5_xboole_0(X14,X15),k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 1.39/1.57  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.39/1.57  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.39/1.57  fof(c_0_21, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 1.39/1.57  fof(c_0_22, plain, ![X45, X46]:k1_enumset1(X45,X45,X46)=k2_tarski(X45,X46), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.39/1.57  fof(c_0_23, plain, ![X47, X48, X49]:k2_enumset1(X47,X47,X48,X49)=k1_enumset1(X47,X48,X49), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.39/1.57  fof(c_0_24, plain, ![X50, X51, X52, X53]:k3_enumset1(X50,X50,X51,X52,X53)=k2_enumset1(X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.39/1.57  fof(c_0_25, plain, ![X54, X55, X56, X57, X58]:k4_enumset1(X54,X54,X55,X56,X57,X58)=k3_enumset1(X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.39/1.57  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.39/1.57  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 1.39/1.57  fof(c_0_28, plain, ![X11, X12, X13]:k5_xboole_0(k5_xboole_0(X11,X12),X13)=k5_xboole_0(X11,k5_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 1.39/1.57  fof(c_0_29, plain, ![X30, X31, X32, X33]:k2_enumset1(X30,X31,X32,X33)=k2_enumset1(X33,X32,X31,X30), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 1.39/1.57  fof(c_0_30, plain, ![X38, X39, X40, X41, X42, X43]:k4_enumset1(X38,X39,X40,X41,X42,X43)=k2_xboole_0(k2_enumset1(X38,X39,X40,X41),k2_tarski(X42,X43)), inference(variable_rename,[status(thm)],[t54_enumset1])).
% 1.39/1.57  fof(c_0_31, plain, ![X34, X35, X36, X37]:k2_enumset1(X34,X35,X36,X37)=k2_xboole_0(k1_enumset1(X34,X35,X36),k1_tarski(X37)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 1.39/1.57  fof(c_0_32, plain, ![X44]:k2_tarski(X44,X44)=k1_tarski(X44), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.39/1.57  cnf(c_0_33, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.39/1.57  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.39/1.57  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.39/1.57  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.39/1.57  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.39/1.57  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 1.39/1.57  cnf(c_0_39, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.39/1.57  cnf(c_0_40, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.39/1.57  cnf(c_0_41, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.39/1.57  cnf(c_0_42, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.39/1.57  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.39/1.57  fof(c_0_44, plain, ![X22, X23, X24, X25]:k2_enumset1(X22,X23,X24,X25)=k2_enumset1(X22,X25,X24,X23), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 1.39/1.57  cnf(c_0_45, negated_conjecture, (k5_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_27]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 1.39/1.57  cnf(c_0_46, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 1.39/1.57  cnf(c_0_47, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 1.39/1.57  cnf(c_0_48, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X1,X1,X1,X2,X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_34]), c_0_27]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 1.39/1.57  cnf(c_0_49, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_34]), c_0_27]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 1.39/1.57  cnf(c_0_50, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.39/1.57  fof(c_0_51, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k5_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 1.39/1.57  cnf(c_0_52, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_47])).
% 1.39/1.57  cnf(c_0_53, plain, (k4_enumset1(X1,X1,X2,X3,X4,X4)=k4_enumset1(X1,X1,X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.39/1.57  cnf(c_0_54, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X1,X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 1.39/1.57  cnf(c_0_55, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.39/1.57  cnf(c_0_56, negated_conjecture, (k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)!=k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53])).
% 1.39/1.57  cnf(c_0_57, plain, (k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X4),k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X4),k4_enumset1(X1,X1,X1,X1,X1,X2))))=k4_enumset1(X1,X1,X1,X4,X3,X2)), inference(spm,[status(thm)],[c_0_54, c_0_48])).
% 1.39/1.57  cnf(c_0_58, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_55]), c_0_39])).
% 1.39/1.57  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_47]), c_0_53]), c_0_53]), c_0_47]), c_0_53]), c_0_53]), c_0_58])]), ['proof']).
% 1.39/1.57  # SZS output end CNFRefutation
% 1.39/1.57  # Proof object total steps             : 60
% 1.39/1.57  # Proof object clause steps            : 29
% 1.39/1.57  # Proof object formula steps           : 31
% 1.39/1.57  # Proof object conjectures             : 8
% 1.39/1.57  # Proof object clause conjectures      : 5
% 1.39/1.57  # Proof object formula conjectures     : 3
% 1.39/1.57  # Proof object initial clauses used    : 15
% 1.39/1.57  # Proof object initial formulas used   : 15
% 1.39/1.57  # Proof object generating inferences   : 3
% 1.39/1.57  # Proof object simplifying inferences  : 81
% 1.39/1.57  # Training examples: 0 positive, 0 negative
% 1.39/1.57  # Parsed axioms                        : 17
% 1.39/1.57  # Removed by relevancy pruning/SinE    : 0
% 1.39/1.57  # Initial clauses                      : 17
% 1.39/1.57  # Removed in clause preprocessing      : 7
% 1.39/1.57  # Initial clauses in saturation        : 10
% 1.39/1.57  # Processed clauses                    : 7474
% 1.39/1.57  # ...of these trivial                  : 355
% 1.39/1.57  # ...subsumed                          : 6676
% 1.39/1.57  # ...remaining for further processing  : 443
% 1.39/1.57  # Other redundant clauses eliminated   : 0
% 1.39/1.57  # Clauses deleted for lack of memory   : 0
% 1.39/1.57  # Backward-subsumed                    : 0
% 1.39/1.57  # Backward-rewritten                   : 3
% 1.39/1.57  # Generated clauses                    : 232768
% 1.39/1.57  # ...of the previous two non-trivial   : 229397
% 1.39/1.57  # Contextual simplify-reflections      : 0
% 1.39/1.57  # Paramodulations                      : 232768
% 1.39/1.57  # Factorizations                       : 0
% 1.39/1.57  # Equation resolutions                 : 0
% 1.39/1.57  # Propositional unsat checks           : 0
% 1.39/1.57  #    Propositional check models        : 0
% 1.39/1.57  #    Propositional check unsatisfiable : 0
% 1.39/1.57  #    Propositional clauses             : 0
% 1.39/1.57  #    Propositional clauses after purity: 0
% 1.39/1.57  #    Propositional unsat core size     : 0
% 1.39/1.57  #    Propositional preprocessing time  : 0.000
% 1.39/1.57  #    Propositional encoding time       : 0.000
% 1.39/1.57  #    Propositional solver time         : 0.000
% 1.39/1.57  #    Success case prop preproc time    : 0.000
% 1.39/1.57  #    Success case prop encoding time   : 0.000
% 1.39/1.57  #    Success case prop solver time     : 0.000
% 1.39/1.57  # Current number of processed clauses  : 430
% 1.39/1.57  #    Positive orientable unit clauses  : 5
% 1.39/1.57  #    Positive unorientable unit clauses: 425
% 1.39/1.57  #    Negative unit clauses             : 0
% 1.39/1.57  #    Non-unit-clauses                  : 0
% 1.39/1.57  # Current number of unprocessed clauses: 221935
% 1.39/1.57  # ...number of literals in the above   : 221935
% 1.39/1.57  # Current number of archived formulas  : 0
% 1.39/1.57  # Current number of archived clauses   : 20
% 1.39/1.57  # Clause-clause subsumption calls (NU) : 0
% 1.39/1.57  # Rec. Clause-clause subsumption calls : 0
% 1.39/1.57  # Non-unit clause-clause subsumptions  : 0
% 1.39/1.57  # Unit Clause-clause subsumption calls : 45166
% 1.39/1.57  # Rewrite failures with RHS unbound    : 0
% 1.39/1.57  # BW rewrite match attempts            : 69384
% 1.39/1.57  # BW rewrite match successes           : 5533
% 1.39/1.57  # Condensation attempts                : 0
% 1.39/1.57  # Condensation successes               : 0
% 1.39/1.57  # Termbank termtop insertions          : 2286307
% 1.39/1.58  
% 1.39/1.58  # -------------------------------------------------
% 1.39/1.58  # User time                : 1.146 s
% 1.39/1.58  # System time              : 0.088 s
% 1.39/1.58  # Total time               : 1.233 s
% 1.39/1.58  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
