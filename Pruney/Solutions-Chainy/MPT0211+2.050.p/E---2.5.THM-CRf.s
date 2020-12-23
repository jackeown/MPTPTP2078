%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:48 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   73 (1279 expanded)
%              Number of clauses        :   38 ( 474 expanded)
%              Number of leaves         :   17 ( 402 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 (1279 expanded)
%              Number of equality atoms :   72 (1278 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(t113_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(c_0_17,plain,(
    ! [X18,X19] : k2_xboole_0(X18,X19) = k5_xboole_0(X18,k4_xboole_0(X19,X18)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_18,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_20,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(k5_xboole_0(X16,X17),k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_24,plain,(
    ! [X50,X51] : k1_enumset1(X50,X50,X51) = k2_tarski(X50,X51) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X52,X53,X54] : k2_enumset1(X52,X52,X53,X54) = k1_enumset1(X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X55,X56,X57,X58] : k3_enumset1(X55,X55,X56,X57,X58) = k2_enumset1(X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X59,X60,X61,X62,X63] : k4_enumset1(X59,X59,X60,X61,X62,X63) = k3_enumset1(X59,X60,X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_30,plain,(
    ! [X13,X14,X15] : k5_xboole_0(k5_xboole_0(X13,X14),X15) = k5_xboole_0(X13,k5_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X33,X34,X35,X36] : k2_enumset1(X33,X34,X35,X36) = k2_enumset1(X36,X35,X34,X33) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_39,plain,(
    ! [X37,X38,X39,X40] : k2_enumset1(X37,X38,X39,X40) = k2_xboole_0(k1_enumset1(X37,X38,X39),k1_tarski(X40)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_40,plain,(
    ! [X49] : k2_tarski(X49,X49) = k1_tarski(X49) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_41,plain,(
    ! [X20,X21,X22,X23,X24] : k3_enumset1(X20,X21,X22,X23,X24) = k2_xboole_0(k1_enumset1(X20,X21,X22),k2_tarski(X23,X24)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

cnf(c_0_42,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32]),c_0_29]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_49,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48] : k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) = k2_xboole_0(k4_enumset1(X41,X42,X43,X44,X45,X46),k2_tarski(X47,X48)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

fof(c_0_50,plain,(
    ! [X29,X30,X31,X32] : k2_enumset1(X29,X30,X31,X32) = k2_enumset1(X30,X32,X31,X29) ),
    inference(variable_rename,[status(thm)],[t113_enumset1])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_53,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_32]),c_0_29]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_54,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_32]),c_0_29]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_57,plain,(
    ! [X25,X26,X27,X28] : k2_enumset1(X25,X26,X27,X28) = k2_enumset1(X25,X28,X27,X26) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

cnf(c_0_58,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_60,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X4) = k4_enumset1(X1,X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_37])).

cnf(c_0_62,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k5_xboole_0(k4_enumset1(X7,X7,X7,X7,X7,X8),k3_xboole_0(k4_enumset1(X7,X7,X7,X7,X7,X8),k4_enumset1(X1,X2,X3,X4,X5,X6)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_32]),c_0_29]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_63,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X2,X2,X2,X4,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)))) = k6_enumset1(X3,X4,X5,X6,X7,X8,X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_55])).

cnf(c_0_67,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k4_enumset1(X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_54,c_0_62])).

cnf(c_0_68,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X1,X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_69,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X1,X1,X1,X3,X4,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_71,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X1,X1,X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:51:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.026 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.18/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.38  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 0.18/0.38  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.18/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.38  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.18/0.38  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 0.18/0.38  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.18/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.38  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 0.18/0.38  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.18/0.38  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 0.18/0.38  fof(t113_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 0.18/0.38  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 0.18/0.38  fof(c_0_17, plain, ![X18, X19]:k2_xboole_0(X18,X19)=k5_xboole_0(X18,k4_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.18/0.38  fof(c_0_18, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.38  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.18/0.38  fof(c_0_20, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(k5_xboole_0(X16,X17),k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.18/0.38  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.38  fof(c_0_23, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.18/0.38  fof(c_0_24, plain, ![X50, X51]:k1_enumset1(X50,X50,X51)=k2_tarski(X50,X51), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.38  fof(c_0_25, plain, ![X52, X53, X54]:k2_enumset1(X52,X52,X53,X54)=k1_enumset1(X52,X53,X54), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.38  fof(c_0_26, plain, ![X55, X56, X57, X58]:k3_enumset1(X55,X55,X56,X57,X58)=k2_enumset1(X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.38  fof(c_0_27, plain, ![X59, X60, X61, X62, X63]:k4_enumset1(X59,X59,X60,X61,X62,X63)=k3_enumset1(X59,X60,X61,X62,X63), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.38  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.38  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.38  fof(c_0_30, plain, ![X13, X14, X15]:k5_xboole_0(k5_xboole_0(X13,X14),X15)=k5_xboole_0(X13,k5_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.18/0.38  cnf(c_0_31, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.38  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.38  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.38  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.38  cnf(c_0_36, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.38  cnf(c_0_37, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.38  fof(c_0_38, plain, ![X33, X34, X35, X36]:k2_enumset1(X33,X34,X35,X36)=k2_enumset1(X36,X35,X34,X33), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.18/0.38  fof(c_0_39, plain, ![X37, X38, X39, X40]:k2_enumset1(X37,X38,X39,X40)=k2_xboole_0(k1_enumset1(X37,X38,X39),k1_tarski(X40)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.18/0.38  fof(c_0_40, plain, ![X49]:k2_tarski(X49,X49)=k1_tarski(X49), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.38  fof(c_0_41, plain, ![X20, X21, X22, X23, X24]:k3_enumset1(X20,X21,X22,X23,X24)=k2_xboole_0(k1_enumset1(X20,X21,X22),k2_tarski(X23,X24)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.18/0.38  cnf(c_0_42, negated_conjecture, (k5_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_32]), c_0_29]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.18/0.38  cnf(c_0_43, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.38  cnf(c_0_44, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.38  cnf(c_0_45, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.38  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.38  cnf(c_0_47, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.38  fof(c_0_48, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.18/0.38  fof(c_0_49, plain, ![X41, X42, X43, X44, X45, X46, X47, X48]:k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48)=k2_xboole_0(k4_enumset1(X41,X42,X43,X44,X45,X46),k2_tarski(X47,X48)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 0.18/0.38  fof(c_0_50, plain, ![X29, X30, X31, X32]:k2_enumset1(X29,X30,X31,X32)=k2_enumset1(X30,X32,X31,X29), inference(variable_rename,[status(thm)],[t113_enumset1])).
% 0.18/0.38  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.38  cnf(c_0_52, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.18/0.38  cnf(c_0_53, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_32]), c_0_29]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.18/0.38  cnf(c_0_54, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_32]), c_0_29]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.18/0.38  cnf(c_0_55, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.38  cnf(c_0_56, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.38  fof(c_0_57, plain, ![X25, X26, X27, X28]:k2_enumset1(X25,X26,X27,X28)=k2_enumset1(X25,X28,X27,X26), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 0.18/0.38  cnf(c_0_58, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.18/0.38  cnf(c_0_59, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_52]), c_0_52]), c_0_52])).
% 0.18/0.38  cnf(c_0_60, plain, (k4_enumset1(X1,X1,X2,X3,X4,X4)=k4_enumset1(X1,X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.18/0.38  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_55, c_0_37])).
% 0.18/0.38  cnf(c_0_62, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k5_xboole_0(k4_enumset1(X7,X7,X7,X7,X7,X8),k3_xboole_0(k4_enumset1(X7,X7,X7,X7,X7,X8),k4_enumset1(X1,X2,X3,X4,X5,X6))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_32]), c_0_29]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.18/0.38  cnf(c_0_63, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.18/0.38  cnf(c_0_64, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X2,X2,X2,X4,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.18/0.38  cnf(c_0_65, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60])).
% 0.18/0.38  cnf(c_0_66, plain, (k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))))=k6_enumset1(X3,X4,X5,X6,X7,X8,X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_55])).
% 0.18/0.38  cnf(c_0_67, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k4_enumset1(X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_54, c_0_62])).
% 0.18/0.38  cnf(c_0_68, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X1,X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.18/0.38  cnf(c_0_69, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X1,X1,X1,X3,X4,X2)), inference(spm,[status(thm)],[c_0_52, c_0_64])).
% 0.18/0.38  cnf(c_0_70, negated_conjecture, (k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68]), c_0_69])).
% 0.18/0.38  cnf(c_0_71, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X1,X1,X1,X2,X4,X3)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.18/0.38  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 73
% 0.18/0.38  # Proof object clause steps            : 38
% 0.18/0.38  # Proof object formula steps           : 35
% 0.18/0.38  # Proof object conjectures             : 10
% 0.18/0.38  # Proof object clause conjectures      : 7
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 17
% 0.18/0.38  # Proof object initial formulas used   : 17
% 0.18/0.38  # Proof object generating inferences   : 4
% 0.18/0.38  # Proof object simplifying inferences  : 95
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 17
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 17
% 0.18/0.38  # Removed in clause preprocessing      : 7
% 0.18/0.38  # Initial clauses in saturation        : 10
% 0.18/0.38  # Processed clauses                    : 205
% 0.18/0.38  # ...of these trivial                  : 63
% 0.18/0.38  # ...subsumed                          : 83
% 0.18/0.38  # ...remaining for further processing  : 59
% 0.18/0.38  # Other redundant clauses eliminated   : 0
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 0
% 0.18/0.38  # Backward-rewritten                   : 6
% 0.18/0.38  # Generated clauses                    : 1707
% 0.18/0.38  # ...of the previous two non-trivial   : 1504
% 0.18/0.38  # Contextual simplify-reflections      : 0
% 0.18/0.38  # Paramodulations                      : 1707
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 0
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 43
% 0.18/0.38  #    Positive orientable unit clauses  : 12
% 0.18/0.38  #    Positive unorientable unit clauses: 31
% 0.18/0.38  #    Negative unit clauses             : 0
% 0.18/0.38  #    Non-unit-clauses                  : 0
% 0.18/0.38  # Current number of unprocessed clauses: 1319
% 0.18/0.38  # ...number of literals in the above   : 1319
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 23
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.38  # Unit Clause-clause subsumption calls : 269
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 878
% 0.18/0.38  # BW rewrite match successes           : 463
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 10532
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.042 s
% 0.18/0.38  # System time              : 0.006 s
% 0.18/0.38  # Total time               : 0.048 s
% 0.18/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
