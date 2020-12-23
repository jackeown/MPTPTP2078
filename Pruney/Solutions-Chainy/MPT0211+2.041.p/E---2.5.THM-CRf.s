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
% DateTime   : Thu Dec  3 10:36:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 (1246 expanded)
%              Number of clauses        :   40 ( 461 expanded)
%              Number of leaves         :   19 ( 392 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 (1246 expanded)
%              Number of equality atoms :   78 (1245 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

fof(t54_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t132_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(t104_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

fof(c_0_19,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X20) = k5_xboole_0(X19,k4_xboole_0(X20,X19)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_20,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_22,plain,(
    ! [X17,X18] : k2_xboole_0(X17,X18) = k5_xboole_0(k5_xboole_0(X17,X18),k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_26,plain,(
    ! [X66,X67] : k1_enumset1(X66,X66,X67) = k2_tarski(X66,X67) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X68,X69,X70] : k2_enumset1(X68,X68,X69,X70) = k1_enumset1(X68,X69,X70) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X71,X72,X73,X74] : k3_enumset1(X71,X71,X72,X73,X74) = k2_enumset1(X71,X72,X73,X74) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X75,X76,X77,X78,X79] : k4_enumset1(X75,X75,X76,X77,X78,X79) = k3_enumset1(X75,X76,X77,X78,X79) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_32,plain,(
    ! [X14,X15,X16] : k5_xboole_0(k5_xboole_0(X14,X15),X16) = k5_xboole_0(X14,k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X37,X38,X39,X40] : k2_enumset1(X37,X38,X39,X40) = k2_enumset1(X40,X39,X38,X37) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_41,plain,(
    ! [X50,X51,X52,X53] : k2_enumset1(X50,X51,X52,X53) = k2_xboole_0(k1_enumset1(X50,X51,X52),k1_tarski(X53)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_42,plain,(
    ! [X65] : k2_tarski(X65,X65) = k1_tarski(X65) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_43,plain,(
    ! [X59,X60,X61,X62,X63,X64] : k4_enumset1(X59,X60,X61,X62,X63,X64) = k2_xboole_0(k2_enumset1(X59,X60,X61,X62),k2_tarski(X63,X64)) ),
    inference(variable_rename,[status(thm)],[t54_enumset1])).

cnf(c_0_44,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_31]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_51,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48,X49] : k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) = k2_xboole_0(k4_enumset1(X41,X42,X43,X44,X45,X46),k1_enumset1(X47,X48,X49)) ),
    inference(variable_rename,[status(thm)],[t132_enumset1])).

fof(c_0_52,plain,(
    ! [X54,X55,X56,X57,X58] : k3_enumset1(X54,X55,X56,X57,X58) = k2_xboole_0(k2_tarski(X54,X55),k1_enumset1(X56,X57,X58)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_53,plain,(
    ! [X21,X22,X23,X24] : k2_enumset1(X21,X22,X23,X24) = k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X24)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_56,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_34]),c_0_31]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_57,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X1,X1,X1,X2,X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_34]),c_0_31]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_62,plain,(
    ! [X29,X30,X31,X32] : k2_enumset1(X29,X30,X31,X32) = k2_enumset1(X29,X32,X31,X30) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

fof(c_0_63,plain,(
    ! [X25,X26,X27,X28] : k2_enumset1(X25,X26,X27,X28) = k2_enumset1(X25,X27,X26,X28) ),
    inference(variable_rename,[status(thm)],[t104_enumset1])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_65,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X4) = k4_enumset1(X1,X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_58]),c_0_39])).

cnf(c_0_67,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k5_xboole_0(k4_enumset1(X7,X7,X7,X7,X8,X9),k3_xboole_0(k4_enumset1(X7,X7,X7,X7,X8,X9),k4_enumset1(X1,X2,X3,X4,X5,X6)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_31]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_68,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X4,X5),k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X4,X5),k4_enumset1(X1,X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_34]),c_0_31]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_69,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X4),k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X4),k4_enumset1(X1,X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_34]),c_0_34]),c_0_31]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_70,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65]),c_0_65])).

cnf(c_0_73,plain,
    ( k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X5,X6,X7,X8,X9),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)))) = k7_enumset1(X4,X5,X6,X7,X8,X9,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( k7_enumset1(X1,X1,X1,X1,X1,X2,X3,X4,X5) = k4_enumset1(X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_68,c_0_67])).

cnf(c_0_75,plain,
    ( k4_enumset1(X1,X1,X2,X3,X3,X4) = k4_enumset1(X1,X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_76,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X1,X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_77,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k4_enumset1(X1,X1,X1,X3,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75]),c_0_76]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:43:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.049 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.42  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 0.19/0.42  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.19/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.42  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.42  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.42  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 0.19/0.42  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.19/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.42  fof(t54_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 0.19/0.42  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.42  fof(t132_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_enumset1)).
% 0.19/0.42  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 0.19/0.42  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.19/0.42  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 0.19/0.42  fof(t104_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X2,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 0.19/0.42  fof(c_0_19, plain, ![X19, X20]:k2_xboole_0(X19,X20)=k5_xboole_0(X19,k4_xboole_0(X20,X19)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.42  fof(c_0_20, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.42  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.19/0.42  fof(c_0_22, plain, ![X17, X18]:k2_xboole_0(X17,X18)=k5_xboole_0(k5_xboole_0(X17,X18),k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.19/0.42  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  fof(c_0_25, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.19/0.42  fof(c_0_26, plain, ![X66, X67]:k1_enumset1(X66,X66,X67)=k2_tarski(X66,X67), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.42  fof(c_0_27, plain, ![X68, X69, X70]:k2_enumset1(X68,X68,X69,X70)=k1_enumset1(X68,X69,X70), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.42  fof(c_0_28, plain, ![X71, X72, X73, X74]:k3_enumset1(X71,X71,X72,X73,X74)=k2_enumset1(X71,X72,X73,X74), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.42  fof(c_0_29, plain, ![X75, X76, X77, X78, X79]:k4_enumset1(X75,X75,X76,X77,X78,X79)=k3_enumset1(X75,X76,X77,X78,X79), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.42  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.42  fof(c_0_32, plain, ![X14, X15, X16]:k5_xboole_0(k5_xboole_0(X14,X15),X16)=k5_xboole_0(X14,k5_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.42  cnf(c_0_39, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  fof(c_0_40, plain, ![X37, X38, X39, X40]:k2_enumset1(X37,X38,X39,X40)=k2_enumset1(X40,X39,X38,X37), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.19/0.42  fof(c_0_41, plain, ![X50, X51, X52, X53]:k2_enumset1(X50,X51,X52,X53)=k2_xboole_0(k1_enumset1(X50,X51,X52),k1_tarski(X53)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.19/0.42  fof(c_0_42, plain, ![X65]:k2_tarski(X65,X65)=k1_tarski(X65), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.42  fof(c_0_43, plain, ![X59, X60, X61, X62, X63, X64]:k4_enumset1(X59,X60,X61,X62,X63,X64)=k2_xboole_0(k2_enumset1(X59,X60,X61,X62),k2_tarski(X63,X64)), inference(variable_rename,[status(thm)],[t54_enumset1])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (k5_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_31]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.19/0.42  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.42  cnf(c_0_46, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.42  cnf(c_0_47, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.42  cnf(c_0_48, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_49, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.42  fof(c_0_50, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.42  fof(c_0_51, plain, ![X41, X42, X43, X44, X45, X46, X47, X48, X49]:k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)=k2_xboole_0(k4_enumset1(X41,X42,X43,X44,X45,X46),k1_enumset1(X47,X48,X49)), inference(variable_rename,[status(thm)],[t132_enumset1])).
% 0.19/0.42  fof(c_0_52, plain, ![X54, X55, X56, X57, X58]:k3_enumset1(X54,X55,X56,X57,X58)=k2_xboole_0(k2_tarski(X54,X55),k1_enumset1(X56,X57,X58)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.19/0.42  fof(c_0_53, plain, ![X21, X22, X23, X24]:k2_enumset1(X21,X22,X23,X24)=k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X24)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (k5_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.42  cnf(c_0_55, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.19/0.42  cnf(c_0_56, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_34]), c_0_31]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.19/0.42  cnf(c_0_57, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X1,X1,X1,X2,X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_34]), c_0_31]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.19/0.42  cnf(c_0_58, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.42  cnf(c_0_59, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_60, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.42  cnf(c_0_61, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.42  fof(c_0_62, plain, ![X29, X30, X31, X32]:k2_enumset1(X29,X30,X31,X32)=k2_enumset1(X29,X32,X31,X30), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 0.19/0.42  fof(c_0_63, plain, ![X25, X26, X27, X28]:k2_enumset1(X25,X26,X27,X28)=k2_enumset1(X25,X27,X26,X28), inference(variable_rename,[status(thm)],[t104_enumset1])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_55]), c_0_55]), c_0_55])).
% 0.19/0.42  cnf(c_0_65, plain, (k4_enumset1(X1,X1,X2,X3,X4,X4)=k4_enumset1(X1,X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.42  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_58]), c_0_39])).
% 0.19/0.42  cnf(c_0_67, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k5_xboole_0(k4_enumset1(X7,X7,X7,X7,X8,X9),k3_xboole_0(k4_enumset1(X7,X7,X7,X7,X8,X9),k4_enumset1(X1,X2,X3,X4,X5,X6))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_31]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.19/0.42  cnf(c_0_68, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X4,X5),k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X4,X5),k4_enumset1(X1,X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_34]), c_0_31]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.19/0.42  cnf(c_0_69, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X4),k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X4),k4_enumset1(X1,X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_34]), c_0_34]), c_0_31]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.19/0.42  cnf(c_0_70, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.42  cnf(c_0_71, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X2,X4)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65]), c_0_65])).
% 0.19/0.42  cnf(c_0_73, plain, (k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X5,X6,X7,X8,X9),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9))))=k7_enumset1(X4,X5,X6,X7,X8,X9,X1,X2,X3)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.42  cnf(c_0_74, plain, (k7_enumset1(X1,X1,X1,X1,X1,X2,X3,X4,X5)=k4_enumset1(X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_68, c_0_67])).
% 0.19/0.42  cnf(c_0_75, plain, (k4_enumset1(X1,X1,X2,X3,X3,X4)=k4_enumset1(X1,X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_69, c_0_68])).
% 0.19/0.42  cnf(c_0_76, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X1,X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.19/0.42  cnf(c_0_77, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k4_enumset1(X1,X1,X1,X3,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_75]), c_0_76]), c_0_77])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 79
% 0.19/0.42  # Proof object clause steps            : 40
% 0.19/0.42  # Proof object formula steps           : 39
% 0.19/0.42  # Proof object conjectures             : 9
% 0.19/0.42  # Proof object clause conjectures      : 6
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 19
% 0.19/0.42  # Proof object initial formulas used   : 19
% 0.19/0.42  # Proof object generating inferences   : 2
% 0.19/0.42  # Proof object simplifying inferences  : 124
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 20
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 20
% 0.19/0.42  # Removed in clause preprocessing      : 7
% 0.19/0.42  # Initial clauses in saturation        : 13
% 0.19/0.42  # Processed clauses                    : 193
% 0.19/0.42  # ...of these trivial                  : 56
% 0.19/0.42  # ...subsumed                          : 83
% 0.19/0.42  # ...remaining for further processing  : 54
% 0.19/0.42  # Other redundant clauses eliminated   : 0
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 0
% 0.19/0.42  # Backward-rewritten                   : 6
% 0.19/0.42  # Generated clauses                    : 1736
% 0.19/0.42  # ...of the previous two non-trivial   : 1528
% 0.19/0.42  # Contextual simplify-reflections      : 0
% 0.19/0.42  # Paramodulations                      : 1736
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 0
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 35
% 0.19/0.42  #    Positive orientable unit clauses  : 8
% 0.19/0.42  #    Positive unorientable unit clauses: 27
% 0.19/0.42  #    Negative unit clauses             : 0
% 0.19/0.42  #    Non-unit-clauses                  : 0
% 0.19/0.42  # Current number of unprocessed clauses: 1361
% 0.19/0.42  # ...number of literals in the above   : 1361
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 26
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.42  # Unit Clause-clause subsumption calls : 255
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 760
% 0.19/0.42  # BW rewrite match successes           : 383
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 12180
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.078 s
% 0.19/0.43  # System time              : 0.005 s
% 0.19/0.43  # Total time               : 0.083 s
% 0.19/0.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
