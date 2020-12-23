%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:37 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 952 expanded)
%              Number of clauses        :   39 ( 417 expanded)
%              Number of leaves         :   15 ( 267 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 952 expanded)
%              Number of equality atoms :   69 ( 951 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(t71_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_15,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X36,X37,X38,X39,X40] : k3_enumset1(X36,X37,X38,X39,X40) = k2_xboole_0(k2_tarski(X36,X37),k1_enumset1(X38,X39,X40)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_18,plain,(
    ! [X85,X86] : k1_enumset1(X85,X85,X86) = k2_tarski(X85,X86) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X18,X19,X20,X21,X22,X23] : k4_enumset1(X18,X19,X20,X21,X22,X23) = k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

fof(c_0_22,plain,(
    ! [X47,X48,X49,X50,X51,X52] : k4_enumset1(X47,X48,X49,X50,X51,X52) = k2_xboole_0(k3_enumset1(X47,X48,X49,X50,X51),k1_tarski(X52)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_23,plain,(
    ! [X84] : k2_tarski(X84,X84) = k1_tarski(X84) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X53,X54,X55,X56,X57,X58,X59] : k5_enumset1(X53,X54,X55,X56,X57,X58,X59) = k2_xboole_0(k4_enumset1(X53,X54,X55,X56,X57,X58),k1_tarski(X59)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

fof(c_0_29,plain,(
    ! [X41,X42,X43,X44,X45,X46] : k4_enumset1(X41,X42,X43,X44,X45,X46) = k2_xboole_0(k1_tarski(X41),k3_enumset1(X42,X43,X44,X45,X46)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

fof(c_0_34,plain,(
    ! [X13,X14,X15] : k5_xboole_0(k5_xboole_0(X13,X14),X15) = k5_xboole_0(X13,k5_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))),k5_xboole_0(k1_enumset1(X6,X6,X6),k3_xboole_0(k1_enumset1(X6,X6,X6),k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_25]),c_0_26]),c_0_32]),c_0_32]),c_0_33])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_31]),c_0_25]),c_0_26]),c_0_33]),c_0_33])).

fof(c_0_40,plain,(
    ! [X24,X25,X26] : k1_enumset1(X24,X25,X26) = k2_xboole_0(k2_tarski(X24,X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) = k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X2,X2,X3)))),k3_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X2,X2,X3)))),k1_enumset1(X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_31]),c_0_25]),c_0_26]),c_0_32]),c_0_32]),c_0_33])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)),k5_xboole_0(k1_enumset1(X6,X6,X6),k3_xboole_0(k1_enumset1(X6,X6,X6),k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))))))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_38])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))))))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38]),c_0_38])).

fof(c_0_44,plain,(
    ! [X60,X61,X62,X63,X64,X65,X66,X67] : k6_enumset1(X60,X61,X62,X63,X64,X65,X66,X67) = k2_xboole_0(k1_tarski(X60),k5_enumset1(X61,X62,X63,X64,X65,X66,X67)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t71_enumset1])).

fof(c_0_46,plain,(
    ! [X27,X28,X29,X30] : k2_enumset1(X27,X28,X29,X30) = k2_xboole_0(k1_tarski(X27),k1_enumset1(X28,X29,X30)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_47,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X2,X2,X3)))),k1_enumset1(X1,X1,X1)))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_38]),c_0_38])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) = k5_enumset1(X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_51,negated_conjecture,(
    k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

cnf(c_0_52,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_31]),c_0_25]),c_0_25]),c_0_26])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k1_enumset1(X1,X1,X1)))))) = k5_enumset1(X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_49])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)),X7))) = k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_49]),c_0_38])).

cnf(c_0_56,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_31]),c_0_25]),c_0_26])).

cnf(c_0_57,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_31]),c_0_25]),c_0_26])).

fof(c_0_59,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_60,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X3,X3) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_53,c_0_49])).

cnf(c_0_61,plain,
    ( k6_enumset1(X1,X2,X2,X2,X3,X4,X5,X6) = k5_enumset1(X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k3_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk1_0,esk1_0,esk1_0)))) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X2,X2,X2,X3,X4,X4,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_60]),c_0_49])).

cnf(c_0_65,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X3,X3) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k3_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)))) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)))) = k5_enumset1(X1,X1,X2,X3,X4,X5,X6) ),
    inference(spm,[status(thm)],[c_0_49,c_0_63])).

cnf(c_0_68,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:17:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.38  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 0.19/0.38  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(t61_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 0.19/0.38  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.19/0.38  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.38  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 0.19/0.38  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 0.19/0.38  fof(t71_enumset1, conjecture, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.19/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.38  fof(c_0_15, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.38  fof(c_0_16, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.38  fof(c_0_17, plain, ![X36, X37, X38, X39, X40]:k3_enumset1(X36,X37,X38,X39,X40)=k2_xboole_0(k2_tarski(X36,X37),k1_enumset1(X38,X39,X40)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.19/0.38  fof(c_0_18, plain, ![X85, X86]:k1_enumset1(X85,X85,X86)=k2_tarski(X85,X86), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_21, plain, ![X18, X19, X20, X21, X22, X23]:k4_enumset1(X18,X19,X20,X21,X22,X23)=k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X21,X22,X23)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 0.19/0.38  fof(c_0_22, plain, ![X47, X48, X49, X50, X51, X52]:k4_enumset1(X47,X48,X49,X50,X51,X52)=k2_xboole_0(k3_enumset1(X47,X48,X49,X50,X51),k1_tarski(X52)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.19/0.38  fof(c_0_23, plain, ![X84]:k2_tarski(X84,X84)=k1_tarski(X84), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  cnf(c_0_24, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  cnf(c_0_27, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  fof(c_0_28, plain, ![X53, X54, X55, X56, X57, X58, X59]:k5_enumset1(X53,X54,X55,X56,X57,X58,X59)=k2_xboole_0(k4_enumset1(X53,X54,X55,X56,X57,X58),k1_tarski(X59)), inference(variable_rename,[status(thm)],[t61_enumset1])).
% 0.19/0.38  fof(c_0_29, plain, ![X41, X42, X43, X44, X45, X46]:k4_enumset1(X41,X42,X43,X44,X45,X46)=k2_xboole_0(k1_tarski(X41),k3_enumset1(X42,X43,X44,X45,X46)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.19/0.38  cnf(c_0_30, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_32, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.19/0.38  cnf(c_0_33, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.19/0.38  fof(c_0_34, plain, ![X13, X14, X15]:k5_xboole_0(k5_xboole_0(X13,X14),X15)=k5_xboole_0(X13,k5_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.38  cnf(c_0_35, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_36, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_37, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))),k5_xboole_0(k1_enumset1(X6,X6,X6),k3_xboole_0(k1_enumset1(X6,X6,X6),k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_25]), c_0_26]), c_0_32]), c_0_32]), c_0_33])).
% 0.19/0.38  cnf(c_0_38, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_39, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_31]), c_0_25]), c_0_26]), c_0_33]), c_0_33])).
% 0.19/0.38  fof(c_0_40, plain, ![X24, X25, X26]:k1_enumset1(X24,X25,X26)=k2_xboole_0(k2_tarski(X24,X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.19/0.38  cnf(c_0_41, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))=k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X2,X2,X3)))),k3_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X2,X2,X3)))),k1_enumset1(X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_31]), c_0_25]), c_0_26]), c_0_32]), c_0_32]), c_0_33])).
% 0.19/0.38  cnf(c_0_42, plain, (k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)),k5_xboole_0(k1_enumset1(X6,X6,X6),k3_xboole_0(k1_enumset1(X6,X6,X6),k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))))))))=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_38])).
% 0.19/0.38  cnf(c_0_43, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))))))))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_38]), c_0_38])).
% 0.19/0.38  fof(c_0_44, plain, ![X60, X61, X62, X63, X64, X65, X66, X67]:k6_enumset1(X60,X61,X62,X63,X64,X65,X66,X67)=k2_xboole_0(k1_tarski(X60),k5_enumset1(X61,X62,X63,X64,X65,X66,X67)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.19/0.38  fof(c_0_45, negated_conjecture, ~(![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_46, plain, ![X27, X28, X29, X30]:k2_enumset1(X27,X28,X29,X30)=k2_xboole_0(k1_tarski(X27),k1_enumset1(X28,X29,X30)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.19/0.38  cnf(c_0_47, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_48, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X2,X2,X3)))),k1_enumset1(X1,X1,X1))))))=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_38]), c_0_38])).
% 0.19/0.38  cnf(c_0_49, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))=k5_enumset1(X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.38  cnf(c_0_50, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.38  fof(c_0_51, negated_conjecture, k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 0.19/0.38  cnf(c_0_52, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.38  cnf(c_0_53, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_31]), c_0_25]), c_0_25]), c_0_26])).
% 0.19/0.38  cnf(c_0_54, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k1_enumset1(X1,X1,X1))))))=k5_enumset1(X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_49])).
% 0.19/0.38  cnf(c_0_55, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)),X7)))=k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_49]), c_0_38])).
% 0.19/0.38  cnf(c_0_56, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_31]), c_0_25]), c_0_26])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.38  cnf(c_0_58, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_31]), c_0_25]), c_0_26])).
% 0.19/0.38  fof(c_0_59, plain, ![X9, X10]:k3_xboole_0(X9,X10)=k3_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.38  cnf(c_0_60, plain, (k5_enumset1(X1,X1,X1,X2,X3,X3,X3)=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[c_0_53, c_0_49])).
% 0.19/0.38  cnf(c_0_61, plain, (k6_enumset1(X1,X2,X2,X2,X3,X4,X5,X6)=k5_enumset1(X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k3_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk1_0,esk1_0,esk1_0))))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.38  cnf(c_0_63, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.38  cnf(c_0_64, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X2,X2,X2,X3,X4,X4,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_60]), c_0_49])).
% 0.19/0.38  cnf(c_0_65, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X3,X3)=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k3_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0))))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.38  cnf(c_0_67, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))))=k5_enumset1(X1,X1,X2,X3,X4,X5,X6)), inference(spm,[status(thm)],[c_0_49, c_0_63])).
% 0.19/0.38  cnf(c_0_68, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_68])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 70
% 0.19/0.38  # Proof object clause steps            : 39
% 0.19/0.38  # Proof object formula steps           : 31
% 0.19/0.38  # Proof object conjectures             : 7
% 0.19/0.38  # Proof object clause conjectures      : 4
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 15
% 0.19/0.38  # Proof object initial formulas used   : 15
% 0.19/0.38  # Proof object generating inferences   : 5
% 0.19/0.38  # Proof object simplifying inferences  : 50
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 18
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 18
% 0.19/0.38  # Removed in clause preprocessing      : 7
% 0.19/0.38  # Initial clauses in saturation        : 11
% 0.19/0.38  # Processed clauses                    : 215
% 0.19/0.38  # ...of these trivial                  : 30
% 0.19/0.38  # ...subsumed                          : 114
% 0.19/0.38  # ...remaining for further processing  : 71
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 19
% 0.19/0.38  # Generated clauses                    : 1223
% 0.19/0.38  # ...of the previous two non-trivial   : 950
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 1223
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 41
% 0.19/0.38  #    Positive orientable unit clauses  : 25
% 0.19/0.38  #    Positive unorientable unit clauses: 16
% 0.19/0.38  #    Negative unit clauses             : 0
% 0.19/0.38  #    Non-unit-clauses                  : 0
% 0.19/0.38  # Current number of unprocessed clauses: 753
% 0.19/0.38  # ...number of literals in the above   : 753
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 37
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 130
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 860
% 0.19/0.38  # BW rewrite match successes           : 93
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 9125
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.041 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.046 s
% 0.19/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
