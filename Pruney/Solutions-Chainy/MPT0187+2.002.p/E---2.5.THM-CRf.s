%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:16 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   62 (1340 expanded)
%              Number of clauses        :   33 ( 565 expanded)
%              Number of leaves         :   14 ( 387 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 (1340 expanded)
%              Number of equality atoms :   61 (1339 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t100_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(t58_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(t52_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

fof(t105_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(c_0_14,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X10,X11),k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_15,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X21,X22,X23,X24,X25] : k3_enumset1(X21,X22,X23,X24,X25) = k2_xboole_0(k2_enumset1(X21,X22,X23,X24),k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_17,plain,(
    ! [X61] : k3_enumset1(X61,X61,X61,X61,X61) = k1_tarski(X61) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

fof(c_0_18,plain,(
    ! [X57,X58,X59,X60] : k3_enumset1(X57,X57,X58,X59,X60) = k2_enumset1(X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k4_enumset1(X32,X33,X34,X35,X36,X37) = k2_xboole_0(k3_enumset1(X32,X33,X34,X35,X36),k1_tarski(X37)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] : k1_enumset1(X18,X19,X20) = k1_enumset1(X19,X20,X18) ),
    inference(variable_rename,[status(thm)],[t100_enumset1])).

fof(c_0_23,plain,(
    ! [X54,X55,X56] : k2_enumset1(X54,X54,X55,X56) = k1_enumset1(X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X12,X13,X14,X15,X16,X17] : k4_enumset1(X12,X13,X14,X15,X16,X17) = k2_xboole_0(k1_enumset1(X12,X13,X14),k1_enumset1(X15,X16,X17)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

fof(c_0_30,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51] : k5_enumset1(X45,X46,X47,X48,X49,X50,X51) = k2_xboole_0(k1_enumset1(X45,X46,X47),k2_enumset1(X48,X49,X50,X51)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

fof(c_0_31,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k4_enumset1(X26,X27,X28,X29,X30,X31) = k2_xboole_0(k2_tarski(X26,X27),k2_enumset1(X28,X29,X30,X31)) ),
    inference(variable_rename,[status(thm)],[t52_enumset1])).

fof(c_0_32,plain,(
    ! [X52,X53] : k1_enumset1(X52,X52,X53) = k2_tarski(X52,X53) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5)),k4_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X6,X6,X6,X6,X6)),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X6,X6,X6,X6,X6)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_25]),c_0_27])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44] : k5_enumset1(X38,X39,X40,X41,X42,X43,X44) = k2_xboole_0(k2_tarski(X38,X39),k3_enumset1(X40,X41,X42,X43,X44)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

cnf(c_0_42,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_enumset1(X2,X2,X2,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_26]),c_0_26])).

cnf(c_0_43,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X6)),k4_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k4_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X6)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_34]),c_0_34]),c_0_26]),c_0_26]),c_0_27])).

cnf(c_0_45,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X5,X6,X7)),k4_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k4_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_34]),c_0_26]),c_0_26]),c_0_27])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X4,X5,X6)),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X4,X5,X6)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_34]),c_0_26]),c_0_26]),c_0_27])).

fof(c_0_47,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(assume_negation,[status(cth)],[t105_enumset1])).

cnf(c_0_48,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X3,X3,X1,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_42]),c_0_36]),c_0_43]),c_0_43])).

cnf(c_0_50,plain,
    ( k5_enumset1(X1,X2,X3,X4,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_46,c_0_45])).

fof(c_0_52,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk3_0,esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])).

cnf(c_0_53,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_40]),c_0_34]),c_0_26]),c_0_27])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X2,X2,X3) = k3_enumset1(X1,X1,X1,X3,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_55,plain,
    ( k4_enumset1(X1,X2,X3,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk3_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_enumset1(X3,X3,X2,X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_58,plain,
    ( k5_enumset1(X1,X2,X3,X3,X4,X4,X5) = k3_enumset1(X1,X2,X3,X5,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_53]),c_0_50]),c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk3_0,esk4_0,esk2_0) != k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_26]),c_0_26])).

cnf(c_0_60,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X4,X5,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_57]),c_0_53]),c_0_50]),c_0_55]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:49:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.14/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.026 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.14/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.14/0.38  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 0.14/0.38  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 0.14/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.38  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.14/0.38  fof(t100_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 0.14/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.38  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 0.14/0.38  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 0.14/0.38  fof(t52_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 0.14/0.38  fof(t105_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 0.14/0.38  fof(c_0_14, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k5_xboole_0(k5_xboole_0(X10,X11),k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.14/0.38  fof(c_0_15, plain, ![X8, X9]:k4_xboole_0(X8,k4_xboole_0(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.14/0.38  fof(c_0_16, plain, ![X21, X22, X23, X24, X25]:k3_enumset1(X21,X22,X23,X24,X25)=k2_xboole_0(k2_enumset1(X21,X22,X23,X24),k1_tarski(X25)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.14/0.38  fof(c_0_17, plain, ![X61]:k3_enumset1(X61,X61,X61,X61,X61)=k1_tarski(X61), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 0.14/0.38  fof(c_0_18, plain, ![X57, X58, X59, X60]:k3_enumset1(X57,X57,X58,X59,X60)=k2_enumset1(X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.38  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  fof(c_0_21, plain, ![X32, X33, X34, X35, X36, X37]:k4_enumset1(X32,X33,X34,X35,X36,X37)=k2_xboole_0(k3_enumset1(X32,X33,X34,X35,X36),k1_tarski(X37)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.14/0.38  fof(c_0_22, plain, ![X18, X19, X20]:k1_enumset1(X18,X19,X20)=k1_enumset1(X19,X20,X18), inference(variable_rename,[status(thm)],[t100_enumset1])).
% 0.14/0.38  fof(c_0_23, plain, ![X54, X55, X56]:k2_enumset1(X54,X54,X55,X56)=k1_enumset1(X54,X55,X56), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.38  cnf(c_0_24, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.38  cnf(c_0_28, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  fof(c_0_29, plain, ![X12, X13, X14, X15, X16, X17]:k4_enumset1(X12,X13,X14,X15,X16,X17)=k2_xboole_0(k1_enumset1(X12,X13,X14),k1_enumset1(X15,X16,X17)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 0.14/0.38  fof(c_0_30, plain, ![X45, X46, X47, X48, X49, X50, X51]:k5_enumset1(X45,X46,X47,X48,X49,X50,X51)=k2_xboole_0(k1_enumset1(X45,X46,X47),k2_enumset1(X48,X49,X50,X51)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 0.14/0.38  fof(c_0_31, plain, ![X26, X27, X28, X29, X30, X31]:k4_enumset1(X26,X27,X28,X29,X30,X31)=k2_xboole_0(k2_tarski(X26,X27),k2_enumset1(X28,X29,X30,X31)), inference(variable_rename,[status(thm)],[t52_enumset1])).
% 0.14/0.38  fof(c_0_32, plain, ![X52, X53]:k1_enumset1(X52,X52,X53)=k2_tarski(X52,X53), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  cnf(c_0_33, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_35, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5)),k4_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])).
% 0.14/0.38  cnf(c_0_36, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X6,X6,X6,X6,X6)),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X6,X6,X6,X6,X6))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_25]), c_0_27])).
% 0.14/0.38  cnf(c_0_37, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_38, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_39, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_40, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.38  fof(c_0_41, plain, ![X38, X39, X40, X41, X42, X43, X44]:k5_enumset1(X38,X39,X40,X41,X42,X43,X44)=k2_xboole_0(k2_tarski(X38,X39),k3_enumset1(X40,X41,X42,X43,X44)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 0.14/0.38  cnf(c_0_42, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_enumset1(X2,X2,X2,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_26]), c_0_26])).
% 0.14/0.38  cnf(c_0_43, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.38  cnf(c_0_44, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X6)),k4_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k4_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X6))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_34]), c_0_34]), c_0_26]), c_0_26]), c_0_27])).
% 0.14/0.38  cnf(c_0_45, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X5,X6,X7)),k4_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k4_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X5,X6,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_34]), c_0_26]), c_0_26]), c_0_27])).
% 0.14/0.38  cnf(c_0_46, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X4,X5,X6)),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X4,X5,X6))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_34]), c_0_26]), c_0_26]), c_0_27])).
% 0.14/0.38  fof(c_0_47, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(assume_negation,[status(cth)],[t105_enumset1])).
% 0.14/0.38  cnf(c_0_48, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X3,X3,X1,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_42]), c_0_36]), c_0_43]), c_0_43])).
% 0.14/0.38  cnf(c_0_50, plain, (k5_enumset1(X1,X2,X3,X4,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.38  cnf(c_0_51, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_46, c_0_45])).
% 0.14/0.38  fof(c_0_52, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk3_0,esk4_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])).
% 0.14/0.38  cnf(c_0_53, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_40]), c_0_34]), c_0_26]), c_0_27])).
% 0.14/0.38  cnf(c_0_54, plain, (k3_enumset1(X1,X1,X2,X2,X3)=k3_enumset1(X1,X1,X1,X3,X2)), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.14/0.38  cnf(c_0_55, plain, (k4_enumset1(X1,X2,X3,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_43])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk3_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.38  cnf(c_0_57, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_enumset1(X3,X3,X2,X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.14/0.38  cnf(c_0_58, plain, (k5_enumset1(X1,X2,X3,X3,X4,X4,X5)=k3_enumset1(X1,X2,X3,X5,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_53]), c_0_50]), c_0_55])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk3_0,esk4_0,esk2_0)!=k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_26]), c_0_26])).
% 0.14/0.38  cnf(c_0_60, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X4,X5,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_57]), c_0_53]), c_0_50]), c_0_55]), c_0_58])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_60])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 62
% 0.14/0.38  # Proof object clause steps            : 33
% 0.14/0.38  # Proof object formula steps           : 29
% 0.14/0.38  # Proof object conjectures             : 6
% 0.14/0.38  # Proof object clause conjectures      : 3
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 14
% 0.14/0.38  # Proof object initial formulas used   : 14
% 0.14/0.38  # Proof object generating inferences   : 6
% 0.14/0.38  # Proof object simplifying inferences  : 47
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 14
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 14
% 0.14/0.38  # Removed in clause preprocessing      : 6
% 0.14/0.38  # Initial clauses in saturation        : 8
% 0.14/0.38  # Processed clauses                    : 44
% 0.14/0.38  # ...of these trivial                  : 2
% 0.14/0.38  # ...subsumed                          : 10
% 0.14/0.38  # ...remaining for further processing  : 32
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 4
% 0.14/0.38  # Generated clauses                    : 286
% 0.14/0.38  # ...of the previous two non-trivial   : 219
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 286
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 20
% 0.14/0.38  #    Positive orientable unit clauses  : 11
% 0.14/0.38  #    Positive unorientable unit clauses: 9
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 0
% 0.14/0.38  # Current number of unprocessed clauses: 191
% 0.14/0.38  # ...number of literals in the above   : 191
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 18
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 50
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 258
% 0.14/0.38  # BW rewrite match successes           : 118
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2637
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.028 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
