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
% DateTime   : Thu Dec  3 10:35:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 (1345 expanded)
%              Number of clauses        :   32 ( 600 expanded)
%              Number of leaves         :   11 ( 372 expanded)
%              Depth                    :   15
%              Number of atoms          :   55 (1345 expanded)
%              Number of equality atoms :   54 (1344 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(t58_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(t75_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(c_0_11,plain,(
    ! [X26,X27,X28] : k1_enumset1(X26,X27,X28) = k2_xboole_0(k1_tarski(X26),k2_tarski(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_12,plain,(
    ! [X55] : k2_tarski(X55,X55) = k1_tarski(X55) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X29,X30,X31,X32] : k2_enumset1(X29,X30,X31,X32) = k2_xboole_0(k1_enumset1(X29,X30,X31),k1_tarski(X32)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46] : k5_enumset1(X40,X41,X42,X43,X44,X45,X46) = k2_xboole_0(k1_enumset1(X40,X41,X42),k2_enumset1(X43,X44,X45,X46)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15] : k5_enumset1(X9,X10,X11,X12,X13,X14,X15) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X13,X14,X15)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

cnf(c_0_20,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X4,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_15]),c_0_18])).

fof(c_0_22,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_xboole_0(k1_tarski(X24),k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_23,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_21])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X4,X4)),k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_21]),c_0_24])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_15]),c_0_15])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X6,X6))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X4,X4)),k2_tarski(X5,X6)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X4,X5)),k2_tarski(X5,X5))) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3)),k2_tarski(X4,X5)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

fof(c_0_30,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39] : k5_enumset1(X33,X34,X35,X36,X37,X38,X39) = k2_xboole_0(k1_tarski(X33),k4_enumset1(X34,X35,X36,X37,X38,X39)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

fof(c_0_31,plain,(
    ! [X56,X57,X58,X59,X60,X61] : k5_enumset1(X56,X56,X57,X58,X59,X60,X61) = k4_enumset1(X56,X57,X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_32,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53,X54] : k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) = k2_xboole_0(k1_tarski(X47),k5_enumset1(X48,X49,X50,X51,X52,X53,X54)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X4,X4))) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3)),k2_tarski(X4,X4)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(assume_negation,[status(cth)],[t75_enumset1])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3)),k2_tarski(X4,X4)) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_33]),c_0_27]),c_0_27])).

fof(c_0_39,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] : k6_enumset1(X16,X17,X18,X19,X20,X21,X22,X23) = k2_xboole_0(k2_enumset1(X16,X17,X18,X19),k2_enumset1(X20,X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_40,negated_conjecture,(
    k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7))) = k2_xboole_0(k2_tarski(X1,X1),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_15]),c_0_36]),c_0_24]),c_0_24])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X1),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X6,X7)),k2_tarski(X8,X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_15]),c_0_24])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3)) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_27])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X2,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X4,X4)) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X4,X4)),k2_xboole_0(k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X6,X7)),k2_tarski(X8,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_21]),c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk2_0,esk3_0)),k2_xboole_0(k2_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk5_0,esk6_0)),k2_tarski(esk7_0,esk7_0))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_24])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X2,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X8))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_47]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_46])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X2,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:58:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.023 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.13/0.38  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 0.13/0.38  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 0.13/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.13/0.38  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 0.13/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.38  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 0.13/0.38  fof(t75_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.38  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 0.13/0.38  fof(c_0_11, plain, ![X26, X27, X28]:k1_enumset1(X26,X27,X28)=k2_xboole_0(k1_tarski(X26),k2_tarski(X27,X28)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.13/0.38  fof(c_0_12, plain, ![X55]:k2_tarski(X55,X55)=k1_tarski(X55), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_13, plain, ![X29, X30, X31, X32]:k2_enumset1(X29,X30,X31,X32)=k2_xboole_0(k1_enumset1(X29,X30,X31),k1_tarski(X32)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.13/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_16, plain, ![X40, X41, X42, X43, X44, X45, X46]:k5_enumset1(X40,X41,X42,X43,X44,X45,X46)=k2_xboole_0(k1_enumset1(X40,X41,X42),k2_enumset1(X43,X44,X45,X46)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 0.13/0.38  cnf(c_0_17, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_18, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  fof(c_0_19, plain, ![X9, X10, X11, X12, X13, X14, X15]:k5_enumset1(X9,X10,X11,X12,X13,X14,X15)=k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X13,X14,X15)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.13/0.38  cnf(c_0_20, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_21, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X4,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_15]), c_0_18])).
% 0.13/0.38  fof(c_0_22, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_xboole_0(k1_tarski(X24),k1_tarski(X25)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.13/0.38  cnf(c_0_23, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_24, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_21])).
% 0.13/0.38  cnf(c_0_25, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_26, plain, (k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7)))=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X4,X4)),k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_18]), c_0_21]), c_0_24])).
% 0.13/0.38  cnf(c_0_27, plain, (k2_tarski(X1,X2)=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_15]), c_0_15])).
% 0.13/0.38  cnf(c_0_28, plain, (k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X6,X6)))=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X4,X4)),k2_tarski(X5,X6))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_29, plain, (k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X4,X5)),k2_tarski(X5,X5)))=k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3)),k2_tarski(X4,X5))), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.13/0.38  fof(c_0_30, plain, ![X33, X34, X35, X36, X37, X38, X39]:k5_enumset1(X33,X34,X35,X36,X37,X38,X39)=k2_xboole_0(k1_tarski(X33),k4_enumset1(X34,X35,X36,X37,X38,X39)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 0.13/0.38  fof(c_0_31, plain, ![X56, X57, X58, X59, X60, X61]:k5_enumset1(X56,X56,X57,X58,X59,X60,X61)=k4_enumset1(X56,X57,X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.38  fof(c_0_32, plain, ![X47, X48, X49, X50, X51, X52, X53, X54]:k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)=k2_xboole_0(k1_tarski(X47),k5_enumset1(X48,X49,X50,X51,X52,X53,X54)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.13/0.38  cnf(c_0_33, plain, (k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X4,X4)))=k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3)),k2_tarski(X4,X4))), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.13/0.38  fof(c_0_34, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(assume_negation,[status(cth)],[t75_enumset1])).
% 0.13/0.38  cnf(c_0_35, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_37, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_38, plain, (k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3)),k2_tarski(X4,X4))=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_33]), c_0_27]), c_0_27])).
% 0.13/0.38  fof(c_0_39, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:k6_enumset1(X16,X17,X18,X19,X20,X21,X22,X23)=k2_xboole_0(k2_enumset1(X16,X17,X18,X19),k2_enumset1(X20,X21,X22,X23)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.13/0.38  fof(c_0_40, negated_conjecture, k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 0.13/0.38  cnf(c_0_41, plain, (k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7)))=k2_xboole_0(k2_tarski(X1,X1),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_15]), c_0_36]), c_0_24]), c_0_24])).
% 0.13/0.38  cnf(c_0_42, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X1),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X6,X7)),k2_tarski(X8,X8))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_15]), c_0_24])).
% 0.13/0.38  cnf(c_0_43, plain, (k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3))=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3))), inference(spm,[status(thm)],[c_0_38, c_0_27])).
% 0.13/0.38  cnf(c_0_44, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_46, plain, (k6_enumset1(X1,X2,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7)))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_47, plain, (k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X4,X4))=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(spm,[status(thm)],[c_0_38, c_0_43])).
% 0.13/0.38  cnf(c_0_48, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X4,X4)),k2_xboole_0(k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X6,X7)),k2_tarski(X8,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_21]), c_0_21])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk2_0,esk3_0)),k2_xboole_0(k2_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk5_0,esk6_0)),k2_tarski(esk7_0,esk7_0)))), inference(rw,[status(thm)],[c_0_45, c_0_24])).
% 0.13/0.38  cnf(c_0_50, plain, (k6_enumset1(X1,X2,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7)))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.38  cnf(c_0_51, plain, (k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X8)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_47]), c_0_47])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_49, c_0_46])).
% 0.13/0.38  cnf(c_0_53, plain, (k6_enumset1(X1,X2,X2,X3,X4,X5,X6,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 55
% 0.13/0.38  # Proof object clause steps            : 32
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 7
% 0.13/0.38  # Proof object clause conjectures      : 4
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 6
% 0.13/0.38  # Proof object simplifying inferences  : 29
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 11
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 11
% 0.13/0.38  # Removed in clause preprocessing      : 5
% 0.13/0.38  # Initial clauses in saturation        : 6
% 0.13/0.38  # Processed clauses                    : 105
% 0.13/0.38  # ...of these trivial                  : 11
% 0.13/0.38  # ...subsumed                          : 55
% 0.13/0.38  # ...remaining for further processing  : 39
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 13
% 0.13/0.38  # Generated clauses                    : 405
% 0.13/0.38  # ...of the previous two non-trivial   : 331
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 405
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 20
% 0.13/0.38  #    Positive orientable unit clauses  : 15
% 0.13/0.38  #    Positive unorientable unit clauses: 5
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 0
% 0.13/0.38  # Current number of unprocessed clauses: 233
% 0.13/0.38  # ...number of literals in the above   : 233
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 24
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 33
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 165
% 0.13/0.38  # BW rewrite match successes           : 49
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6307
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.029 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
