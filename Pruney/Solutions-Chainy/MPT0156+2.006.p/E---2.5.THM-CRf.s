%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:41 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 792 expanded)
%              Number of clauses        :   32 ( 307 expanded)
%              Number of leaves         :   13 ( 242 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 792 expanded)
%              Number of equality atoms :   58 ( 791 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t64_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t66_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t72_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(c_0_13,plain,(
    ! [X29,X30,X31,X32,X33] : k3_enumset1(X29,X30,X31,X32,X33) = k2_xboole_0(k1_tarski(X29),k2_enumset1(X30,X31,X32,X33)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_14,plain,(
    ! [X56] : k2_tarski(X56,X56) = k1_tarski(X56) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X57,X58] : k1_enumset1(X57,X57,X58) = k2_tarski(X57,X58) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k5_xboole_0(X9,k4_xboole_0(X10,X9)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_17,plain,(
    ! [X59,X60,X61] : k2_enumset1(X59,X59,X60,X61) = k1_enumset1(X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] : k6_enumset1(X15,X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k2_enumset1(X15,X16,X17,X18),k2_enumset1(X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_19,plain,(
    ! [X34,X35,X36,X37,X38,X39] : k4_enumset1(X34,X35,X36,X37,X38,X39) = k2_xboole_0(k1_tarski(X34),k3_enumset1(X35,X36,X37,X38,X39)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46,X47] : k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) = k2_xboole_0(k1_enumset1(X40,X41,X42),k3_enumset1(X43,X44,X45,X46,X47)) ),
    inference(variable_rename,[status(thm)],[t64_enumset1])).

cnf(c_0_26,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X23,X24] : k2_tarski(X23,X24) = k2_xboole_0(k1_tarski(X23),k1_tarski(X24)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_28,plain,(
    ! [X25,X26,X27,X28] : k2_enumset1(X25,X26,X27,X28) = k2_xboole_0(k1_tarski(X25),k1_enumset1(X26,X27,X28)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_29,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54,X55] : k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) = k2_xboole_0(k3_enumset1(X48,X49,X50,X51,X52),k1_enumset1(X53,X54,X55)) ),
    inference(variable_rename,[status(thm)],[t66_enumset1])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_24])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_23])).

fof(c_0_34,plain,(
    ! [X11,X12,X13,X14] : k2_enumset1(X11,X12,X13,X14) = k2_xboole_0(k2_tarski(X11,X12),k2_tarski(X13,X14)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(assume_negation,[status(cth)],[t72_enumset1])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_enumset1(X2,X2,X2,X2))),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_24]),c_0_31])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k5_xboole_0(k2_enumset1(X4,X4,X4,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X4,X4,X4,X4))),k2_enumset1(X1,X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_23]),c_0_24]),c_0_24]),c_0_31]),c_0_33])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_24]),c_0_24])).

fof(c_0_44,negated_conjecture,(
    k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1))),k4_xboole_0(k2_enumset1(X6,X6,X7,X8),k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_23]),c_0_24]),c_0_31]),c_0_31]),c_0_33])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_enumset1(X1,X1,X1,X2))) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_22]),c_0_22]),c_0_23]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X2,X2,X2) = k2_enumset1(X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_xboole_0(k2_enumset1(X6,X6,X7,X8),k4_enumset1(X1,X1,X2,X3,X4,X5))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_46])).

cnf(c_0_51,plain,
    ( k4_enumset1(X1,X2,X3,X3,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X2,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_enumset1(X1,X2,X2,X2))) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(spm,[status(thm)],[c_0_46,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_31])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X1,X1,X2,X3))) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_55,plain,
    ( k4_enumset1(X1,X1,X2,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_43,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_57,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_54]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 0.13/0.38  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.13/0.38  fof(t64_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 0.13/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.13/0.38  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.13/0.38  fof(t66_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 0.13/0.38  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.13/0.38  fof(t72_enumset1, conjecture, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(c_0_13, plain, ![X29, X30, X31, X32, X33]:k3_enumset1(X29,X30,X31,X32,X33)=k2_xboole_0(k1_tarski(X29),k2_enumset1(X30,X31,X32,X33)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.13/0.38  fof(c_0_14, plain, ![X56]:k2_tarski(X56,X56)=k1_tarski(X56), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_15, plain, ![X57, X58]:k1_enumset1(X57,X57,X58)=k2_tarski(X57,X58), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_16, plain, ![X9, X10]:k2_xboole_0(X9,X10)=k5_xboole_0(X9,k4_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.38  fof(c_0_17, plain, ![X59, X60, X61]:k2_enumset1(X59,X59,X60,X61)=k1_enumset1(X59,X60,X61), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_18, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:k6_enumset1(X15,X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k2_enumset1(X15,X16,X17,X18),k2_enumset1(X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.13/0.38  fof(c_0_19, plain, ![X34, X35, X36, X37, X38, X39]:k4_enumset1(X34,X35,X36,X37,X38,X39)=k2_xboole_0(k1_tarski(X34),k3_enumset1(X35,X36,X37,X38,X39)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.13/0.38  cnf(c_0_20, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_25, plain, ![X40, X41, X42, X43, X44, X45, X46, X47]:k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)=k2_xboole_0(k1_enumset1(X40,X41,X42),k3_enumset1(X43,X44,X45,X46,X47)), inference(variable_rename,[status(thm)],[t64_enumset1])).
% 0.13/0.38  cnf(c_0_26, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_27, plain, ![X23, X24]:k2_tarski(X23,X24)=k2_xboole_0(k1_tarski(X23),k1_tarski(X24)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.13/0.38  fof(c_0_28, plain, ![X25, X26, X27, X28]:k2_enumset1(X25,X26,X27,X28)=k2_xboole_0(k1_tarski(X25),k1_enumset1(X26,X27,X28)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.13/0.38  fof(c_0_29, plain, ![X48, X49, X50, X51, X52, X53, X54, X55]:k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55)=k2_xboole_0(k3_enumset1(X48,X49,X50,X51,X52),k1_enumset1(X53,X54,X55)), inference(variable_rename,[status(thm)],[t66_enumset1])).
% 0.13/0.38  cnf(c_0_30, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_31, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_24])).
% 0.13/0.38  cnf(c_0_32, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_33, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[c_0_26, c_0_23])).
% 0.13/0.38  fof(c_0_34, plain, ![X11, X12, X13, X14]:k2_enumset1(X11,X12,X13,X14)=k2_xboole_0(k2_tarski(X11,X12),k2_tarski(X13,X14)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.13/0.38  cnf(c_0_35, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_36, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  fof(c_0_37, negated_conjecture, ~(![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(assume_negation,[status(cth)],[t72_enumset1])).
% 0.13/0.38  cnf(c_0_38, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_39, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_enumset1(X2,X2,X2,X2))),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_24]), c_0_31])).
% 0.13/0.38  cnf(c_0_40, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k5_xboole_0(k2_enumset1(X4,X4,X4,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X4,X4,X4,X4))),k2_enumset1(X1,X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_23]), c_0_24]), c_0_24]), c_0_31]), c_0_33])).
% 0.13/0.38  cnf(c_0_41, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X1,X2)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.13/0.38  cnf(c_0_43, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_24]), c_0_24])).
% 0.13/0.38  fof(c_0_44, negated_conjecture, k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 0.13/0.38  cnf(c_0_45, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1))),k4_xboole_0(k2_enumset1(X6,X6,X7,X8),k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_23]), c_0_24]), c_0_31]), c_0_31]), c_0_33])).
% 0.13/0.38  cnf(c_0_46, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_enumset1(X1,X1,X1,X2)))=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_47, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_22]), c_0_22]), c_0_23]), c_0_24]), c_0_24]), c_0_24])).
% 0.13/0.38  cnf(c_0_48, plain, (k2_enumset1(X1,X2,X2,X2)=k2_enumset1(X1,X1,X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_50, plain, (k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_xboole_0(k2_enumset1(X6,X6,X7,X8),k4_enumset1(X1,X1,X2,X3,X4,X5)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_46])).
% 0.13/0.38  cnf(c_0_51, plain, (k4_enumset1(X1,X2,X3,X3,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_47, c_0_46])).
% 0.13/0.38  cnf(c_0_52, plain, (k5_xboole_0(k2_enumset1(X1,X2,X2,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_enumset1(X1,X2,X2,X2)))=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(spm,[status(thm)],[c_0_46, c_0_48])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_49, c_0_31])).
% 0.13/0.38  cnf(c_0_54, plain, (k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X1,X1,X2,X3)))=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.13/0.38  cnf(c_0_55, plain, (k4_enumset1(X1,X1,X2,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_43, c_0_46])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_53, c_0_46])).
% 0.13/0.38  cnf(c_0_57, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_54]), c_0_55])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 59
% 0.13/0.38  # Proof object clause steps            : 32
% 0.13/0.38  # Proof object formula steps           : 27
% 0.13/0.38  # Proof object conjectures             : 7
% 0.13/0.38  # Proof object clause conjectures      : 4
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 13
% 0.13/0.38  # Proof object initial formulas used   : 13
% 0.13/0.38  # Proof object generating inferences   : 3
% 0.13/0.38  # Proof object simplifying inferences  : 56
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 13
% 0.13/0.38  # Removed in clause preprocessing      : 6
% 0.13/0.38  # Initial clauses in saturation        : 7
% 0.13/0.38  # Processed clauses                    : 84
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 47
% 0.13/0.38  # ...remaining for further processing  : 34
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 6
% 0.13/0.38  # Generated clauses                    : 276
% 0.13/0.38  # ...of the previous two non-trivial   : 202
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 276
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
% 0.13/0.38  #    Positive orientable unit clauses  : 12
% 0.13/0.38  #    Positive unorientable unit clauses: 8
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 0
% 0.13/0.38  # Current number of unprocessed clauses: 130
% 0.13/0.38  # ...number of literals in the above   : 130
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 20
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 24
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 223
% 0.13/0.38  # BW rewrite match successes           : 49
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2978
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
