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
% DateTime   : Thu Dec  3 10:35:11 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (2732 expanded)
%              Number of clauses        :   33 (1109 expanded)
%              Number of leaves         :   10 ( 811 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (2732 expanded)
%              Number of equality atoms :   53 (2731 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t55_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X22] : k2_enumset1(X19,X20,X21,X22) = k2_xboole_0(k1_tarski(X19),k1_enumset1(X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_11,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(assume_negation,[status(cth)],[t55_enumset1])).

fof(c_0_14,plain,(
    ! [X37,X38,X39,X40,X41,X42] : k4_enumset1(X37,X38,X39,X40,X41,X42) = k2_xboole_0(k1_tarski(X37),k3_enumset1(X38,X39,X40,X41,X42)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_15,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_16,plain,(
    ! [X27,X28,X29,X30,X31] : k3_enumset1(X27,X28,X29,X30,X31) = k2_xboole_0(k1_tarski(X27),k2_enumset1(X28,X29,X30,X31)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X32,X33,X34,X35,X36] : k3_enumset1(X32,X33,X34,X35,X36) = k2_xboole_0(k2_enumset1(X32,X33,X34,X35),k1_tarski(X36)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_21,plain,(
    ! [X23,X24,X25,X26] : k2_enumset1(X23,X24,X25,X26) = k2_xboole_0(k1_enumset1(X23,X24,X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_22,negated_conjecture,(
    k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_23,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X13,X14,X15,X16,X17,X18] : k4_enumset1(X13,X14,X15,X16,X17,X18) = k2_xboole_0(k1_enumset1(X13,X14,X15),k1_enumset1(X16,X17,X18)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_19])).

cnf(c_0_32,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_18]),c_0_19]),c_0_27]),c_0_27])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_18]),c_0_19]),c_0_27]),c_0_27])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_18]),c_0_19]),c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k3_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk1_0)))) != k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k5_xboole_0(k1_tarski(esk6_0),k3_xboole_0(k1_tarski(esk6_0),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_18]),c_0_19]),c_0_31])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_18]),c_0_19]),c_0_31])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X2,X3,X4,X5,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X4,X1,X2,X3,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_36]),c_0_36]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k3_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)))) != k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k3_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))) = k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_enumset1(X5,X6,X1,X2,X3),k3_xboole_0(k3_enumset1(X5,X6,X1,X2,X3),k1_tarski(X4)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_38]),c_0_38])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X1,X5,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_36]),c_0_36]),c_0_34])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X3,X4,X5,X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_39])).

cnf(c_0_45,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X5,X4,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X3,X5,X1,X2,X4) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X3,X4,X1,X2,X5) ),
    inference(spm,[status(thm)],[c_0_40,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k3_xboole_0(k3_enumset1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk3_0)))) != k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k3_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_40]),c_0_43]),c_0_40]),c_0_43])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))) = k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_enumset1(X1,X2,X3,X5,X6),k3_xboole_0(k3_enumset1(X1,X2,X3,X5,X6),k1_tarski(X4)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_44])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X1,X3,X5,X4,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X5,X4) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_52,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X4,X5,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_50]),c_0_51]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.42  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.026 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.21/0.42  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.42  fof(t55_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.21/0.42  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.21/0.42  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.21/0.42  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.21/0.42  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.21/0.42  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.21/0.42  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 0.21/0.42  fof(c_0_10, plain, ![X19, X20, X21, X22]:k2_enumset1(X19,X20,X21,X22)=k2_xboole_0(k1_tarski(X19),k1_enumset1(X20,X21,X22)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.21/0.42  fof(c_0_11, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(X11,k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.42  fof(c_0_12, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.42  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(assume_negation,[status(cth)],[t55_enumset1])).
% 0.21/0.42  fof(c_0_14, plain, ![X37, X38, X39, X40, X41, X42]:k4_enumset1(X37,X38,X39,X40,X41,X42)=k2_xboole_0(k1_tarski(X37),k3_enumset1(X38,X39,X40,X41,X42)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.21/0.42  fof(c_0_15, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.21/0.42  fof(c_0_16, plain, ![X27, X28, X29, X30, X31]:k3_enumset1(X27,X28,X29,X30,X31)=k2_xboole_0(k1_tarski(X27),k2_enumset1(X28,X29,X30,X31)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.21/0.42  cnf(c_0_17, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.42  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.42  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.42  fof(c_0_20, plain, ![X32, X33, X34, X35, X36]:k3_enumset1(X32,X33,X34,X35,X36)=k2_xboole_0(k2_enumset1(X32,X33,X34,X35),k1_tarski(X36)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.21/0.42  fof(c_0_21, plain, ![X23, X24, X25, X26]:k2_enumset1(X23,X24,X25,X26)=k2_xboole_0(k1_enumset1(X23,X24,X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.21/0.42  fof(c_0_22, negated_conjecture, k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.21/0.42  cnf(c_0_23, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.42  fof(c_0_24, plain, ![X13, X14, X15, X16, X17, X18]:k4_enumset1(X13,X14,X15,X16,X17,X18)=k2_xboole_0(k1_enumset1(X13,X14,X15),k1_enumset1(X16,X17,X18)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 0.21/0.42  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.42  cnf(c_0_26, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.42  cnf(c_0_27, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.21/0.42  cnf(c_0_28, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.42  cnf(c_0_29, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_30, negated_conjecture, (k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  cnf(c_0_31, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_18]), c_0_19])).
% 0.21/0.42  cnf(c_0_32, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.42  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.21/0.42  cnf(c_0_34, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_18]), c_0_19]), c_0_27]), c_0_27])).
% 0.21/0.42  cnf(c_0_35, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_18]), c_0_19]), c_0_27]), c_0_27])).
% 0.21/0.42  cnf(c_0_36, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_18]), c_0_19]), c_0_27])).
% 0.21/0.42  cnf(c_0_37, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k3_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk1_0))))!=k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k5_xboole_0(k1_tarski(esk6_0),k3_xboole_0(k1_tarski(esk6_0),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_18]), c_0_19]), c_0_31])).
% 0.21/0.42  cnf(c_0_38, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1))))=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_18]), c_0_19]), c_0_31])).
% 0.21/0.42  cnf(c_0_39, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X2,X3,X4,X5,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.21/0.42  cnf(c_0_40, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X4,X1,X2,X3,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_33]), c_0_36]), c_0_36]), c_0_35])).
% 0.21/0.42  cnf(c_0_41, negated_conjecture, (k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k3_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0))))!=k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k3_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk1_0))))), inference(rw,[status(thm)],[c_0_37, c_0_33])).
% 0.21/0.42  cnf(c_0_42, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1))))=k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_enumset1(X5,X6,X1,X2,X3),k3_xboole_0(k3_enumset1(X5,X6,X1,X2,X3),k1_tarski(X4))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_38]), c_0_38])).
% 0.21/0.42  cnf(c_0_43, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X1,X5,X2,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_36]), c_0_36]), c_0_34])).
% 0.21/0.42  cnf(c_0_44, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X3,X4,X5,X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_39])).
% 0.21/0.42  cnf(c_0_45, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X5,X4,X1,X2,X3)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.21/0.42  cnf(c_0_46, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X3,X5,X1,X2,X4)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.21/0.42  cnf(c_0_47, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X3,X4,X1,X2,X5)), inference(spm,[status(thm)],[c_0_40, c_0_40])).
% 0.21/0.42  cnf(c_0_48, negated_conjecture, (k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k3_xboole_0(k3_enumset1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk3_0))))!=k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k3_xboole_0(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_40]), c_0_43]), c_0_40]), c_0_43])).
% 0.21/0.42  cnf(c_0_49, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1))))=k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_enumset1(X1,X2,X3,X5,X6),k3_xboole_0(k3_enumset1(X1,X2,X3,X5,X6),k1_tarski(X4))))), inference(spm,[status(thm)],[c_0_42, c_0_44])).
% 0.21/0.42  cnf(c_0_50, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X1,X3,X5,X4,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.42  cnf(c_0_51, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X5,X4)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.21/0.42  cnf(c_0_52, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X4,X5,X3)), inference(spm,[status(thm)],[c_0_47, c_0_44])).
% 0.21/0.42  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_50]), c_0_51]), c_0_52])]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 54
% 0.21/0.42  # Proof object clause steps            : 33
% 0.21/0.42  # Proof object formula steps           : 21
% 0.21/0.42  # Proof object conjectures             : 8
% 0.21/0.42  # Proof object clause conjectures      : 5
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 10
% 0.21/0.42  # Proof object initial formulas used   : 10
% 0.21/0.42  # Proof object generating inferences   : 12
% 0.21/0.42  # Proof object simplifying inferences  : 47
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 10
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 10
% 0.21/0.42  # Removed in clause preprocessing      : 4
% 0.21/0.42  # Initial clauses in saturation        : 6
% 0.21/0.42  # Processed clauses                    : 303
% 0.21/0.42  # ...of these trivial                  : 3
% 0.21/0.42  # ...subsumed                          : 228
% 0.21/0.42  # ...remaining for further processing  : 72
% 0.21/0.42  # Other redundant clauses eliminated   : 0
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 0
% 0.21/0.42  # Backward-rewritten                   : 2
% 0.21/0.42  # Generated clauses                    : 7160
% 0.21/0.42  # ...of the previous two non-trivial   : 6725
% 0.21/0.42  # Contextual simplify-reflections      : 0
% 0.21/0.42  # Paramodulations                      : 7160
% 0.21/0.42  # Factorizations                       : 0
% 0.21/0.42  # Equation resolutions                 : 0
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 64
% 0.21/0.42  #    Positive orientable unit clauses  : 5
% 0.21/0.42  #    Positive unorientable unit clauses: 59
% 0.21/0.42  #    Negative unit clauses             : 0
% 0.21/0.42  #    Non-unit-clauses                  : 0
% 0.21/0.42  # Current number of unprocessed clauses: 6434
% 0.21/0.42  # ...number of literals in the above   : 6434
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 12
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 0
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.42  # Unit Clause-clause subsumption calls : 1440
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 3208
% 0.21/0.42  # BW rewrite match successes           : 3208
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 36726
% 0.21/0.42  
% 0.21/0.42  # -------------------------------------------------
% 0.21/0.42  # User time                : 0.069 s
% 0.21/0.42  # System time              : 0.007 s
% 0.21/0.42  # Total time               : 0.077 s
% 0.21/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
