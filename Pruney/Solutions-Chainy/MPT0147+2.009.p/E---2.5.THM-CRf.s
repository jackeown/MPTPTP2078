%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 716 expanded)
%              Number of clauses        :   34 ( 309 expanded)
%              Number of leaves         :   11 ( 203 expanded)
%              Depth                    :   11
%              Number of atoms          :   57 ( 716 expanded)
%              Number of equality atoms :   56 ( 715 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t113_xboole_1,axiom,(
    ! [X1,X2,X3,X4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(t63_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(c_0_11,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k5_xboole_0(X21,k4_xboole_0(X22,X21)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X23,X24] : k2_tarski(X23,X24) = k2_xboole_0(k1_tarski(X23),k1_tarski(X24)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X25,X26,X27] : k1_enumset1(X25,X26,X27) = k2_xboole_0(k1_tarski(X25),k2_tarski(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X15,X16,X17] : k2_xboole_0(k2_xboole_0(X15,X16),X17) = k2_xboole_0(X15,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] : k5_xboole_0(k5_xboole_0(X18,X19),X20) = k5_xboole_0(X18,k5_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_21]),c_0_21])).

cnf(c_0_25,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_18]),c_0_18]),c_0_18])).

fof(c_0_27,plain,(
    ! [X11,X12,X13,X14] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X11,X12),X13),X14) = k2_xboole_0(X11,k2_xboole_0(k2_xboole_0(X12,X13),X14)) ),
    inference(variable_rename,[status(thm)],[t113_xboole_1])).

fof(c_0_28,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k5_enumset1(X34,X35,X36,X37,X38,X39,X40) = k2_xboole_0(k2_tarski(X34,X35),k3_enumset1(X36,X37,X38,X39,X40)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(assume_negation,[status(cth)],[t63_enumset1])).

fof(c_0_30,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k4_enumset1(X28,X29,X30,X31,X32,X33) = k2_xboole_0(k1_tarski(X28),k3_enumset1(X29,X30,X31,X32,X33)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_31,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48] : k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) = k2_xboole_0(k1_tarski(X41),k5_enumset1(X42,X43,X44,X45,X46,X47,X48)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))))) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k4_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))))) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))),X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_18]),c_0_18]),c_0_18]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_18]),c_0_21]),c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k4_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_18])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_18])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,k5_xboole_0(X1,X2)),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,X2))))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))),k5_xboole_0(X1,X2))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_33]),c_0_25]),c_0_25])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))),X4))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_39]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))))),X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_25]),c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))) != k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))),k5_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk3_0)))),k3_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk3_0)))),k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_18]),c_0_21]),c_0_21]),c_0_43]),c_0_43]),c_0_44])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3)))))))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X1,k5_xboole_0(X2,X3))))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_45]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))))))),k1_tarski(X1)))))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_39])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))),X8))))) = k5_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),X8) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_48]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k5_xboole_0(k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)),k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k5_xboole_0(k3_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk3_0)),k3_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk3_0)))),k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0))))))))))) != k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_tarski(X3)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_50]),c_0_39])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k1_enumset1(X1,X2,X3)))) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.55  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.55  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.55  #
% 0.19/0.55  # Preprocessing time       : 0.049 s
% 0.19/0.55  # Presaturation interreduction done
% 0.19/0.55  
% 0.19/0.55  # Proof found!
% 0.19/0.55  # SZS status Theorem
% 0.19/0.55  # SZS output start CNFRefutation
% 0.19/0.55  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.55  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.55  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.19/0.55  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.19/0.55  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.19/0.55  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.55  fof(t113_xboole_1, axiom, ![X1, X2, X3, X4]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_xboole_1)).
% 0.19/0.55  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 0.19/0.55  fof(t63_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 0.19/0.55  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.19/0.55  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 0.19/0.55  fof(c_0_11, plain, ![X21, X22]:k2_xboole_0(X21,X22)=k5_xboole_0(X21,k4_xboole_0(X22,X21)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.55  fof(c_0_12, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.55  fof(c_0_13, plain, ![X23, X24]:k2_tarski(X23,X24)=k2_xboole_0(k1_tarski(X23),k1_tarski(X24)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.19/0.55  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.55  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.55  fof(c_0_16, plain, ![X25, X26, X27]:k1_enumset1(X25,X26,X27)=k2_xboole_0(k1_tarski(X25),k2_tarski(X26,X27)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.19/0.55  cnf(c_0_17, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.55  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.55  fof(c_0_19, plain, ![X15, X16, X17]:k2_xboole_0(k2_xboole_0(X15,X16),X17)=k2_xboole_0(X15,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.19/0.55  cnf(c_0_20, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.55  cnf(c_0_21, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.55  fof(c_0_22, plain, ![X18, X19, X20]:k5_xboole_0(k5_xboole_0(X18,X19),X20)=k5_xboole_0(X18,k5_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.55  cnf(c_0_23, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.55  cnf(c_0_24, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_21]), c_0_21])).
% 0.19/0.55  cnf(c_0_25, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.55  cnf(c_0_26, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 0.19/0.55  fof(c_0_27, plain, ![X11, X12, X13, X14]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X11,X12),X13),X14)=k2_xboole_0(X11,k2_xboole_0(k2_xboole_0(X12,X13),X14)), inference(variable_rename,[status(thm)],[t113_xboole_1])).
% 0.19/0.55  fof(c_0_28, plain, ![X34, X35, X36, X37, X38, X39, X40]:k5_enumset1(X34,X35,X36,X37,X38,X39,X40)=k2_xboole_0(k2_tarski(X34,X35),k3_enumset1(X36,X37,X38,X39,X40)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 0.19/0.55  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(assume_negation,[status(cth)],[t63_enumset1])).
% 0.19/0.55  fof(c_0_30, plain, ![X28, X29, X30, X31, X32, X33]:k4_enumset1(X28,X29,X30,X31,X32,X33)=k2_xboole_0(k1_tarski(X28),k3_enumset1(X29,X30,X31,X32,X33)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.19/0.55  fof(c_0_31, plain, ![X41, X42, X43, X44, X45, X46, X47, X48]:k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48)=k2_xboole_0(k1_tarski(X41),k5_enumset1(X42,X43,X44,X45,X46,X47,X48)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.19/0.55  cnf(c_0_32, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1))))))=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25])).
% 0.19/0.55  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.19/0.55  cnf(c_0_34, plain, (k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.55  cnf(c_0_35, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.55  fof(c_0_36, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k4_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.19/0.55  cnf(c_0_37, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.55  cnf(c_0_38, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.55  cnf(c_0_39, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))))=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.55  cnf(c_0_40, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))))=k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))),X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_18]), c_0_18]), c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 0.19/0.55  cnf(c_0_41, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_18]), c_0_21]), c_0_21])).
% 0.19/0.55  cnf(c_0_42, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k4_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.55  cnf(c_0_43, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_37, c_0_18])).
% 0.19/0.55  cnf(c_0_44, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_38, c_0_18])).
% 0.19/0.55  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,k5_xboole_0(X1,X2)),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,X2)))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))),k5_xboole_0(X1,X2)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_33]), c_0_25]), c_0_25])).
% 0.19/0.55  cnf(c_0_46, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))),X4)))))=k5_xboole_0(k1_enumset1(X1,X2,X3),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_39]), c_0_25]), c_0_25]), c_0_25])).
% 0.19/0.55  cnf(c_0_47, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))))),X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.19/0.55  cnf(c_0_48, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_25]), c_0_25])).
% 0.19/0.55  cnf(c_0_49, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))))!=k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))),k5_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk3_0)))),k3_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk3_0)))),k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_18]), c_0_21]), c_0_21]), c_0_43]), c_0_43]), c_0_44])).
% 0.19/0.55  cnf(c_0_50, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))))))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X1,k5_xboole_0(X2,X3)))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_45]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.19/0.55  cnf(c_0_51, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))))))),k1_tarski(X1))))))))=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_39])).
% 0.19/0.55  cnf(c_0_52, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))),X8)))))=k5_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),X8)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_48]), c_0_25]), c_0_25]), c_0_25])).
% 0.19/0.55  cnf(c_0_53, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k5_xboole_0(k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)),k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k5_xboole_0(k3_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk3_0)),k3_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk3_0)))),k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))))))))))!=k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.19/0.55  cnf(c_0_54, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_tarski(X3)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))))))=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_50]), c_0_39])).
% 0.19/0.55  cnf(c_0_55, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k1_enumset1(X1,X2,X3))))=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_48]), c_0_52])).
% 0.19/0.55  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_55])]), ['proof']).
% 0.19/0.55  # SZS output end CNFRefutation
% 0.19/0.55  # Proof object total steps             : 57
% 0.19/0.55  # Proof object clause steps            : 34
% 0.19/0.55  # Proof object formula steps           : 23
% 0.19/0.55  # Proof object conjectures             : 7
% 0.19/0.55  # Proof object clause conjectures      : 4
% 0.19/0.55  # Proof object formula conjectures     : 3
% 0.19/0.55  # Proof object initial clauses used    : 11
% 0.19/0.55  # Proof object initial formulas used   : 11
% 0.19/0.55  # Proof object generating inferences   : 8
% 0.19/0.55  # Proof object simplifying inferences  : 73
% 0.19/0.55  # Training examples: 0 positive, 0 negative
% 0.19/0.55  # Parsed axioms                        : 11
% 0.19/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.55  # Initial clauses                      : 11
% 0.19/0.55  # Removed in clause preprocessing      : 5
% 0.19/0.55  # Initial clauses in saturation        : 6
% 0.19/0.55  # Processed clauses                    : 96
% 0.19/0.55  # ...of these trivial                  : 7
% 0.19/0.55  # ...subsumed                          : 42
% 0.19/0.55  # ...remaining for further processing  : 47
% 0.19/0.55  # Other redundant clauses eliminated   : 0
% 0.19/0.55  # Clauses deleted for lack of memory   : 0
% 0.19/0.55  # Backward-subsumed                    : 0
% 0.19/0.55  # Backward-rewritten                   : 1
% 0.19/0.55  # Generated clauses                    : 2707
% 0.19/0.55  # ...of the previous two non-trivial   : 2635
% 0.19/0.55  # Contextual simplify-reflections      : 0
% 0.19/0.55  # Paramodulations                      : 2707
% 0.19/0.55  # Factorizations                       : 0
% 0.19/0.55  # Equation resolutions                 : 0
% 0.19/0.55  # Propositional unsat checks           : 0
% 0.19/0.55  #    Propositional check models        : 0
% 0.19/0.55  #    Propositional check unsatisfiable : 0
% 0.19/0.55  #    Propositional clauses             : 0
% 0.19/0.55  #    Propositional clauses after purity: 0
% 0.19/0.55  #    Propositional unsat core size     : 0
% 0.19/0.55  #    Propositional preprocessing time  : 0.000
% 0.19/0.55  #    Propositional encoding time       : 0.000
% 0.19/0.55  #    Propositional solver time         : 0.000
% 0.19/0.55  #    Success case prop preproc time    : 0.000
% 0.19/0.55  #    Success case prop encoding time   : 0.000
% 0.19/0.55  #    Success case prop solver time     : 0.000
% 0.19/0.55  # Current number of processed clauses  : 40
% 0.19/0.55  #    Positive orientable unit clauses  : 26
% 0.19/0.55  #    Positive unorientable unit clauses: 14
% 0.19/0.55  #    Negative unit clauses             : 0
% 0.19/0.55  #    Non-unit-clauses                  : 0
% 0.19/0.55  # Current number of unprocessed clauses: 2551
% 0.19/0.55  # ...number of literals in the above   : 2551
% 0.19/0.55  # Current number of archived formulas  : 0
% 0.19/0.55  # Current number of archived clauses   : 12
% 0.19/0.55  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.55  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.55  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.55  # Unit Clause-clause subsumption calls : 21
% 0.19/0.55  # Rewrite failures with RHS unbound    : 0
% 0.19/0.55  # BW rewrite match attempts            : 1700
% 0.19/0.55  # BW rewrite match successes           : 8
% 0.19/0.55  # Condensation attempts                : 0
% 0.19/0.55  # Condensation successes               : 0
% 0.19/0.55  # Termbank termtop insertions          : 294285
% 0.19/0.55  
% 0.19/0.55  # -------------------------------------------------
% 0.19/0.55  # User time                : 0.195 s
% 0.19/0.55  # System time              : 0.011 s
% 0.19/0.55  # Total time               : 0.206 s
% 0.19/0.55  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
