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
% DateTime   : Thu Dec  3 10:35:25 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   70 (2506 expanded)
%              Number of clauses        :   47 (1085 expanded)
%              Number of leaves         :   11 ( 710 expanded)
%              Depth                    :   15
%              Number of atoms          :   70 (2506 expanded)
%              Number of equality atoms :   69 (2505 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(t66_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(c_0_11,plain,(
    ! [X17,X18] : k2_xboole_0(X17,X18) = k5_xboole_0(X17,k4_xboole_0(X18,X17)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X27,X28] : k2_tarski(X27,X28) = k2_xboole_0(k1_tarski(X27),k1_tarski(X28)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X29,X30,X31] : k1_enumset1(X29,X30,X31) = k2_xboole_0(k1_tarski(X29),k2_tarski(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X11,X12,X13] : k2_xboole_0(k2_xboole_0(X11,X12),X13) = k2_xboole_0(X11,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X14,X15,X16] : k5_xboole_0(k5_xboole_0(X14,X15),X16) = k5_xboole_0(X14,k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X32,X33,X34,X35] : k2_enumset1(X32,X33,X34,X35) = k2_xboole_0(k1_tarski(X32),k1_enumset1(X33,X34,X35)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_21]),c_0_21])).

cnf(c_0_26,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_18]),c_0_18]),c_0_18])).

fof(c_0_28,plain,(
    ! [X36,X37,X38,X39,X40] : k3_enumset1(X36,X37,X38,X39,X40) = k2_xboole_0(k1_tarski(X36),k2_enumset1(X37,X38,X39,X40)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))))) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))))) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,k5_xboole_0(X1,X2)),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,X2))))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))),k5_xboole_0(X1,X2))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_31]),c_0_26]),c_0_26])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_18]),c_0_33]),c_0_33])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))),X4))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_34]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3)))))))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X1,k5_xboole_0(X2,X3))))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_35]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(k5_xboole_0(X3,X4),X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),X2)))),X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1)))))) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_26]),c_0_26])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_tarski(X3)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_34])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),X2))))),X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_26]),c_0_26]),c_0_26])).

fof(c_0_43,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48] : k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) = k2_xboole_0(k1_tarski(X41),k5_enumset1(X42,X43,X44,X45,X46,X47,X48)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(assume_negation,[status(cth)],[t66_enumset1])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))))) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(spm,[status(thm)],[c_0_31,c_0_40])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k1_tarski(X3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_tarski(X3)))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_tarski(X3)))),k1_tarski(X2)))))),k1_tarski(X1)))))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_enumset1(X1,X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1)),X6))))) = k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_40]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)),X4))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_30]),c_0_26]),c_0_26]),c_0_26])).

fof(c_0_49,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] : k6_enumset1(X19,X20,X21,X22,X23,X24,X25,X26) = k2_xboole_0(k2_enumset1(X19,X20,X21,X22),k2_enumset1(X23,X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_enumset1(esk6_0,esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k3_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))),X6))))) = k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_45]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_47])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),X1),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_xboole_0(k1_tarski(X4),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),X1)))))))))) = k5_xboole_0(X1,k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_30]),c_0_48])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_50,c_0_18])).

cnf(c_0_57,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_enumset1(esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(X6,k3_xboole_0(X6,k1_enumset1(X3,X4,X5)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))))))) = k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(X6,k3_xboole_0(X6,k3_enumset1(X1,X2,X3,X4,X5)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_38]),c_0_45])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)),X7))) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k5_xboole_0(k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)),X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_53]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_60,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_enumset1(X1,X2,X3)))) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_54])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_18]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))) != k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k5_xboole_0(k1_enumset1(esk6_0,esk7_0,esk8_0),k3_xboole_0(k1_enumset1(esk6_0,esk7_0,esk8_0),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_18]),c_0_56])).

cnf(c_0_63,plain,
    ( k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k3_enumset1(X1,X2,X3,X4,X5)))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_53]),c_0_59]),c_0_41])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_xboole_0(k1_tarski(X4),k1_enumset1(X1,X2,X3)),X5))) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_60]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),X1),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)))),k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),X1)))))))))) = k5_xboole_0(X1,k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_47])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k5_xboole_0(k3_xboole_0(k1_enumset1(X6,X7,X8),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))))))))) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k5_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk1_0,esk2_0,esk3_0)))) != k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k1_enumset1(X1,X2,X3)))) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_60]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.39/0.58  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.39/0.58  #
% 0.39/0.58  # Preprocessing time       : 0.026 s
% 0.39/0.58  # Presaturation interreduction done
% 0.39/0.58  
% 0.39/0.58  # Proof found!
% 0.39/0.58  # SZS status Theorem
% 0.39/0.58  # SZS output start CNFRefutation
% 0.39/0.58  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.39/0.58  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.39/0.58  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.39/0.58  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.39/0.58  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.39/0.58  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.39/0.58  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.39/0.58  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.39/0.58  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 0.39/0.58  fof(t66_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 0.39/0.58  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 0.39/0.58  fof(c_0_11, plain, ![X17, X18]:k2_xboole_0(X17,X18)=k5_xboole_0(X17,k4_xboole_0(X18,X17)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.39/0.58  fof(c_0_12, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.39/0.58  fof(c_0_13, plain, ![X27, X28]:k2_tarski(X27,X28)=k2_xboole_0(k1_tarski(X27),k1_tarski(X28)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.39/0.58  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.39/0.58  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.39/0.58  fof(c_0_16, plain, ![X29, X30, X31]:k1_enumset1(X29,X30,X31)=k2_xboole_0(k1_tarski(X29),k2_tarski(X30,X31)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.39/0.58  cnf(c_0_17, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.58  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.39/0.58  fof(c_0_19, plain, ![X11, X12, X13]:k2_xboole_0(k2_xboole_0(X11,X12),X13)=k2_xboole_0(X11,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.39/0.58  cnf(c_0_20, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.39/0.58  cnf(c_0_21, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.39/0.58  fof(c_0_22, plain, ![X14, X15, X16]:k5_xboole_0(k5_xboole_0(X14,X15),X16)=k5_xboole_0(X14,k5_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.39/0.58  cnf(c_0_23, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.58  fof(c_0_24, plain, ![X32, X33, X34, X35]:k2_enumset1(X32,X33,X34,X35)=k2_xboole_0(k1_tarski(X32),k1_enumset1(X33,X34,X35)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.39/0.58  cnf(c_0_25, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_21]), c_0_21])).
% 0.39/0.58  cnf(c_0_26, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.58  cnf(c_0_27, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 0.39/0.58  fof(c_0_28, plain, ![X36, X37, X38, X39, X40]:k3_enumset1(X36,X37,X38,X39,X40)=k2_xboole_0(k1_tarski(X36),k2_enumset1(X37,X38,X39,X40)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.39/0.58  cnf(c_0_29, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.39/0.58  cnf(c_0_30, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1))))))=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_31, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_32, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.39/0.58  cnf(c_0_33, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_29, c_0_18])).
% 0.39/0.58  cnf(c_0_34, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))))=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.39/0.58  cnf(c_0_35, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,k5_xboole_0(X1,X2)),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,X2)))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))),k5_xboole_0(X1,X2)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_31]), c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_36, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_18]), c_0_33]), c_0_33])).
% 0.39/0.58  cnf(c_0_37, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))),X4)))))=k5_xboole_0(k1_enumset1(X1,X2,X3),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_34]), c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))))))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X1,k5_xboole_0(X2,X3)))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_35]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_39, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(k5_xboole_0(X3,X4),X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),X2)))),X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_40, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1))))))=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_41, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_tarski(X3)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))))))=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_34])).
% 0.39/0.58  cnf(c_0_42, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),X2))))),X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  fof(c_0_43, plain, ![X41, X42, X43, X44, X45, X46, X47, X48]:k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48)=k2_xboole_0(k1_tarski(X41),k5_enumset1(X42,X43,X44,X45,X46,X47,X48)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.39/0.58  fof(c_0_44, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))), inference(assume_negation,[status(cth)],[t66_enumset1])).
% 0.39/0.58  cnf(c_0_45, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))))=k3_enumset1(X1,X2,X3,X4,X5)), inference(spm,[status(thm)],[c_0_31, c_0_40])).
% 0.39/0.58  cnf(c_0_46, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k1_tarski(X3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_tarski(X3)))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_tarski(X3)))),k1_tarski(X2)))))),k1_tarski(X1))))))))=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_enumset1(X1,X2,X3))))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.39/0.58  cnf(c_0_47, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1)),X6)))))=k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_40]), c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_48, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)),X4)))))=k5_xboole_0(k1_enumset1(X1,X2,X3),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_30]), c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  fof(c_0_49, plain, ![X19, X20, X21, X22, X23, X24, X25, X26]:k6_enumset1(X19,X20,X21,X22,X23,X24,X25,X26)=k2_xboole_0(k2_enumset1(X19,X20,X21,X22),k2_enumset1(X23,X24,X25,X26)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.39/0.58  cnf(c_0_50, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.39/0.58  fof(c_0_51, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_enumset1(esk6_0,esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).
% 0.39/0.58  cnf(c_0_52, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k3_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))),X6)))))=k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_45]), c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_53, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_47])).
% 0.39/0.58  cnf(c_0_54, plain, (k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),X1),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_xboole_0(k1_tarski(X4),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),X1))))))))))=k5_xboole_0(X1,k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_30]), c_0_48])).
% 0.39/0.58  cnf(c_0_55, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.39/0.58  cnf(c_0_56, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_50, c_0_18])).
% 0.39/0.58  cnf(c_0_57, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_enumset1(esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.39/0.58  cnf(c_0_58, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(X6,k3_xboole_0(X6,k1_enumset1(X3,X4,X5)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))))))=k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(X6,k3_xboole_0(X6,k3_enumset1(X1,X2,X3,X4,X5))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_38]), c_0_45])).
% 0.39/0.58  cnf(c_0_59, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)),X7)))=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k5_xboole_0(k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)),X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_53]), c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_60, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_enumset1(X1,X2,X3))))=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))), inference(spm,[status(thm)],[c_0_41, c_0_54])).
% 0.39/0.58  cnf(c_0_61, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))))=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_18]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_56])).
% 0.39/0.58  cnf(c_0_62, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))))!=k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k5_xboole_0(k1_enumset1(esk6_0,esk7_0,esk8_0),k3_xboole_0(k1_enumset1(esk6_0,esk7_0,esk8_0),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_18]), c_0_56])).
% 0.39/0.58  cnf(c_0_63, plain, (k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k3_enumset1(X1,X2,X3,X4,X5))))=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_53]), c_0_59]), c_0_41])).
% 0.39/0.58  cnf(c_0_64, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_xboole_0(k1_tarski(X4),k1_enumset1(X1,X2,X3)),X5)))=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_60]), c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_65, plain, (k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),X1),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)))),k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),X1))))))))))=k5_xboole_0(X1,k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_40]), c_0_47])).
% 0.39/0.58  cnf(c_0_66, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k5_xboole_0(k3_xboole_0(k1_enumset1(X6,X7,X8),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))))))))))=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.39/0.58  cnf(c_0_67, negated_conjecture, (k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k5_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk1_0,esk2_0,esk3_0))))!=k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k3_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.39/0.58  cnf(c_0_68, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k1_enumset1(X1,X2,X3))))=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_60]), c_0_66])).
% 0.39/0.58  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])]), ['proof']).
% 0.39/0.58  # SZS output end CNFRefutation
% 0.39/0.58  # Proof object total steps             : 70
% 0.39/0.58  # Proof object clause steps            : 47
% 0.39/0.58  # Proof object formula steps           : 23
% 0.39/0.58  # Proof object conjectures             : 7
% 0.39/0.58  # Proof object clause conjectures      : 4
% 0.39/0.58  # Proof object formula conjectures     : 3
% 0.39/0.58  # Proof object initial clauses used    : 11
% 0.39/0.58  # Proof object initial formulas used   : 11
% 0.39/0.58  # Proof object generating inferences   : 21
% 0.39/0.58  # Proof object simplifying inferences  : 76
% 0.39/0.58  # Training examples: 0 positive, 0 negative
% 0.39/0.58  # Parsed axioms                        : 11
% 0.39/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.58  # Initial clauses                      : 11
% 0.39/0.58  # Removed in clause preprocessing      : 5
% 0.39/0.58  # Initial clauses in saturation        : 6
% 0.39/0.58  # Processed clauses                    : 153
% 0.39/0.58  # ...of these trivial                  : 11
% 0.39/0.58  # ...subsumed                          : 82
% 0.39/0.58  # ...remaining for further processing  : 60
% 0.39/0.58  # Other redundant clauses eliminated   : 0
% 0.39/0.58  # Clauses deleted for lack of memory   : 0
% 0.39/0.58  # Backward-subsumed                    : 0
% 0.39/0.58  # Backward-rewritten                   : 3
% 0.39/0.58  # Generated clauses                    : 4157
% 0.39/0.58  # ...of the previous two non-trivial   : 4040
% 0.39/0.58  # Contextual simplify-reflections      : 0
% 0.39/0.58  # Paramodulations                      : 4157
% 0.39/0.58  # Factorizations                       : 0
% 0.39/0.58  # Equation resolutions                 : 0
% 0.39/0.58  # Propositional unsat checks           : 0
% 0.39/0.58  #    Propositional check models        : 0
% 0.39/0.58  #    Propositional check unsatisfiable : 0
% 0.39/0.58  #    Propositional clauses             : 0
% 0.39/0.58  #    Propositional clauses after purity: 0
% 0.39/0.58  #    Propositional unsat core size     : 0
% 0.39/0.58  #    Propositional preprocessing time  : 0.000
% 0.39/0.58  #    Propositional encoding time       : 0.000
% 0.39/0.58  #    Propositional solver time         : 0.000
% 0.39/0.58  #    Success case prop preproc time    : 0.000
% 0.39/0.58  #    Success case prop encoding time   : 0.000
% 0.39/0.58  #    Success case prop solver time     : 0.000
% 0.39/0.58  # Current number of processed clauses  : 51
% 0.39/0.58  #    Positive orientable unit clauses  : 33
% 0.39/0.58  #    Positive unorientable unit clauses: 18
% 0.39/0.58  #    Negative unit clauses             : 0
% 0.39/0.58  #    Non-unit-clauses                  : 0
% 0.39/0.58  # Current number of unprocessed clauses: 3898
% 0.39/0.58  # ...number of literals in the above   : 3898
% 0.39/0.58  # Current number of archived formulas  : 0
% 0.39/0.58  # Current number of archived clauses   : 14
% 0.39/0.58  # Clause-clause subsumption calls (NU) : 0
% 0.39/0.58  # Rec. Clause-clause subsumption calls : 0
% 0.39/0.58  # Non-unit clause-clause subsumptions  : 0
% 0.39/0.58  # Unit Clause-clause subsumption calls : 15
% 0.39/0.58  # Rewrite failures with RHS unbound    : 0
% 0.39/0.58  # BW rewrite match attempts            : 2123
% 0.39/0.58  # BW rewrite match successes           : 11
% 0.39/0.58  # Condensation attempts                : 0
% 0.39/0.58  # Condensation successes               : 0
% 0.39/0.58  # Termbank termtop insertions          : 442258
% 0.39/0.58  
% 0.39/0.58  # -------------------------------------------------
% 0.39/0.58  # User time                : 0.228 s
% 0.39/0.58  # System time              : 0.015 s
% 0.39/0.58  # Total time               : 0.243 s
% 0.39/0.58  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
