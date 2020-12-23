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
% DateTime   : Thu Dec  3 10:35:18 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   59 (2088 expanded)
%              Number of clauses        :   38 ( 903 expanded)
%              Number of leaves         :   10 ( 592 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 (2088 expanded)
%              Number of equality atoms :   58 (2087 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   15 (   5 average)

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

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(t60_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(c_0_10,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_11,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_xboole_0(k1_tarski(X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X27,X28,X29] : k1_enumset1(X27,X28,X29) = k2_xboole_0(k1_tarski(X27),k2_tarski(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,plain,(
    ! [X10,X11,X12] : k2_xboole_0(k2_xboole_0(X10,X11),X12) = k2_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X13,X14,X15] : k5_xboole_0(k5_xboole_0(X13,X14),X15) = k5_xboole_0(X13,k5_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_17]),c_0_20]),c_0_20])).

cnf(c_0_24,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_17]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_26,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))))) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24]),c_0_24]),c_0_24]),c_0_24])).

fof(c_0_28,plain,(
    ! [X30,X31,X32,X33] : k2_enumset1(X30,X31,X32,X33) = k2_xboole_0(k1_tarski(X30),k1_enumset1(X31,X32,X33)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))))) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,k5_xboole_0(X1,X2)),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,X2))))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))),k5_xboole_0(X1,X2))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_27]),c_0_24]),c_0_24])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(k5_xboole_0(X3,X4),X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),X2)))),X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_24]),c_0_24])).

fof(c_0_32,plain,(
    ! [X34,X35,X36,X37,X38] : k3_enumset1(X34,X35,X36,X37,X38) = k2_xboole_0(k2_enumset1(X34,X35,X36,X37),k1_tarski(X38)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(assume_negation,[status(cth)],[t60_enumset1])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))),X4))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_29]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3)))))))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X1,k5_xboole_0(X2,X3))))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_30]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),X2))))),X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)),X4))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_26]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_17])).

fof(c_0_41,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24] : k5_enumset1(X18,X19,X20,X21,X22,X23,X24) = k2_xboole_0(k2_enumset1(X18,X19,X20,X21),k1_enumset1(X22,X23,X24)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

fof(c_0_42,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_tarski(X3)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))))))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_29])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),X1),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_xboole_0(k1_tarski(X4),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),X1)))))))))) = k5_xboole_0(X1,k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_38])).

cnf(c_0_45,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_17]),c_0_40]),c_0_40])).

cnf(c_0_46,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_enumset1(X1,X2,X3)))) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))))))) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_24]),c_0_24])).

cnf(c_0_50,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k5_xboole_0(k1_enumset1(X5,X6,X7),k3_xboole_0(k1_enumset1(X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_17]),c_0_40]),c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k5_xboole_0(k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)))),k3_xboole_0(k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)))),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_17]),c_0_20]),c_0_20])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k5_xboole_0(X1,X2)),k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k5_xboole_0(k3_xboole_0(k1_tarski(X5),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k5_xboole_0(X1,X2))))))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_44]),c_0_24]),c_0_24])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_xboole_0(k1_tarski(X4),k1_enumset1(X1,X2,X3)),X5))) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_48]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),k5_xboole_0(k1_tarski(X5),k5_xboole_0(k3_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))),X6))))) = k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_49]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),k5_xboole_0(k1_enumset1(X5,X6,X7),k3_xboole_0(k1_enumset1(X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))))))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_24]),c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k5_xboole_0(k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)),k3_xboole_0(k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)))),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)))))) != k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_24]),c_0_24])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X7),k5_xboole_0(k3_xboole_0(k1_tarski(X7),k1_tarski(X6)),k3_xboole_0(k5_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X7),k3_xboole_0(k1_tarski(X7),k1_tarski(X6)))),k3_enumset1(X1,X2,X3,X4,X5)))))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_24]),c_0_53]),c_0_49]),c_0_24]),c_0_53]),c_0_54]),c_0_24]),c_0_53]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:07:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.52  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.52  #
% 0.18/0.52  # Preprocessing time       : 0.026 s
% 0.18/0.52  # Presaturation interreduction done
% 0.18/0.52  
% 0.18/0.52  # Proof found!
% 0.18/0.52  # SZS status Theorem
% 0.18/0.52  # SZS output start CNFRefutation
% 0.18/0.52  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.18/0.52  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.52  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.18/0.52  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.18/0.52  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.18/0.52  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.18/0.52  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.18/0.52  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.18/0.52  fof(t60_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 0.18/0.52  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 0.18/0.52  fof(c_0_10, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.18/0.52  fof(c_0_11, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.52  fof(c_0_12, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_xboole_0(k1_tarski(X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.18/0.52  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.52  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.52  fof(c_0_15, plain, ![X27, X28, X29]:k1_enumset1(X27,X28,X29)=k2_xboole_0(k1_tarski(X27),k2_tarski(X28,X29)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.18/0.52  cnf(c_0_16, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.52  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.52  fof(c_0_18, plain, ![X10, X11, X12]:k2_xboole_0(k2_xboole_0(X10,X11),X12)=k2_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.18/0.52  cnf(c_0_19, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.52  cnf(c_0_20, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.52  fof(c_0_21, plain, ![X13, X14, X15]:k5_xboole_0(k5_xboole_0(X13,X14),X15)=k5_xboole_0(X13,k5_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.18/0.52  cnf(c_0_22, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.52  cnf(c_0_23, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_17]), c_0_20]), c_0_20])).
% 0.18/0.52  cnf(c_0_24, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.52  cnf(c_0_25, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_17]), c_0_17]), c_0_17]), c_0_17])).
% 0.18/0.52  cnf(c_0_26, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1))))))=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_27, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.18/0.52  fof(c_0_28, plain, ![X30, X31, X32, X33]:k2_enumset1(X30,X31,X32,X33)=k2_xboole_0(k1_tarski(X30),k1_enumset1(X31,X32,X33)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.18/0.52  cnf(c_0_29, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))))=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.52  cnf(c_0_30, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,k5_xboole_0(X1,X2)),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,X2)))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))),k5_xboole_0(X1,X2)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_27]), c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_31, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(k5_xboole_0(X3,X4),X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),X2)))),X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_24]), c_0_24])).
% 0.18/0.52  fof(c_0_32, plain, ![X34, X35, X36, X37, X38]:k3_enumset1(X34,X35,X36,X37,X38)=k2_xboole_0(k2_enumset1(X34,X35,X36,X37),k1_tarski(X38)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.18/0.52  cnf(c_0_33, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.52  fof(c_0_34, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(assume_negation,[status(cth)],[t60_enumset1])).
% 0.18/0.52  cnf(c_0_35, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))),X4)))))=k5_xboole_0(k1_enumset1(X1,X2,X3),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_29]), c_0_24]), c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_36, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))))))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X1,k5_xboole_0(X2,X3)))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_30]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_37, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X4,X5)),X2))))),X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_38, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)),X4)))))=k5_xboole_0(k1_enumset1(X1,X2,X3),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_26]), c_0_24]), c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_39, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.52  cnf(c_0_40, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_33, c_0_17])).
% 0.18/0.52  fof(c_0_41, plain, ![X18, X19, X20, X21, X22, X23, X24]:k5_enumset1(X18,X19,X20,X21,X22,X23,X24)=k2_xboole_0(k2_enumset1(X18,X19,X20,X21),k1_enumset1(X22,X23,X24)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.18/0.52  fof(c_0_42, negated_conjecture, k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 0.18/0.52  cnf(c_0_43, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_tarski(X3)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))))))=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_29])).
% 0.18/0.52  cnf(c_0_44, plain, (k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),X1),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_xboole_0(k1_tarski(X4),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(X1,k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),X1))))))))))=k5_xboole_0(X1,k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_38])).
% 0.18/0.52  cnf(c_0_45, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_17]), c_0_40]), c_0_40])).
% 0.18/0.52  cnf(c_0_46, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.52  cnf(c_0_47, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.52  cnf(c_0_48, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_enumset1(X1,X2,X3))))=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.52  cnf(c_0_49, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))))))))=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_50, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k5_xboole_0(k1_enumset1(X5,X6,X7),k3_xboole_0(k1_enumset1(X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_17]), c_0_40]), c_0_40])).
% 0.18/0.52  cnf(c_0_51, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k5_xboole_0(k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)))),k3_xboole_0(k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)))),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_17]), c_0_20]), c_0_20])).
% 0.18/0.52  cnf(c_0_52, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k5_xboole_0(X1,X2)),k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k5_xboole_0(k3_xboole_0(k1_tarski(X5),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k5_xboole_0(X1,X2)))))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(X1,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_44]), c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_53, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_tarski(X4),k5_xboole_0(k3_xboole_0(k1_tarski(X4),k1_enumset1(X1,X2,X3)),X5)))=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_48]), c_0_24]), c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_54, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),k5_xboole_0(k1_tarski(X5),k5_xboole_0(k3_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))),X6)))))=k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_49]), c_0_24]), c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_55, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k5_xboole_0(k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)),k5_xboole_0(k1_enumset1(X5,X6,X7),k3_xboole_0(k1_enumset1(X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))))))))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_56, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k5_xboole_0(k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)),k3_xboole_0(k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)))),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0))))))!=k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_24]), c_0_24])).
% 0.18/0.52  cnf(c_0_57, plain, (k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X7),k5_xboole_0(k3_xboole_0(k1_tarski(X7),k1_tarski(X6)),k3_xboole_0(k5_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X7),k3_xboole_0(k1_tarski(X7),k1_tarski(X6)))),k3_enumset1(X1,X2,X3,X4,X5))))))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_48]), c_0_24]), c_0_53]), c_0_49]), c_0_24]), c_0_53]), c_0_54]), c_0_24]), c_0_53]), c_0_55])).
% 0.18/0.52  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])]), ['proof']).
% 0.18/0.52  # SZS output end CNFRefutation
% 0.18/0.52  # Proof object total steps             : 59
% 0.18/0.52  # Proof object clause steps            : 38
% 0.18/0.52  # Proof object formula steps           : 21
% 0.18/0.52  # Proof object conjectures             : 7
% 0.18/0.52  # Proof object clause conjectures      : 4
% 0.18/0.52  # Proof object formula conjectures     : 3
% 0.18/0.52  # Proof object initial clauses used    : 10
% 0.18/0.52  # Proof object initial formulas used   : 10
% 0.18/0.52  # Proof object generating inferences   : 14
% 0.18/0.52  # Proof object simplifying inferences  : 70
% 0.18/0.52  # Training examples: 0 positive, 0 negative
% 0.18/0.52  # Parsed axioms                        : 10
% 0.18/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.52  # Initial clauses                      : 10
% 0.18/0.52  # Removed in clause preprocessing      : 4
% 0.18/0.52  # Initial clauses in saturation        : 6
% 0.18/0.52  # Processed clauses                    : 125
% 0.18/0.52  # ...of these trivial                  : 9
% 0.18/0.52  # ...subsumed                          : 66
% 0.18/0.52  # ...remaining for further processing  : 50
% 0.18/0.52  # Other redundant clauses eliminated   : 0
% 0.18/0.52  # Clauses deleted for lack of memory   : 0
% 0.18/0.52  # Backward-subsumed                    : 0
% 0.18/0.52  # Backward-rewritten                   : 3
% 0.18/0.52  # Generated clauses                    : 3819
% 0.18/0.52  # ...of the previous two non-trivial   : 3702
% 0.18/0.52  # Contextual simplify-reflections      : 0
% 0.18/0.52  # Paramodulations                      : 3819
% 0.18/0.52  # Factorizations                       : 0
% 0.18/0.52  # Equation resolutions                 : 0
% 0.18/0.52  # Propositional unsat checks           : 0
% 0.18/0.52  #    Propositional check models        : 0
% 0.18/0.52  #    Propositional check unsatisfiable : 0
% 0.18/0.52  #    Propositional clauses             : 0
% 0.18/0.52  #    Propositional clauses after purity: 0
% 0.18/0.52  #    Propositional unsat core size     : 0
% 0.18/0.52  #    Propositional preprocessing time  : 0.000
% 0.18/0.52  #    Propositional encoding time       : 0.000
% 0.18/0.52  #    Propositional solver time         : 0.000
% 0.18/0.52  #    Success case prop preproc time    : 0.000
% 0.18/0.52  #    Success case prop encoding time   : 0.000
% 0.18/0.52  #    Success case prop solver time     : 0.000
% 0.18/0.52  # Current number of processed clauses  : 41
% 0.18/0.52  #    Positive orientable unit clauses  : 25
% 0.18/0.52  #    Positive unorientable unit clauses: 16
% 0.18/0.52  #    Negative unit clauses             : 0
% 0.18/0.52  #    Non-unit-clauses                  : 0
% 0.18/0.52  # Current number of unprocessed clauses: 3589
% 0.18/0.52  # ...number of literals in the above   : 3589
% 0.18/0.52  # Current number of archived formulas  : 0
% 0.18/0.52  # Current number of archived clauses   : 13
% 0.18/0.52  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.52  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.52  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.52  # Unit Clause-clause subsumption calls : 16
% 0.18/0.52  # Rewrite failures with RHS unbound    : 0
% 0.18/0.52  # BW rewrite match attempts            : 2039
% 0.18/0.52  # BW rewrite match successes           : 9
% 0.18/0.52  # Condensation attempts                : 0
% 0.18/0.52  # Condensation successes               : 0
% 0.18/0.52  # Termbank termtop insertions          : 411984
% 0.18/0.52  
% 0.18/0.52  # -------------------------------------------------
% 0.18/0.52  # User time                : 0.173 s
% 0.18/0.52  # System time              : 0.010 s
% 0.18/0.52  # Total time               : 0.184 s
% 0.18/0.52  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
