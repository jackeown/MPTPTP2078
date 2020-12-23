%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:32 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   94 (50954 expanded)
%              Number of clauses        :   63 (22515 expanded)
%              Number of leaves         :   15 (14219 expanded)
%              Depth                    :   22
%              Number of atoms          :   94 (50954 expanded)
%              Number of equality atoms :   93 (50953 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t70_enumset1,conjecture,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(c_0_15,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_20,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X20) = k5_xboole_0(X19,k4_xboole_0(X20,X19)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_21,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_22,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

fof(c_0_23,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_22])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_18])).

fof(c_0_30,plain,(
    ! [X16,X17,X18] : k5_xboole_0(k5_xboole_0(X16,X17),X18) = k5_xboole_0(X16,k5_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_25]),c_0_18])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k3_xboole_0(X12,X13)) = X12 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_33])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_38,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_25]),c_0_18])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_31,c_0_42])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_34])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_42])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_46])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_44,c_0_46])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X2,k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50])).

fof(c_0_53,plain,(
    ! [X27,X28,X29] : k1_enumset1(X27,X28,X29) = k2_xboole_0(k1_tarski(X27),k2_tarski(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_54,plain,(
    ! [X34] : k2_tarski(X34,X34) = k1_tarski(X34) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_55,plain,(
    ! [X21,X22,X23,X24] : k2_enumset1(X21,X22,X23,X24) = k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X24)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_57,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_xboole_0(k1_tarski(X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_58,plain,(
    ! [X30,X31,X32,X33] : k2_enumset1(X30,X31,X32,X33) = k2_xboole_0(k1_tarski(X30),k1_enumset1(X31,X32,X33)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_59,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_52,c_0_56])).

cnf(c_0_63,plain,
    ( k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50])).

cnf(c_0_64,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_25]),c_0_18])).

cnf(c_0_67,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_25]),c_0_18])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_49])).

cnf(c_0_69,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_60]),c_0_60]),c_0_25]),c_0_18])).

cnf(c_0_70,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_60]),c_0_25]),c_0_18]),c_0_66]),c_0_66]),c_0_67])).

fof(c_0_71,negated_conjecture,(
    ~ ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t70_enumset1])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1))) = k5_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_34])).

cnf(c_0_73,plain,
    ( k5_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2)) = k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_69])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X1,X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_34]),c_0_34])).

cnf(c_0_75,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_41])).

fof(c_0_76,negated_conjecture,(
    k1_enumset1(esk1_0,esk1_0,esk2_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_71])])])).

cnf(c_0_77,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(X3,k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))))) = k5_xboole_0(X3,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X2)))) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_28]),c_0_33]),c_0_47])).

cnf(c_0_79,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),X3) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)),X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_69]),c_0_34])).

cnf(c_0_80,plain,
    ( k5_xboole_0(k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)),k2_tarski(X1,X2)) = k5_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( k1_enumset1(esk1_0,esk1_0,esk2_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,plain,
    ( k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_62]),c_0_50])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k2_tarski(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_62]),c_0_50])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_68])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk2_0),k2_tarski(esk1_0,esk1_0)))) != k2_tarski(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_66])).

cnf(c_0_86,plain,
    ( k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X1)) = k2_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_82]),c_0_49])).

cnf(c_0_87,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_83]),c_0_49])).

cnf(c_0_88,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk2_0)))) != k2_tarski(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_41])).

cnf(c_0_90,plain,
    ( k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2)) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k2_tarski(X2,X3)) = k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X3,X3),k2_tarski(X2,X2)),X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_69]),c_0_34])).

cnf(c_0_92,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X2,X1),X3)) = X3 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_83]),c_0_56])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_90]),c_0_92]),c_0_92])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.41/0.60  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.41/0.60  # and selection function SelectNewComplexAHP.
% 0.41/0.60  #
% 0.41/0.60  # Preprocessing time       : 0.027 s
% 0.41/0.60  # Presaturation interreduction done
% 0.41/0.60  
% 0.41/0.60  # Proof found!
% 0.41/0.60  # SZS status Theorem
% 0.41/0.60  # SZS output start CNFRefutation
% 0.41/0.60  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.41/0.60  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.41/0.60  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.41/0.60  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.41/0.60  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.41/0.60  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.41/0.60  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.41/0.60  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.41/0.60  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.41/0.60  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.41/0.60  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.41/0.60  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.41/0.60  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.41/0.60  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.41/0.60  fof(t70_enumset1, conjecture, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.41/0.60  fof(c_0_15, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.41/0.60  fof(c_0_16, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.41/0.60  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.41/0.60  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.60  fof(c_0_19, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.41/0.60  fof(c_0_20, plain, ![X19, X20]:k2_xboole_0(X19,X20)=k5_xboole_0(X19,k4_xboole_0(X20,X19)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.41/0.60  fof(c_0_21, plain, ![X11]:k2_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.41/0.60  cnf(c_0_22, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 0.41/0.60  fof(c_0_23, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.41/0.60  cnf(c_0_24, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.60  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.41/0.60  cnf(c_0_26, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.41/0.60  cnf(c_0_27, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_22, c_0_22])).
% 0.41/0.60  cnf(c_0_28, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.41/0.60  cnf(c_0_29, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_18])).
% 0.41/0.60  fof(c_0_30, plain, ![X16, X17, X18]:k5_xboole_0(k5_xboole_0(X16,X17),X18)=k5_xboole_0(X16,k5_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.41/0.60  cnf(c_0_31, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_25]), c_0_18])).
% 0.41/0.60  cnf(c_0_32, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X1))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 0.41/0.60  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 0.41/0.60  cnf(c_0_34, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.41/0.60  fof(c_0_35, plain, ![X12, X13]:k2_xboole_0(X12,k3_xboole_0(X12,X13))=X12, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.41/0.60  cnf(c_0_36, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_33])).
% 0.41/0.60  cnf(c_0_37, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.41/0.60  fof(c_0_38, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.41/0.60  cnf(c_0_39, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.41/0.60  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_25]), c_0_18])).
% 0.41/0.60  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.41/0.60  cnf(c_0_42, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_22])).
% 0.41/0.60  cnf(c_0_43, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.41/0.60  cnf(c_0_44, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_31, c_0_42])).
% 0.41/0.60  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_34])).
% 0.41/0.60  cnf(c_0_46, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_42])).
% 0.41/0.60  cnf(c_0_47, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_22])).
% 0.41/0.60  cnf(c_0_48, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_46])).
% 0.41/0.60  cnf(c_0_49, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_44, c_0_46])).
% 0.41/0.60  cnf(c_0_50, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.41/0.60  cnf(c_0_51, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.41/0.60  cnf(c_0_52, plain, (k5_xboole_0(k1_xboole_0,X1)=k5_xboole_0(X2,k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_34, c_0_50])).
% 0.41/0.60  fof(c_0_53, plain, ![X27, X28, X29]:k1_enumset1(X27,X28,X29)=k2_xboole_0(k1_tarski(X27),k2_tarski(X28,X29)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.41/0.60  fof(c_0_54, plain, ![X34]:k2_tarski(X34,X34)=k1_tarski(X34), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.41/0.60  fof(c_0_55, plain, ![X21, X22, X23, X24]:k2_enumset1(X21,X22,X23,X24)=k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X24)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.41/0.60  cnf(c_0_56, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.41/0.60  fof(c_0_57, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_xboole_0(k1_tarski(X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.41/0.60  fof(c_0_58, plain, ![X30, X31, X32, X33]:k2_enumset1(X30,X31,X32,X33)=k2_xboole_0(k1_tarski(X30),k1_enumset1(X31,X32,X33)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.41/0.60  cnf(c_0_59, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.41/0.60  cnf(c_0_60, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.41/0.60  cnf(c_0_61, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.41/0.60  cnf(c_0_62, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_52, c_0_56])).
% 0.41/0.60  cnf(c_0_63, plain, (k1_xboole_0=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_34, c_0_50])).
% 0.41/0.60  cnf(c_0_64, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.41/0.60  cnf(c_0_65, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.41/0.60  cnf(c_0_66, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_25]), c_0_18])).
% 0.41/0.60  cnf(c_0_67, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_25]), c_0_18])).
% 0.41/0.60  cnf(c_0_68, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_49])).
% 0.41/0.60  cnf(c_0_69, plain, (k2_tarski(X1,X2)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_60]), c_0_60]), c_0_25]), c_0_18])).
% 0.41/0.60  cnf(c_0_70, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_60]), c_0_25]), c_0_18]), c_0_66]), c_0_66]), c_0_67])).
% 0.41/0.60  fof(c_0_71, negated_conjecture, ~(![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t70_enumset1])).
% 0.41/0.60  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1)))=k5_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_68, c_0_34])).
% 0.41/0.60  cnf(c_0_73, plain, (k5_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2))=k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))), inference(spm,[status(thm)],[c_0_62, c_0_69])).
% 0.41/0.60  cnf(c_0_74, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X1,X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_34]), c_0_34])).
% 0.41/0.60  cnf(c_0_75, plain, (k2_tarski(X1,X2)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))))), inference(spm,[status(thm)],[c_0_69, c_0_41])).
% 0.41/0.60  fof(c_0_76, negated_conjecture, k1_enumset1(esk1_0,esk1_0,esk2_0)!=k2_tarski(esk1_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_71])])])).
% 0.41/0.60  cnf(c_0_77, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(X3,k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))))=k5_xboole_0(X3,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.41/0.60  cnf(c_0_78, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X2))))=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_28]), c_0_33]), c_0_47])).
% 0.41/0.60  cnf(c_0_79, plain, (k5_xboole_0(k2_tarski(X1,X2),X3)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)),X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_69]), c_0_34])).
% 0.41/0.60  cnf(c_0_80, plain, (k5_xboole_0(k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)),k2_tarski(X1,X2))=k5_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_72, c_0_75])).
% 0.41/0.60  cnf(c_0_81, negated_conjecture, (k1_enumset1(esk1_0,esk1_0,esk2_0)!=k2_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.41/0.60  cnf(c_0_82, plain, (k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_62]), c_0_50])).
% 0.41/0.60  cnf(c_0_83, plain, (k5_xboole_0(k2_tarski(X1,X2),k2_tarski(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_62]), c_0_50])).
% 0.41/0.60  cnf(c_0_84, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_62, c_0_68])).
% 0.41/0.60  cnf(c_0_85, negated_conjecture, (k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk2_0),k2_tarski(esk1_0,esk1_0))))!=k2_tarski(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_81, c_0_66])).
% 0.41/0.60  cnf(c_0_86, plain, (k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X1))=k2_tarski(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_82]), c_0_49])).
% 0.41/0.60  cnf(c_0_87, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_83]), c_0_49])).
% 0.41/0.60  cnf(c_0_88, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_34, c_0_84])).
% 0.41/0.60  cnf(c_0_89, negated_conjecture, (k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk2_0))))!=k2_tarski(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_85, c_0_41])).
% 0.41/0.60  cnf(c_0_90, plain, (k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2))=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.41/0.60  cnf(c_0_91, plain, (k5_xboole_0(X1,k2_tarski(X2,X3))=k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X3,X3),k2_tarski(X2,X2)),X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_69]), c_0_34])).
% 0.41/0.60  cnf(c_0_92, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X2,X1),X3))=X3), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_83]), c_0_56])).
% 0.41/0.60  cnf(c_0_93, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90]), c_0_91]), c_0_90]), c_0_92]), c_0_92])]), ['proof']).
% 0.41/0.60  # SZS output end CNFRefutation
% 0.41/0.60  # Proof object total steps             : 94
% 0.41/0.60  # Proof object clause steps            : 63
% 0.41/0.60  # Proof object formula steps           : 31
% 0.41/0.60  # Proof object conjectures             : 7
% 0.41/0.60  # Proof object clause conjectures      : 4
% 0.41/0.60  # Proof object formula conjectures     : 3
% 0.41/0.60  # Proof object initial clauses used    : 15
% 0.41/0.60  # Proof object initial formulas used   : 15
% 0.41/0.60  # Proof object generating inferences   : 31
% 0.41/0.60  # Proof object simplifying inferences  : 57
% 0.41/0.60  # Training examples: 0 positive, 0 negative
% 0.41/0.60  # Parsed axioms                        : 15
% 0.41/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.60  # Initial clauses                      : 15
% 0.41/0.60  # Removed in clause preprocessing      : 5
% 0.41/0.60  # Initial clauses in saturation        : 10
% 0.41/0.60  # Processed clauses                    : 2946
% 0.41/0.60  # ...of these trivial                  : 1349
% 0.41/0.60  # ...subsumed                          : 1400
% 0.41/0.60  # ...remaining for further processing  : 197
% 0.41/0.60  # Other redundant clauses eliminated   : 0
% 0.41/0.60  # Clauses deleted for lack of memory   : 0
% 0.41/0.60  # Backward-subsumed                    : 0
% 0.41/0.60  # Backward-rewritten                   : 25
% 0.41/0.60  # Generated clauses                    : 26985
% 0.41/0.60  # ...of the previous two non-trivial   : 20321
% 0.41/0.60  # Contextual simplify-reflections      : 0
% 0.41/0.60  # Paramodulations                      : 26985
% 0.41/0.60  # Factorizations                       : 0
% 0.41/0.60  # Equation resolutions                 : 0
% 0.41/0.60  # Propositional unsat checks           : 0
% 0.41/0.60  #    Propositional check models        : 0
% 0.41/0.60  #    Propositional check unsatisfiable : 0
% 0.41/0.60  #    Propositional clauses             : 0
% 0.41/0.60  #    Propositional clauses after purity: 0
% 0.41/0.60  #    Propositional unsat core size     : 0
% 0.41/0.60  #    Propositional preprocessing time  : 0.000
% 0.41/0.60  #    Propositional encoding time       : 0.000
% 0.41/0.60  #    Propositional solver time         : 0.000
% 0.41/0.60  #    Success case prop preproc time    : 0.000
% 0.41/0.60  #    Success case prop encoding time   : 0.000
% 0.41/0.60  #    Success case prop solver time     : 0.000
% 0.41/0.60  # Current number of processed clauses  : 162
% 0.41/0.60  #    Positive orientable unit clauses  : 103
% 0.41/0.60  #    Positive unorientable unit clauses: 59
% 0.41/0.60  #    Negative unit clauses             : 0
% 0.41/0.60  #    Non-unit-clauses                  : 0
% 0.41/0.60  # Current number of unprocessed clauses: 17236
% 0.41/0.60  # ...number of literals in the above   : 17236
% 0.41/0.60  # Current number of archived formulas  : 0
% 0.41/0.60  # Current number of archived clauses   : 40
% 0.41/0.60  # Clause-clause subsumption calls (NU) : 0
% 0.41/0.60  # Rec. Clause-clause subsumption calls : 0
% 0.41/0.60  # Non-unit clause-clause subsumptions  : 0
% 0.41/0.60  # Unit Clause-clause subsumption calls : 1451
% 0.41/0.60  # Rewrite failures with RHS unbound    : 60
% 0.41/0.60  # BW rewrite match attempts            : 2716
% 0.41/0.60  # BW rewrite match successes           : 1091
% 0.41/0.60  # Condensation attempts                : 0
% 0.41/0.60  # Condensation successes               : 0
% 0.41/0.60  # Termbank termtop insertions          : 398815
% 0.41/0.61  
% 0.41/0.61  # -------------------------------------------------
% 0.41/0.61  # User time                : 0.239 s
% 0.41/0.61  # System time              : 0.013 s
% 0.41/0.61  # Total time               : 0.251 s
% 0.41/0.61  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
