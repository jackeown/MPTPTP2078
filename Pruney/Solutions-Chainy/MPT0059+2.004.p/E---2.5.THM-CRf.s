%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:23 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  102 (31730 expanded)
%              Number of clauses        :   83 (13953 expanded)
%              Number of leaves         :    9 (8888 expanded)
%              Depth                    :   28
%              Number of atoms          :  108 (38830 expanded)
%              Number of equality atoms :   87 (28359 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t52_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(c_0_9,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_10,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_11,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_12,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_14,plain,(
    ! [X19,X20,X21] : k3_xboole_0(X19,k4_xboole_0(X20,X21)) = k4_xboole_0(k3_xboole_0(X19,X20),k3_xboole_0(X19,X21)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

cnf(c_0_15,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,plain,(
    ! [X9,X10,X11] : k3_xboole_0(k3_xboole_0(X9,X10),X11) = k3_xboole_0(X9,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_27,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_16])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_16]),c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_18]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_30]),c_0_25]),c_0_28])).

fof(c_0_33,plain,(
    ! [X6,X7,X8] : k4_xboole_0(X6,k3_xboole_0(X7,X8)) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,X8)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_16])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_26])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_31])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_37])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X1,X3)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_26]),c_0_16])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_40])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_41]),c_0_41]),c_0_16])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_43])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_23])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_28]),c_0_24]),c_0_47])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_23]),c_0_48])).

cnf(c_0_52,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_51])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_31])).

cnf(c_0_56,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_24]),c_0_16])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_51])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_34])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X3) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_51])).

cnf(c_0_63,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_16]),c_0_26]),c_0_16])).

cnf(c_0_65,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4),k4_xboole_0(X1,X4)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_51])).

cnf(c_0_66,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X4)),X4) ),
    inference(spm,[status(thm)],[c_0_63,c_0_51])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_64,c_0_26])).

cnf(c_0_68,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_64,c_0_23])).

cnf(c_0_69,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_58])).

cnf(c_0_70,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X3),X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_58])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_24]),c_0_67])).

cnf(c_0_73,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))),X3) = X3 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_32]),c_0_25])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3),k4_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_69])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X3),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_70])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_61]),c_0_16])).

cnf(c_0_77,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X1))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_50]),c_0_72])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X3),X2) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_16])).

cnf(c_0_79,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2)),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_75])).

cnf(c_0_80,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X3),X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_23]),c_0_77])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_32])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_16]),c_0_80])).

cnf(c_0_83,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X3) = X3 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_61]),c_0_16])).

cnf(c_0_84,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_81]),c_0_28]),c_0_24]),c_0_47])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_38])).

cnf(c_0_87,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))),X3) = X3 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_32])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_55]),c_0_85])).

fof(c_0_89,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t52_xboole_1])).

cnf(c_0_90,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_85]),c_0_88]),c_0_85])).

fof(c_0_91,negated_conjecture,(
    k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_89])])])).

cnf(c_0_92,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_94,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_92]),c_0_92])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X3))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_38])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_93,c_0_18])).

cnf(c_0_97,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_38]),c_0_95])).

cnf(c_0_98,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X4,X1)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_50]),c_0_85])).

cnf(c_0_99,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0))) != k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_96,c_0_23])).

cnf(c_0_100,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_23]),c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:31:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.43/0.58  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.43/0.58  # and selection function SelectNewComplexAHP.
% 0.43/0.58  #
% 0.43/0.58  # Preprocessing time       : 0.026 s
% 0.43/0.58  # Presaturation interreduction done
% 0.43/0.58  
% 0.43/0.58  # Proof found!
% 0.43/0.58  # SZS status Theorem
% 0.43/0.58  # SZS output start CNFRefutation
% 0.43/0.58  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.43/0.58  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.43/0.58  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.43/0.58  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.43/0.58  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.43/0.58  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.43/0.58  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.43/0.58  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 0.43/0.58  fof(t52_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.43/0.58  fof(c_0_9, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.43/0.58  fof(c_0_10, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.43/0.58  fof(c_0_11, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.43/0.58  fof(c_0_12, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.43/0.58  fof(c_0_13, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.43/0.58  fof(c_0_14, plain, ![X19, X20, X21]:k3_xboole_0(X19,k4_xboole_0(X20,X21))=k4_xboole_0(k3_xboole_0(X19,X20),k3_xboole_0(X19,X21)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 0.43/0.58  cnf(c_0_15, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.43/0.58  cnf(c_0_16, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.43/0.58  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.43/0.58  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.43/0.58  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.43/0.58  cnf(c_0_20, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.58  cnf(c_0_21, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.43/0.58  fof(c_0_22, plain, ![X9, X10, X11]:k3_xboole_0(k3_xboole_0(X9,X10),X11)=k3_xboole_0(X9,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.43/0.58  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 0.43/0.58  cnf(c_0_24, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_15])).
% 0.43/0.58  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_18]), c_0_18])).
% 0.43/0.58  cnf(c_0_26, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_21])).
% 0.43/0.58  cnf(c_0_27, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.43/0.58  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_16])).
% 0.43/0.58  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_16]), c_0_24])).
% 0.43/0.58  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 0.43/0.58  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_16])).
% 0.43/0.58  cnf(c_0_32, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_30]), c_0_25]), c_0_28])).
% 0.43/0.58  fof(c_0_33, plain, ![X6, X7, X8]:k4_xboole_0(X6,k3_xboole_0(X7,X8))=k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,X8)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 0.43/0.58  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1))))=X1), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.43/0.58  cnf(c_0_35, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.43/0.58  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_24]), c_0_16])).
% 0.43/0.58  cnf(c_0_37, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_26])).
% 0.43/0.58  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_35, c_0_18])).
% 0.43/0.58  cnf(c_0_39, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_31])).
% 0.43/0.58  cnf(c_0_40, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_31])).
% 0.43/0.58  cnf(c_0_41, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_37])).
% 0.43/0.58  cnf(c_0_42, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X1,X3))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_26]), c_0_16])).
% 0.43/0.58  cnf(c_0_43, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_40])).
% 0.43/0.58  cnf(c_0_44, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_16]), c_0_41]), c_0_41]), c_0_16])).
% 0.43/0.58  cnf(c_0_45, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 0.43/0.58  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_32, c_0_43])).
% 0.43/0.58  cnf(c_0_47, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 0.43/0.58  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_23])).
% 0.43/0.58  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_15, c_0_23])).
% 0.43/0.58  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_28]), c_0_24]), c_0_47])).
% 0.43/0.58  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_23]), c_0_48])).
% 0.43/0.58  cnf(c_0_52, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.43/0.58  cnf(c_0_53, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_51])).
% 0.43/0.58  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 0.43/0.58  cnf(c_0_55, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_50, c_0_31])).
% 0.43/0.58  cnf(c_0_56, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_24]), c_0_16])).
% 0.43/0.58  cnf(c_0_57, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_51])).
% 0.43/0.58  cnf(c_0_58, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3),X2)=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.43/0.58  cnf(c_0_59, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_56, c_0_34])).
% 0.43/0.58  cnf(c_0_60, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.43/0.58  cnf(c_0_61, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X3)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.43/0.58  cnf(c_0_62, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_59, c_0_51])).
% 0.43/0.58  cnf(c_0_63, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X3)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.43/0.58  cnf(c_0_64, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_16]), c_0_16]), c_0_26]), c_0_16])).
% 0.43/0.58  cnf(c_0_65, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4),k4_xboole_0(X1,X4))), inference(spm,[status(thm)],[c_0_62, c_0_51])).
% 0.43/0.58  cnf(c_0_66, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X4)),X4)), inference(spm,[status(thm)],[c_0_63, c_0_51])).
% 0.43/0.58  cnf(c_0_67, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_64, c_0_26])).
% 0.43/0.58  cnf(c_0_68, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)=X2), inference(spm,[status(thm)],[c_0_64, c_0_23])).
% 0.43/0.58  cnf(c_0_69, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_65, c_0_58])).
% 0.43/0.58  cnf(c_0_70, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X3),X2)), inference(spm,[status(thm)],[c_0_66, c_0_58])).
% 0.43/0.58  cnf(c_0_71, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_44, c_0_23])).
% 0.43/0.58  cnf(c_0_72, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_24]), c_0_67])).
% 0.43/0.58  cnf(c_0_73, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))),X3)=X3), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_32]), c_0_25])).
% 0.43/0.58  cnf(c_0_74, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3),k4_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_69])).
% 0.43/0.58  cnf(c_0_75, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X3),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_70])).
% 0.43/0.58  cnf(c_0_76, plain, (k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_61]), c_0_16])).
% 0.43/0.58  cnf(c_0_77, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X1)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_50]), c_0_72])).
% 0.43/0.58  cnf(c_0_78, plain, (k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X3),X2)=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_16])).
% 0.43/0.58  cnf(c_0_79, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2)),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_75])).
% 0.43/0.58  cnf(c_0_80, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X3),X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_23]), c_0_77])).
% 0.43/0.58  cnf(c_0_81, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_25, c_0_32])).
% 0.43/0.58  cnf(c_0_82, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_16]), c_0_80])).
% 0.43/0.58  cnf(c_0_83, plain, (k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X3)=X3), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_61]), c_0_16])).
% 0.43/0.58  cnf(c_0_84, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))))))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.43/0.58  cnf(c_0_85, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_81]), c_0_28]), c_0_24]), c_0_47])).
% 0.43/0.58  cnf(c_0_86, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_82, c_0_38])).
% 0.43/0.58  cnf(c_0_87, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))),X3)=X3), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_32])).
% 0.43/0.58  cnf(c_0_88, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_55]), c_0_85])).
% 0.43/0.58  fof(c_0_89, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t52_xboole_1])).
% 0.43/0.58  cnf(c_0_90, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_85]), c_0_88]), c_0_85])).
% 0.43/0.58  fof(c_0_91, negated_conjecture, k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_89])])])).
% 0.43/0.58  cnf(c_0_92, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_50, c_0_90])).
% 0.43/0.58  cnf(c_0_93, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.43/0.58  cnf(c_0_94, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X2,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_92]), c_0_92])).
% 0.43/0.58  cnf(c_0_95, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X3)))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_85, c_0_38])).
% 0.43/0.58  cnf(c_0_96, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_93, c_0_18])).
% 0.43/0.58  cnf(c_0_97, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_38]), c_0_95])).
% 0.43/0.58  cnf(c_0_98, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X4,X1))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_50]), c_0_85])).
% 0.43/0.58  cnf(c_0_99, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0)))!=k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_96, c_0_23])).
% 0.43/0.58  cnf(c_0_100, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_23]), c_0_98])).
% 0.43/0.58  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])]), ['proof']).
% 0.43/0.58  # SZS output end CNFRefutation
% 0.43/0.58  # Proof object total steps             : 102
% 0.43/0.58  # Proof object clause steps            : 83
% 0.43/0.58  # Proof object formula steps           : 19
% 0.43/0.58  # Proof object conjectures             : 7
% 0.43/0.58  # Proof object clause conjectures      : 4
% 0.43/0.58  # Proof object formula conjectures     : 3
% 0.43/0.58  # Proof object initial clauses used    : 10
% 0.43/0.58  # Proof object initial formulas used   : 9
% 0.43/0.58  # Proof object generating inferences   : 65
% 0.43/0.58  # Proof object simplifying inferences  : 56
% 0.43/0.58  # Training examples: 0 positive, 0 negative
% 0.43/0.58  # Parsed axioms                        : 9
% 0.43/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.43/0.58  # Initial clauses                      : 10
% 0.43/0.58  # Removed in clause preprocessing      : 1
% 0.43/0.58  # Initial clauses in saturation        : 9
% 0.43/0.58  # Processed clauses                    : 727
% 0.43/0.58  # ...of these trivial                  : 269
% 0.43/0.58  # ...subsumed                          : 232
% 0.43/0.58  # ...remaining for further processing  : 226
% 0.43/0.58  # Other redundant clauses eliminated   : 0
% 0.43/0.58  # Clauses deleted for lack of memory   : 0
% 0.43/0.58  # Backward-subsumed                    : 3
% 0.43/0.58  # Backward-rewritten                   : 99
% 0.43/0.58  # Generated clauses                    : 35196
% 0.43/0.58  # ...of the previous two non-trivial   : 14409
% 0.43/0.58  # Contextual simplify-reflections      : 0
% 0.43/0.58  # Paramodulations                      : 35190
% 0.43/0.58  # Factorizations                       : 0
% 0.43/0.58  # Equation resolutions                 : 6
% 0.43/0.58  # Propositional unsat checks           : 0
% 0.43/0.58  #    Propositional check models        : 0
% 0.43/0.58  #    Propositional check unsatisfiable : 0
% 0.43/0.58  #    Propositional clauses             : 0
% 0.43/0.58  #    Propositional clauses after purity: 0
% 0.43/0.58  #    Propositional unsat core size     : 0
% 0.43/0.58  #    Propositional preprocessing time  : 0.000
% 0.43/0.58  #    Propositional encoding time       : 0.000
% 0.43/0.58  #    Propositional solver time         : 0.000
% 0.43/0.58  #    Success case prop preproc time    : 0.000
% 0.43/0.58  #    Success case prop encoding time   : 0.000
% 0.43/0.58  #    Success case prop solver time     : 0.000
% 0.43/0.58  # Current number of processed clauses  : 115
% 0.43/0.58  #    Positive orientable unit clauses  : 92
% 0.43/0.58  #    Positive unorientable unit clauses: 3
% 0.43/0.58  #    Negative unit clauses             : 0
% 0.43/0.58  #    Non-unit-clauses                  : 20
% 0.43/0.58  # Current number of unprocessed clauses: 13478
% 0.43/0.58  # ...number of literals in the above   : 14478
% 0.43/0.58  # Current number of archived formulas  : 0
% 0.43/0.58  # Current number of archived clauses   : 112
% 0.43/0.58  # Clause-clause subsumption calls (NU) : 941
% 0.43/0.58  # Rec. Clause-clause subsumption calls : 941
% 0.43/0.58  # Non-unit clause-clause subsumptions  : 195
% 0.43/0.58  # Unit Clause-clause subsumption calls : 117
% 0.43/0.58  # Rewrite failures with RHS unbound    : 0
% 0.43/0.58  # BW rewrite match attempts            : 976
% 0.43/0.58  # BW rewrite match successes           : 145
% 0.43/0.58  # Condensation attempts                : 0
% 0.43/0.58  # Condensation successes               : 0
% 0.43/0.58  # Termbank termtop insertions          : 344198
% 0.43/0.58  
% 0.43/0.58  # -------------------------------------------------
% 0.43/0.58  # User time                : 0.222 s
% 0.43/0.58  # System time              : 0.012 s
% 0.43/0.58  # Total time               : 0.234 s
% 0.43/0.58  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
