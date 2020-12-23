%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:14 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 624 expanded)
%              Number of clauses        :   70 ( 285 expanded)
%              Number of leaves         :   13 ( 169 expanded)
%              Depth                    :   18
%              Number of atoms          :  106 ( 712 expanded)
%              Number of equality atoms :   76 ( 568 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t24_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t47_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_13,plain,(
    ! [X16] : k2_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_14,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_15,plain,(
    ! [X26,X27] : k4_xboole_0(k2_xboole_0(X26,X27),X27) = k4_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X24,X25] : k2_xboole_0(X24,k4_xboole_0(X25,X24)) = k2_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_22,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_23,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_24,plain,(
    ! [X17,X18,X19] : k2_xboole_0(X17,k3_xboole_0(X18,X19)) = k3_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(X17,X19)) ),
    inference(variable_rename,[status(thm)],[t24_xboole_1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X28,X29,X30] : k4_xboole_0(k4_xboole_0(X28,X29),X30) = k4_xboole_0(X28,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_25]),c_0_16])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_37,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_38,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X1)),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_25])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_35]),c_0_16]),c_0_36])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_43,plain,(
    ! [X11,X12,X13] : k3_xboole_0(k3_xboole_0(X11,X12),X13) = k3_xboole_0(X11,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_39]),c_0_34]),c_0_16])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_34])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_34])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_36,c_0_40])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_27]),c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_42])).

cnf(c_0_52,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_46]),c_0_34])).

cnf(c_0_55,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_47]),c_0_25])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_17])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

cnf(c_0_58,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_53])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_54]),c_0_25])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_55])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_16])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_20])).

cnf(c_0_68,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_17]),c_0_63])).

cnf(c_0_69,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_64])).

cnf(c_0_70,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_65])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_25]),c_0_31])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_66])).

cnf(c_0_73,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_35])).

cnf(c_0_74,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_68])).

cnf(c_0_75,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_20])).

cnf(c_0_76,plain,
    ( r1_tarski(k4_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))),X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X1,X3)),X4)) = k2_xboole_0(X4,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_16]),c_0_52]),c_0_74])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X1,X2),X3)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_59]),c_0_40])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_75]),c_0_42])).

cnf(c_0_80,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_34])).

cnf(c_0_81,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_51])).

cnf(c_0_82,plain,
    ( r1_tarski(k4_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))),X3) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) = X1 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_17])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_81]),c_0_16])).

fof(c_0_86,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t47_xboole_1])).

cnf(c_0_87,plain,
    ( r1_tarski(k4_xboole_0(X1,k3_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

fof(c_0_89,negated_conjecture,(
    k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_86])])])).

cnf(c_0_90,plain,
    ( r1_tarski(k4_xboole_0(X1,k3_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_67])).

cnf(c_0_91,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k3_xboole_0(X3,X2))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_93,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_90]),c_0_42]),c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_42])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_93,c_0_42])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:48:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 4.32/4.52  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 4.32/4.52  # and selection function SelectNewComplexAHP.
% 4.32/4.52  #
% 4.32/4.52  # Preprocessing time       : 0.027 s
% 4.32/4.52  # Presaturation interreduction done
% 4.32/4.52  
% 4.32/4.52  # Proof found!
% 4.32/4.52  # SZS status Theorem
% 4.32/4.52  # SZS output start CNFRefutation
% 4.32/4.52  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.32/4.52  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.32/4.52  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.32/4.52  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.32/4.52  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.32/4.52  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.32/4.52  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.32/4.52  fof(t24_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_xboole_1)).
% 4.32/4.52  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.32/4.52  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.32/4.52  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.32/4.52  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.32/4.52  fof(t47_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.32/4.52  fof(c_0_13, plain, ![X16]:k2_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t1_boole])).
% 4.32/4.52  fof(c_0_14, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 4.32/4.52  fof(c_0_15, plain, ![X26, X27]:k4_xboole_0(k2_xboole_0(X26,X27),X27)=k4_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 4.32/4.52  cnf(c_0_16, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.32/4.52  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.32/4.52  fof(c_0_18, plain, ![X24, X25]:k2_xboole_0(X24,k4_xboole_0(X25,X24))=k2_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 4.32/4.52  cnf(c_0_19, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.32/4.52  cnf(c_0_20, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 4.32/4.52  fof(c_0_21, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 4.32/4.52  fof(c_0_22, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 4.32/4.52  fof(c_0_23, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 4.32/4.52  fof(c_0_24, plain, ![X17, X18, X19]:k2_xboole_0(X17,k3_xboole_0(X18,X19))=k3_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[t24_xboole_1])).
% 4.32/4.52  cnf(c_0_25, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.32/4.52  cnf(c_0_26, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 4.32/4.52  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.32/4.52  fof(c_0_28, plain, ![X28, X29, X30]:k4_xboole_0(k4_xboole_0(X28,X29),X30)=k4_xboole_0(X28,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 4.32/4.52  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.32/4.52  cnf(c_0_30, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.32/4.52  cnf(c_0_31, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.32/4.52  cnf(c_0_32, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_25]), c_0_16])).
% 4.32/4.52  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 4.32/4.52  cnf(c_0_34, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.32/4.52  cnf(c_0_35, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 4.32/4.52  cnf(c_0_36, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 4.32/4.52  fof(c_0_37, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 4.32/4.52  fof(c_0_38, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 4.32/4.52  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X1)),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_25])).
% 4.32/4.52  cnf(c_0_40, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_35]), c_0_16]), c_0_36])).
% 4.32/4.52  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 4.32/4.52  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 4.32/4.52  fof(c_0_43, plain, ![X11, X12, X13]:k3_xboole_0(k3_xboole_0(X11,X12),X13)=k3_xboole_0(X11,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 4.32/4.52  cnf(c_0_44, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.32/4.52  cnf(c_0_45, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_39]), c_0_34]), c_0_16])).
% 4.32/4.52  cnf(c_0_46, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 4.32/4.52  cnf(c_0_47, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_19]), c_0_34])).
% 4.32/4.52  cnf(c_0_48, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_34])).
% 4.32/4.52  cnf(c_0_49, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_36, c_0_40])).
% 4.32/4.52  cnf(c_0_50, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_27]), c_0_42])).
% 4.32/4.52  cnf(c_0_51, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_30, c_0_42])).
% 4.32/4.52  cnf(c_0_52, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 4.32/4.52  cnf(c_0_53, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 4.32/4.52  cnf(c_0_54, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_46]), c_0_34])).
% 4.32/4.52  cnf(c_0_55, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_47]), c_0_25])).
% 4.32/4.52  cnf(c_0_56, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_48, c_0_17])).
% 4.32/4.52  cnf(c_0_57, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,X2))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_45])).
% 4.32/4.52  cnf(c_0_58, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k2_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_31, c_0_17])).
% 4.32/4.52  cnf(c_0_59, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 4.32/4.52  cnf(c_0_60, plain, (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 4.32/4.52  cnf(c_0_61, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_41, c_0_53])).
% 4.32/4.52  cnf(c_0_62, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_54]), c_0_25])).
% 4.32/4.52  cnf(c_0_63, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k2_xboole_0(k2_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_17, c_0_55])).
% 4.32/4.52  cnf(c_0_64, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_16])).
% 4.32/4.52  cnf(c_0_65, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 4.32/4.52  cnf(c_0_66, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 4.32/4.52  cnf(c_0_67, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_20])).
% 4.32/4.52  cnf(c_0_68, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X3,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_17]), c_0_63])).
% 4.32/4.52  cnf(c_0_69, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))),X3)), inference(spm,[status(thm)],[c_0_53, c_0_64])).
% 4.32/4.52  cnf(c_0_70, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X3),X2))), inference(spm,[status(thm)],[c_0_17, c_0_65])).
% 4.32/4.52  cnf(c_0_71, plain, (k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_25]), c_0_31])).
% 4.32/4.52  cnf(c_0_72, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_66])).
% 4.32/4.52  cnf(c_0_73, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_35])).
% 4.32/4.52  cnf(c_0_74, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X2,k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_17, c_0_68])).
% 4.32/4.52  cnf(c_0_75, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_69, c_0_20])).
% 4.32/4.52  cnf(c_0_76, plain, (r1_tarski(k4_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))),X2)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 4.32/4.52  cnf(c_0_77, plain, (k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X1,X3)),X4))=k2_xboole_0(X4,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_16]), c_0_52]), c_0_74])).
% 4.32/4.52  cnf(c_0_78, plain, (k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X1,X2),X3))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_59]), c_0_40])).
% 4.32/4.52  cnf(c_0_79, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_75]), c_0_42])).
% 4.32/4.52  cnf(c_0_80, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_27, c_0_34])).
% 4.32/4.52  cnf(c_0_81, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_51])).
% 4.32/4.52  cnf(c_0_82, plain, (r1_tarski(k4_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))),X3)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 4.32/4.52  cnf(c_0_83, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))=X1), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 4.32/4.52  cnf(c_0_84, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_80, c_0_17])).
% 4.32/4.52  cnf(c_0_85, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_81]), c_0_16])).
% 4.32/4.52  fof(c_0_86, negated_conjecture, ~(![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t47_xboole_1])).
% 4.32/4.52  cnf(c_0_87, plain, (r1_tarski(k4_xboole_0(X1,k3_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 4.32/4.52  cnf(c_0_88, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 4.32/4.52  fof(c_0_89, negated_conjecture, k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(esk1_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_86])])])).
% 4.32/4.52  cnf(c_0_90, plain, (r1_tarski(k4_xboole_0(X1,k3_xboole_0(X1,X2)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_87, c_0_67])).
% 4.32/4.52  cnf(c_0_91, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k3_xboole_0(X3,X2)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_88])).
% 4.32/4.52  cnf(c_0_92, negated_conjecture, (k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 4.32/4.52  cnf(c_0_93, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_90]), c_0_42]), c_0_91])).
% 4.32/4.52  cnf(c_0_94, negated_conjecture, (k4_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))!=k4_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_92, c_0_42])).
% 4.32/4.52  cnf(c_0_95, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_93, c_0_42])).
% 4.32/4.52  cnf(c_0_96, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])]), ['proof']).
% 4.32/4.52  # SZS output end CNFRefutation
% 4.32/4.52  # Proof object total steps             : 97
% 4.32/4.52  # Proof object clause steps            : 70
% 4.32/4.52  # Proof object formula steps           : 27
% 4.32/4.52  # Proof object conjectures             : 6
% 4.32/4.52  # Proof object clause conjectures      : 3
% 4.32/4.52  # Proof object formula conjectures     : 3
% 4.32/4.52  # Proof object initial clauses used    : 14
% 4.32/4.52  # Proof object initial formulas used   : 13
% 4.32/4.52  # Proof object generating inferences   : 53
% 4.32/4.52  # Proof object simplifying inferences  : 29
% 4.32/4.52  # Training examples: 0 positive, 0 negative
% 4.32/4.52  # Parsed axioms                        : 14
% 4.32/4.52  # Removed by relevancy pruning/SinE    : 0
% 4.32/4.52  # Initial clauses                      : 15
% 4.32/4.52  # Removed in clause preprocessing      : 0
% 4.32/4.52  # Initial clauses in saturation        : 15
% 4.32/4.52  # Processed clauses                    : 12488
% 4.32/4.52  # ...of these trivial                  : 4730
% 4.32/4.52  # ...subsumed                          : 6404
% 4.32/4.52  # ...remaining for further processing  : 1354
% 4.32/4.52  # Other redundant clauses eliminated   : 0
% 4.32/4.52  # Clauses deleted for lack of memory   : 0
% 4.32/4.52  # Backward-subsumed                    : 0
% 4.32/4.52  # Backward-rewritten                   : 237
% 4.32/4.52  # Generated clauses                    : 669642
% 4.32/4.52  # ...of the previous two non-trivial   : 445685
% 4.32/4.52  # Contextual simplify-reflections      : 0
% 4.32/4.52  # Paramodulations                      : 669641
% 4.32/4.52  # Factorizations                       : 0
% 4.32/4.52  # Equation resolutions                 : 1
% 4.32/4.52  # Propositional unsat checks           : 0
% 4.32/4.52  #    Propositional check models        : 0
% 4.32/4.52  #    Propositional check unsatisfiable : 0
% 4.32/4.52  #    Propositional clauses             : 0
% 4.32/4.52  #    Propositional clauses after purity: 0
% 4.32/4.52  #    Propositional unsat core size     : 0
% 4.32/4.52  #    Propositional preprocessing time  : 0.000
% 4.32/4.52  #    Propositional encoding time       : 0.000
% 4.32/4.52  #    Propositional solver time         : 0.000
% 4.32/4.52  #    Success case prop preproc time    : 0.000
% 4.32/4.52  #    Success case prop encoding time   : 0.000
% 4.32/4.52  #    Success case prop solver time     : 0.000
% 4.32/4.52  # Current number of processed clauses  : 1102
% 4.32/4.52  #    Positive orientable unit clauses  : 1056
% 4.32/4.52  #    Positive unorientable unit clauses: 12
% 4.32/4.52  #    Negative unit clauses             : 0
% 4.32/4.52  #    Non-unit-clauses                  : 34
% 4.32/4.52  # Current number of unprocessed clauses: 430623
% 4.32/4.52  # ...number of literals in the above   : 437402
% 4.32/4.52  # Current number of archived formulas  : 0
% 4.32/4.52  # Current number of archived clauses   : 252
% 4.32/4.52  # Clause-clause subsumption calls (NU) : 1274
% 4.32/4.52  # Rec. Clause-clause subsumption calls : 1252
% 4.32/4.52  # Non-unit clause-clause subsumptions  : 402
% 4.32/4.52  # Unit Clause-clause subsumption calls : 206
% 4.32/4.52  # Rewrite failures with RHS unbound    : 0
% 4.32/4.52  # BW rewrite match attempts            : 6993
% 4.32/4.52  # BW rewrite match successes           : 656
% 4.32/4.52  # Condensation attempts                : 0
% 4.32/4.52  # Condensation successes               : 0
% 4.32/4.52  # Termbank termtop insertions          : 7384655
% 4.37/4.54  
% 4.37/4.54  # -------------------------------------------------
% 4.37/4.54  # User time                : 3.993 s
% 4.37/4.54  # System time              : 0.215 s
% 4.37/4.54  # Total time               : 4.208 s
% 4.37/4.54  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
