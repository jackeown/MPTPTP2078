%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:18 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  125 (651240 expanded)
%              Number of clauses        :  108 (288133 expanded)
%              Number of leaves         :    8 (181553 expanded)
%              Depth                    :   37
%              Number of atoms          :  125 (651240 expanded)
%              Number of equality atoms :  124 (651239 expanded)
%              Maximal formula depth    :    4 (   1 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(c_0_8,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_10,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k3_xboole_0(X12,X13)) = k4_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_11,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X9,X10,X11] : k4_xboole_0(k4_xboole_0(X9,X10),X11) = k4_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k4_xboole_0(k2_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_15]),c_0_12])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X1) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_12]),c_0_15])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_16])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_17]),c_0_12]),c_0_13])).

cnf(c_0_27,plain,
    ( k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_18]),c_0_18]),c_0_24])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),X1) = k5_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k5_xboole_0(X1,X1)) = k3_xboole_0(X1,k2_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_29]),c_0_16])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_30]),c_0_12]),c_0_26])).

fof(c_0_33,plain,(
    ! [X17,X18] : k2_xboole_0(X17,X18) = k5_xboole_0(X17,k4_xboole_0(X18,X17)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(k5_xboole_0(X1,X1),X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_34])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_36]),c_0_16])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k5_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_29])).

cnf(c_0_41,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_25]),c_0_16])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X1)) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_30]),c_0_35])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X1,X1),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X1),X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_23]),c_0_35]),c_0_43]),c_0_40])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_44]),c_0_12])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_39])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_47]),c_0_16]),c_0_47]),c_0_26])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_18]),c_0_18])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_48]),c_0_35]),c_0_49])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_12])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_48]),c_0_24]),c_0_23]),c_0_16])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_51]),c_0_15]),c_0_35]),c_0_49])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_35]),c_0_49]),c_0_54])).

cnf(c_0_56,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X2)) = k3_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_42]),c_0_50]),c_0_16])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_55]),c_0_35])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_53]),c_0_51]),c_0_16]),c_0_53]),c_0_51]),c_0_35]),c_0_49])).

cnf(c_0_59,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X2,X1)) = k3_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_56])).

cnf(c_0_60,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_57]),c_0_50])).

cnf(c_0_61,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_58])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),X2) = k3_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_58]),c_0_60]),c_0_16]),c_0_16]),c_0_61])).

cnf(c_0_64,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_17]),c_0_16])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_12])).

cnf(c_0_66,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_61])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_65])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X2)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_66])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_67])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_15]),c_0_17]),c_0_16]),c_0_61])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_65])).

cnf(c_0_73,plain,
    ( k3_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_58])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_58]),c_0_26]),c_0_12])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_73]),c_0_12]),c_0_61]),c_0_18]),c_0_12]),c_0_61])).

cnf(c_0_77,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_12]),c_0_71]),c_0_74]),c_0_23])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_57]),c_0_75])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_76]),c_0_74]),c_0_77])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_78]),c_0_20])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_22]),c_0_12])).

cnf(c_0_82,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_55]),c_0_12]),c_0_61])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_84,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X1)),k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_81])).

cnf(c_0_85,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_81]),c_0_16]),c_0_81])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k4_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_81])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_55])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k4_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_89,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_16])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_55])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_58])).

cnf(c_0_92,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_85]),c_0_55]),c_0_86]),c_0_85]),c_0_87]),c_0_17]),c_0_16]),c_0_61])).

cnf(c_0_93,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_25])).

cnf(c_0_94,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_90]),c_0_35])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_39]),c_0_65]),c_0_27]),c_0_18]),c_0_61]),c_0_18]),c_0_76])).

cnf(c_0_96,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_61]),c_0_57])).

cnf(c_0_97,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))) = k3_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_13]),c_0_91]),c_0_18]),c_0_76])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_92,c_0_71])).

cnf(c_0_99,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_16])).

cnf(c_0_100,plain,
    ( k2_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_93]),c_0_55]),c_0_12]),c_0_61])).

cnf(c_0_101,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_58]),c_0_94]),c_0_49])).

cnf(c_0_102,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_77]),c_0_67]),c_0_71]),c_0_12]),c_0_61])).

cnf(c_0_103,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k3_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_96])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X1,X2))) = k3_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_12]),c_0_61]),c_0_97]),c_0_99])).

cnf(c_0_105,plain,
    ( k2_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_100,c_0_58])).

cnf(c_0_106,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_83]),c_0_12])).

cnf(c_0_107,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_25]),c_0_16])).

cnf(c_0_108,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_101]),c_0_15])).

cnf(c_0_109,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_90]),c_0_50])).

cnf(c_0_110,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_102]),c_0_103]),c_0_104])).

cnf(c_0_111,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X2) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_35]),c_0_18]),c_0_57]),c_0_57])).

cnf(c_0_112,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X2))) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_101])).

cnf(c_0_113,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_101]),c_0_109]),c_0_16])).

cnf(c_0_114,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_26]),c_0_112])).

cnf(c_0_115,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_113]),c_0_57]),c_0_57]),c_0_109]),c_0_16]),c_0_23])).

cnf(c_0_116,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_114]),c_0_114])).

fof(c_0_117,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t100_xboole_1])).

cnf(c_0_118,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_119,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

fof(c_0_120,negated_conjecture,(
    k4_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_117])])])).

cnf(c_0_121,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_119]),c_0_12])).

cnf(c_0_122,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_123,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_12]),c_0_23])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:47:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.65  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.47/0.65  # and selection function SelectNewComplexAHP.
% 0.47/0.65  #
% 0.47/0.65  # Preprocessing time       : 0.026 s
% 0.47/0.65  # Presaturation interreduction done
% 0.47/0.65  
% 0.47/0.65  # Proof found!
% 0.47/0.65  # SZS status Theorem
% 0.47/0.65  # SZS output start CNFRefutation
% 0.47/0.65  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.47/0.65  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.47/0.65  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.47/0.65  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.47/0.65  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.47/0.65  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.47/0.65  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.47/0.65  fof(t100_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.47/0.65  fof(c_0_8, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.47/0.65  fof(c_0_9, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.47/0.65  fof(c_0_10, plain, ![X12, X13]:k4_xboole_0(X12,k3_xboole_0(X12,X13))=k4_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.47/0.65  fof(c_0_11, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.47/0.65  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.47/0.65  cnf(c_0_13, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.47/0.65  fof(c_0_14, plain, ![X9, X10, X11]:k4_xboole_0(k4_xboole_0(X9,X10),X11)=k4_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.47/0.65  cnf(c_0_15, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.65  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.65  cnf(c_0_17, plain, (k4_xboole_0(X1,X1)=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.47/0.65  cnf(c_0_18, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.65  fof(c_0_19, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k4_xboole_0(k2_xboole_0(X6,X7),k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.47/0.65  cnf(c_0_20, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_15]), c_0_12])).
% 0.47/0.65  cnf(c_0_21, plain, (k4_xboole_0(X1,X1)=k3_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.47/0.65  cnf(c_0_22, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.47/0.65  cnf(c_0_23, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_12]), c_0_15])).
% 0.47/0.65  cnf(c_0_24, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_16])).
% 0.47/0.65  cnf(c_0_25, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.65  cnf(c_0_26, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_17]), c_0_12]), c_0_13])).
% 0.47/0.65  cnf(c_0_27, plain, (k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.47/0.65  cnf(c_0_28, plain, (k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))=k4_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_18]), c_0_18]), c_0_24])).
% 0.47/0.65  cnf(c_0_29, plain, (k4_xboole_0(k2_xboole_0(X1,X1),X1)=k5_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.47/0.65  cnf(c_0_30, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.47/0.65  cnf(c_0_31, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k5_xboole_0(X1,X1))=k3_xboole_0(X1,k2_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_29]), c_0_16])).
% 0.47/0.65  cnf(c_0_32, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_30]), c_0_12]), c_0_26])).
% 0.47/0.65  fof(c_0_33, plain, ![X17, X18]:k2_xboole_0(X17,X18)=k5_xboole_0(X17,k4_xboole_0(X18,X17)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.47/0.65  cnf(c_0_34, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.47/0.65  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.47/0.65  cnf(c_0_36, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(k5_xboole_0(X1,X1),X1))=k3_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_34])).
% 0.47/0.65  cnf(c_0_37, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_35, c_0_18])).
% 0.47/0.65  cnf(c_0_38, plain, (k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_36]), c_0_16])).
% 0.47/0.65  cnf(c_0_39, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_17])).
% 0.47/0.65  cnf(c_0_40, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(X1,X2))=k4_xboole_0(k5_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_18, c_0_29])).
% 0.47/0.65  cnf(c_0_41, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k4_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_25]), c_0_16])).
% 0.47/0.65  cnf(c_0_42, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X1))=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_30]), c_0_35])).
% 0.47/0.65  cnf(c_0_43, plain, (k3_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_38, c_0_21])).
% 0.47/0.65  cnf(c_0_44, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_18])).
% 0.47/0.65  cnf(c_0_45, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X1,X1),X1))=k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.47/0.65  cnf(c_0_46, plain, (k4_xboole_0(k5_xboole_0(X1,X1),X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_23]), c_0_35]), c_0_43]), c_0_40])).
% 0.47/0.65  cnf(c_0_47, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_44]), c_0_12])).
% 0.47/0.65  cnf(c_0_48, plain, (k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_39])).
% 0.47/0.65  cnf(c_0_49, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_47]), c_0_16]), c_0_47]), c_0_26])).
% 0.47/0.65  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_18]), c_0_18])).
% 0.47/0.65  cnf(c_0_51, plain, (k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_48]), c_0_35]), c_0_49])).
% 0.47/0.65  cnf(c_0_52, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_35, c_0_12])).
% 0.47/0.65  cnf(c_0_53, plain, (k3_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_48]), c_0_24]), c_0_23]), c_0_16])).
% 0.47/0.65  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_51]), c_0_15]), c_0_35]), c_0_49])).
% 0.47/0.65  cnf(c_0_55, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_35]), c_0_49]), c_0_54])).
% 0.47/0.65  cnf(c_0_56, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X2))=k3_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_42]), c_0_50]), c_0_16])).
% 0.47/0.65  cnf(c_0_57, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_55]), c_0_35])).
% 0.47/0.65  cnf(c_0_58, plain, (k4_xboole_0(k1_xboole_0,X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_53]), c_0_51]), c_0_16]), c_0_53]), c_0_51]), c_0_35]), c_0_49])).
% 0.47/0.65  cnf(c_0_59, plain, (k3_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X2,X1))=k3_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_16, c_0_56])).
% 0.47/0.65  cnf(c_0_60, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_57]), c_0_50])).
% 0.47/0.65  cnf(c_0_61, plain, (k3_xboole_0(k1_xboole_0,X1)=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_58])).
% 0.47/0.65  cnf(c_0_62, plain, (k3_xboole_0(k4_xboole_0(X1,X1),X2)=k3_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.47/0.65  cnf(c_0_63, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_58]), c_0_60]), c_0_16]), c_0_16]), c_0_61])).
% 0.47/0.65  cnf(c_0_64, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))=k4_xboole_0(k3_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_17]), c_0_16])).
% 0.47/0.65  cnf(c_0_65, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_18, c_0_12])).
% 0.47/0.65  cnf(c_0_66, plain, (k3_xboole_0(k4_xboole_0(X1,X1),X2)=k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.47/0.65  cnf(c_0_67, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_64, c_0_61])).
% 0.47/0.65  cnf(c_0_68, plain, (k3_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_23, c_0_65])).
% 0.47/0.65  cnf(c_0_69, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X2))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_16, c_0_66])).
% 0.47/0.65  cnf(c_0_70, plain, (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_67])).
% 0.47/0.65  cnf(c_0_71, plain, (k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_15]), c_0_17]), c_0_16]), c_0_61])).
% 0.47/0.65  cnf(c_0_72, plain, (k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_12, c_0_65])).
% 0.47/0.65  cnf(c_0_73, plain, (k3_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)=k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_66, c_0_58])).
% 0.47/0.65  cnf(c_0_74, plain, (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.47/0.65  cnf(c_0_75, plain, (k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_58]), c_0_26]), c_0_12])).
% 0.47/0.65  cnf(c_0_76, plain, (k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_73]), c_0_12]), c_0_61]), c_0_18]), c_0_12]), c_0_61])).
% 0.47/0.65  cnf(c_0_77, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_12]), c_0_71]), c_0_74]), c_0_23])).
% 0.47/0.65  cnf(c_0_78, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k1_xboole_0,X1)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_57]), c_0_75])).
% 0.47/0.65  cnf(c_0_79, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_76]), c_0_74]), c_0_77])).
% 0.47/0.65  cnf(c_0_80, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_78]), c_0_20])).
% 0.47/0.65  cnf(c_0_81, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_22]), c_0_12])).
% 0.47/0.65  cnf(c_0_82, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_55]), c_0_12]), c_0_61])).
% 0.47/0.65  cnf(c_0_83, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_18]), c_0_18]), c_0_18])).
% 0.47/0.65  cnf(c_0_84, plain, (k4_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X1)),k3_xboole_0(X1,X2))=k5_xboole_0(X1,k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_25, c_0_81])).
% 0.47/0.65  cnf(c_0_85, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_81]), c_0_16]), c_0_81])).
% 0.47/0.65  cnf(c_0_86, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k4_xboole_0(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_22, c_0_81])).
% 0.47/0.65  cnf(c_0_87, plain, (k5_xboole_0(X1,X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[c_0_29, c_0_55])).
% 0.47/0.65  cnf(c_0_88, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X1,X2),X3))=k4_xboole_0(k5_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_18, c_0_25])).
% 0.47/0.65  cnf(c_0_89, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_82, c_0_16])).
% 0.47/0.65  cnf(c_0_90, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_83, c_0_55])).
% 0.47/0.65  cnf(c_0_91, plain, (k3_xboole_0(X1,k1_xboole_0)=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_17, c_0_58])).
% 0.47/0.65  cnf(c_0_92, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_85]), c_0_55]), c_0_86]), c_0_85]), c_0_87]), c_0_17]), c_0_16]), c_0_61])).
% 0.47/0.65  cnf(c_0_93, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_25])).
% 0.47/0.65  cnf(c_0_94, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_90]), c_0_35])).
% 0.47/0.65  cnf(c_0_95, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_39]), c_0_65]), c_0_27]), c_0_18]), c_0_61]), c_0_18]), c_0_76])).
% 0.47/0.65  cnf(c_0_96, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_61]), c_0_57])).
% 0.47/0.65  cnf(c_0_97, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)))=k3_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_13]), c_0_91]), c_0_18]), c_0_76])).
% 0.47/0.65  cnf(c_0_98, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_92, c_0_71])).
% 0.47/0.65  cnf(c_0_99, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_77, c_0_16])).
% 0.47/0.65  cnf(c_0_100, plain, (k2_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_93]), c_0_55]), c_0_12]), c_0_61])).
% 0.47/0.65  cnf(c_0_101, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X1)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_58]), c_0_94]), c_0_49])).
% 0.47/0.65  cnf(c_0_102, plain, (k4_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_77]), c_0_67]), c_0_71]), c_0_12]), c_0_61])).
% 0.47/0.65  cnf(c_0_103, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))=k3_xboole_0(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_12, c_0_96])).
% 0.47/0.65  cnf(c_0_104, plain, (k3_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X1,X2)))=k3_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_12]), c_0_61]), c_0_97]), c_0_99])).
% 0.47/0.65  cnf(c_0_105, plain, (k2_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_100, c_0_58])).
% 0.47/0.65  cnf(c_0_106, plain, (k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_83]), c_0_12])).
% 0.47/0.65  cnf(c_0_107, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_25]), c_0_16])).
% 0.47/0.65  cnf(c_0_108, plain, (k5_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(k2_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_101]), c_0_15])).
% 0.47/0.65  cnf(c_0_109, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_90]), c_0_50])).
% 0.47/0.65  cnf(c_0_110, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=k3_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_102]), c_0_103]), c_0_104])).
% 0.47/0.65  cnf(c_0_111, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X2)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_35]), c_0_18]), c_0_57]), c_0_57])).
% 0.47/0.65  cnf(c_0_112, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X2)))=k3_xboole_0(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_106, c_0_101])).
% 0.47/0.65  cnf(c_0_113, plain, (k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=k4_xboole_0(k2_xboole_0(X2,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_101]), c_0_109]), c_0_16])).
% 0.47/0.65  cnf(c_0_114, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_26]), c_0_112])).
% 0.47/0.65  cnf(c_0_115, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_113]), c_0_57]), c_0_57]), c_0_109]), c_0_16]), c_0_23])).
% 0.47/0.65  cnf(c_0_116, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_114]), c_0_114])).
% 0.47/0.65  fof(c_0_117, negated_conjecture, ~(![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t100_xboole_1])).
% 0.47/0.65  cnf(c_0_118, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=k5_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.47/0.65  cnf(c_0_119, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.47/0.65  fof(c_0_120, negated_conjecture, k4_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_117])])])).
% 0.47/0.65  cnf(c_0_121, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_119]), c_0_12])).
% 0.47/0.65  cnf(c_0_122, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.47/0.65  cnf(c_0_123, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_12]), c_0_23])).
% 0.47/0.65  cnf(c_0_124, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_123])]), ['proof']).
% 0.47/0.65  # SZS output end CNFRefutation
% 0.47/0.65  # Proof object total steps             : 125
% 0.47/0.65  # Proof object clause steps            : 108
% 0.47/0.65  # Proof object formula steps           : 17
% 0.47/0.65  # Proof object conjectures             : 5
% 0.47/0.65  # Proof object clause conjectures      : 2
% 0.47/0.65  # Proof object formula conjectures     : 3
% 0.47/0.65  # Proof object initial clauses used    : 8
% 0.47/0.65  # Proof object initial formulas used   : 8
% 0.47/0.65  # Proof object generating inferences   : 89
% 0.47/0.65  # Proof object simplifying inferences  : 145
% 0.47/0.65  # Training examples: 0 positive, 0 negative
% 0.47/0.65  # Parsed axioms                        : 9
% 0.47/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.65  # Initial clauses                      : 9
% 0.47/0.65  # Removed in clause preprocessing      : 0
% 0.47/0.65  # Initial clauses in saturation        : 9
% 0.47/0.65  # Processed clauses                    : 1905
% 0.47/0.65  # ...of these trivial                  : 619
% 0.47/0.65  # ...subsumed                          : 800
% 0.47/0.65  # ...remaining for further processing  : 486
% 0.47/0.65  # Other redundant clauses eliminated   : 0
% 0.47/0.65  # Clauses deleted for lack of memory   : 0
% 0.47/0.65  # Backward-subsumed                    : 1
% 0.47/0.65  # Backward-rewritten                   : 289
% 0.47/0.65  # Generated clauses                    : 37397
% 0.47/0.65  # ...of the previous two non-trivial   : 24173
% 0.47/0.65  # Contextual simplify-reflections      : 0
% 0.47/0.65  # Paramodulations                      : 37397
% 0.47/0.65  # Factorizations                       : 0
% 0.47/0.65  # Equation resolutions                 : 0
% 0.47/0.65  # Propositional unsat checks           : 0
% 0.47/0.65  #    Propositional check models        : 0
% 0.47/0.65  #    Propositional check unsatisfiable : 0
% 0.47/0.65  #    Propositional clauses             : 0
% 0.47/0.65  #    Propositional clauses after purity: 0
% 0.47/0.65  #    Propositional unsat core size     : 0
% 0.47/0.65  #    Propositional preprocessing time  : 0.000
% 0.47/0.65  #    Propositional encoding time       : 0.000
% 0.47/0.65  #    Propositional solver time         : 0.000
% 0.47/0.65  #    Success case prop preproc time    : 0.000
% 0.47/0.65  #    Success case prop encoding time   : 0.000
% 0.47/0.65  #    Success case prop solver time     : 0.000
% 0.47/0.65  # Current number of processed clauses  : 187
% 0.47/0.65  #    Positive orientable unit clauses  : 178
% 0.47/0.65  #    Positive unorientable unit clauses: 9
% 0.47/0.65  #    Negative unit clauses             : 0
% 0.47/0.65  #    Non-unit-clauses                  : 0
% 0.47/0.65  # Current number of unprocessed clauses: 21219
% 0.47/0.65  # ...number of literals in the above   : 21219
% 0.47/0.65  # Current number of archived formulas  : 0
% 0.47/0.65  # Current number of archived clauses   : 299
% 0.47/0.65  # Clause-clause subsumption calls (NU) : 0
% 0.47/0.65  # Rec. Clause-clause subsumption calls : 0
% 0.47/0.65  # Non-unit clause-clause subsumptions  : 0
% 0.47/0.65  # Unit Clause-clause subsumption calls : 208
% 0.47/0.65  # Rewrite failures with RHS unbound    : 0
% 0.47/0.65  # BW rewrite match attempts            : 1487
% 0.47/0.65  # BW rewrite match successes           : 521
% 0.47/0.65  # Condensation attempts                : 0
% 0.47/0.65  # Condensation successes               : 0
% 0.47/0.65  # Termbank termtop insertions          : 445516
% 0.47/0.65  
% 0.47/0.65  # -------------------------------------------------
% 0.47/0.65  # User time                : 0.289 s
% 0.47/0.65  # System time              : 0.019 s
% 0.47/0.65  # Total time               : 0.308 s
% 0.47/0.65  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
