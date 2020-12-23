%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:11 EST 2020

% Result     : Theorem 1.05s
% Output     : CNFRefutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  111 (108326 expanded)
%              Number of clauses        :   88 (51361 expanded)
%              Number of leaves         :   11 (28482 expanded)
%              Depth                    :   39
%              Number of atoms          :  117 (108366 expanded)
%              Number of equality atoms :  100 (108289 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t98_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(c_0_11,plain,(
    ! [X25,X26] : k2_xboole_0(X25,X26) = k5_xboole_0(k5_xboole_0(X25,X26),k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_12,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X12,X13)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X9,X10,X11] : k4_xboole_0(k4_xboole_0(X9,X10),X11) = k4_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X22,X23,X24] : k5_xboole_0(k5_xboole_0(X22,X23),X24) = k5_xboole_0(X22,k5_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_18])).

fof(c_0_24,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_25,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X16] : k5_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_30,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_18]),c_0_18])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_22]),c_0_22])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_36]),c_0_31])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_31]),c_0_36]),c_0_38]),c_0_34]),c_0_36]),c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_37]),c_0_27])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_27]),c_0_27]),c_0_41]),c_0_27])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_41])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_42]),c_0_36]),c_0_34]),c_0_35])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_36]),c_0_31])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,X1))) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_22])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_41]),c_0_47])).

fof(c_0_51,plain,(
    ! [X17,X18] :
      ( ( ~ r1_xboole_0(X17,X18)
        | k4_xboole_0(X17,X18) = X17 )
      & ( k4_xboole_0(X17,X18) != X17
        | r1_xboole_0(X17,X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_48]),c_0_31]),c_0_22]),c_0_49]),c_0_50]),c_0_35])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_52])).

cnf(c_0_55,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_42])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4))),X4),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X4)),X2),X4) ),
    inference(spm,[status(thm)],[c_0_54,c_0_54])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_44]),c_0_31])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4)),X3) = k4_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X2,X3),X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_43]),c_0_41]),c_0_44]),c_0_34]),c_0_35])).

cnf(c_0_59,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4),X3),X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X4)) = k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_57]),c_0_36]),c_0_34])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X2))) = k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X3,X2),X4))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_54]),c_0_58])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X4))),X3),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X1,X3),X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_61])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_56])).

cnf(c_0_66,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X4))),X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_47])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))),X3) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_60]),c_0_34])).

cnf(c_0_68,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_38]),c_0_57])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_65])).

cnf(c_0_70,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_44]),c_0_38])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,X4)))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_69]),c_0_31])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4))),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_52])).

cnf(c_0_74,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X3,X2),X4))),k4_xboole_0(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_61])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,X2))),X3) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_35])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_73])).

cnf(c_0_77,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X4,X2))),k4_xboole_0(X4,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_22]),c_0_34])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_76])).

cnf(c_0_79,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,X4)),X3)),k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_52]),c_0_38])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_35]),c_0_22])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_83,plain,
    ( r1_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_31]),c_0_44]),c_0_31]),c_0_81])).

cnf(c_0_84,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))),X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_40]),c_0_22])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_84])).

cnf(c_0_87,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_44]),c_0_31]),c_0_81])).

cnf(c_0_88,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1)))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_85]),c_0_22]),c_0_22])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_86]),c_0_31]),c_0_36]),c_0_38]),c_0_34]),c_0_87]),c_0_44]),c_0_31]),c_0_22]),c_0_22]),c_0_88]),c_0_81])).

cnf(c_0_90,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X1,X2))) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_57]),c_0_41]),c_0_44]),c_0_34]),c_0_42]),c_0_41]),c_0_44]),c_0_34]),c_0_35])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),X3))) = k5_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_89]),c_0_22])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X4,X1))))) = k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_88]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,X1)))) = k5_xboole_0(X3,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_49]),c_0_22]),c_0_22])).

cnf(c_0_94,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X2)),X3)) = k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_90]),c_0_22])).

cnf(c_0_95,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X1,X2)))) = k5_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_91]),c_0_22]),c_0_22]),c_0_22]),c_0_22]),c_0_92]),c_0_93])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_81]),c_0_89])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X2)),X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_96]),c_0_22])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X3),X2))) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_97]),c_0_81]),c_0_89])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,X2))) = k5_xboole_0(k4_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_57])).

fof(c_0_100,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t98_xboole_1])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X2),X3)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_69]),c_0_34]),c_0_35])).

fof(c_0_102,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_100])])])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_101,c_0_31])).

cnf(c_0_104,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_105,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_103,c_0_42])).

cnf(c_0_106,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_104,c_0_18])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_35]),c_0_22])).

cnf(c_0_109,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_107])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.05/1.26  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 1.05/1.26  # and selection function SelectNewComplexAHP.
% 1.05/1.26  #
% 1.05/1.26  # Preprocessing time       : 0.027 s
% 1.05/1.26  # Presaturation interreduction done
% 1.05/1.26  
% 1.05/1.26  # Proof found!
% 1.05/1.26  # SZS status Theorem
% 1.05/1.26  # SZS output start CNFRefutation
% 1.05/1.26  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 1.05/1.26  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.05/1.26  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.05/1.26  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.05/1.26  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 1.05/1.26  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.05/1.26  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.05/1.26  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.05/1.26  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.05/1.26  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.05/1.26  fof(t98_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.05/1.26  fof(c_0_11, plain, ![X25, X26]:k2_xboole_0(X25,X26)=k5_xboole_0(k5_xboole_0(X25,X26),k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 1.05/1.26  fof(c_0_12, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.05/1.26  fof(c_0_13, plain, ![X12, X13]:k4_xboole_0(X12,k2_xboole_0(X12,X13))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 1.05/1.26  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.05/1.26  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.05/1.26  fof(c_0_16, plain, ![X9, X10, X11]:k4_xboole_0(k4_xboole_0(X9,X10),X11)=k4_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.05/1.26  cnf(c_0_17, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.05/1.26  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 1.05/1.26  fof(c_0_19, plain, ![X22, X23, X24]:k5_xboole_0(k5_xboole_0(X22,X23),X24)=k5_xboole_0(X22,k5_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 1.05/1.26  cnf(c_0_20, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.05/1.26  cnf(c_0_21, plain, (k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 1.05/1.26  cnf(c_0_22, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.05/1.26  cnf(c_0_23, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[c_0_20, c_0_18])).
% 1.05/1.26  fof(c_0_24, plain, ![X6, X7]:k2_xboole_0(X6,k4_xboole_0(X7,X6))=k2_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.05/1.26  fof(c_0_25, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.05/1.26  cnf(c_0_26, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 1.05/1.26  cnf(c_0_27, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_23, c_0_22])).
% 1.05/1.26  cnf(c_0_28, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.05/1.26  fof(c_0_29, plain, ![X16]:k5_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t5_boole])).
% 1.05/1.26  fof(c_0_30, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 1.05/1.26  cnf(c_0_31, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.05/1.26  cnf(c_0_32, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 1.05/1.26  cnf(c_0_33, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_18]), c_0_18])).
% 1.05/1.26  cnf(c_0_34, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.05/1.26  cnf(c_0_35, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.05/1.26  cnf(c_0_36, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.05/1.26  cnf(c_0_37, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_22]), c_0_22])).
% 1.05/1.26  cnf(c_0_38, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.05/1.26  cnf(c_0_39, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_36]), c_0_31])).
% 1.05/1.26  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_31]), c_0_36]), c_0_38]), c_0_34]), c_0_36]), c_0_31])).
% 1.05/1.26  cnf(c_0_41, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_37]), c_0_27])).
% 1.05/1.26  cnf(c_0_42, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 1.05/1.26  cnf(c_0_43, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,X2))=k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_27]), c_0_27]), c_0_41]), c_0_27])).
% 1.05/1.26  cnf(c_0_44, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_41])).
% 1.05/1.26  cnf(c_0_45, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)=k4_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_42]), c_0_36]), c_0_34]), c_0_35])).
% 1.05/1.26  cnf(c_0_46, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_22])).
% 1.05/1.26  cnf(c_0_47, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_36]), c_0_31])).
% 1.05/1.26  cnf(c_0_48, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.05/1.26  cnf(c_0_49, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,X1)))=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_22])).
% 1.05/1.26  cnf(c_0_50, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X2,k4_xboole_0(X3,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_41]), c_0_47])).
% 1.05/1.26  fof(c_0_51, plain, ![X17, X18]:((~r1_xboole_0(X17,X18)|k4_xboole_0(X17,X18)=X17)&(k4_xboole_0(X17,X18)!=X17|r1_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 1.05/1.26  cnf(c_0_52, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_48]), c_0_31]), c_0_22]), c_0_49]), c_0_50]), c_0_35])).
% 1.05/1.26  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.05/1.26  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)=k4_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[c_0_45, c_0_52])).
% 1.05/1.26  cnf(c_0_55, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_53, c_0_42])).
% 1.05/1.26  cnf(c_0_56, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4))),X4),X3)=k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X4)),X2),X4)), inference(spm,[status(thm)],[c_0_54, c_0_54])).
% 1.05/1.26  cnf(c_0_57, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_44]), c_0_31])).
% 1.05/1.26  cnf(c_0_58, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4)),X3)=k4_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X2,X3),X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_43]), c_0_41]), c_0_44]), c_0_34]), c_0_35])).
% 1.05/1.26  cnf(c_0_59, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4),X3),X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.05/1.26  cnf(c_0_60, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X4))=k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_57]), c_0_36]), c_0_34])).
% 1.05/1.26  cnf(c_0_61, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X2)))=k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X3,X2),X4)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_54]), c_0_58])).
% 1.05/1.26  cnf(c_0_62, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_27])).
% 1.05/1.26  cnf(c_0_63, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X4))),X3),X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.05/1.26  cnf(c_0_64, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X1,X3),X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_61])).
% 1.05/1.26  cnf(c_0_65, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_56])).
% 1.05/1.26  cnf(c_0_66, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X4))),X3)), inference(spm,[status(thm)],[c_0_63, c_0_47])).
% 1.05/1.26  cnf(c_0_67, plain, (k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))),X3)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_60]), c_0_34])).
% 1.05/1.26  cnf(c_0_68, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_38]), c_0_57])).
% 1.05/1.26  cnf(c_0_69, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_65])).
% 1.05/1.26  cnf(c_0_70, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_44]), c_0_38])).
% 1.05/1.26  cnf(c_0_71, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,X4))))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_69]), c_0_31])).
% 1.05/1.26  cnf(c_0_72, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4))),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.05/1.26  cnf(c_0_73, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_52])).
% 1.05/1.26  cnf(c_0_74, plain, (r1_xboole_0(k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X3,X2),X4))),k4_xboole_0(X3,X4))), inference(spm,[status(thm)],[c_0_72, c_0_61])).
% 1.05/1.26  cnf(c_0_75, plain, (k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,X2))),X3)=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_35])).
% 1.05/1.26  cnf(c_0_76, plain, (k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_73])).
% 1.05/1.26  cnf(c_0_77, plain, (r1_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X4,X2))),k4_xboole_0(X4,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_22]), c_0_34])).
% 1.05/1.26  cnf(c_0_78, plain, (k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_76])).
% 1.05/1.26  cnf(c_0_79, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,X4)),X3)),k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_52]), c_0_38])).
% 1.05/1.26  cnf(c_0_80, plain, (k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 1.05/1.26  cnf(c_0_81, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_35]), c_0_22])).
% 1.05/1.26  cnf(c_0_82, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.05/1.26  cnf(c_0_83, plain, (r1_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_31]), c_0_44]), c_0_31]), c_0_81])).
% 1.05/1.26  cnf(c_0_84, plain, (k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))),X2))=X1), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 1.05/1.26  cnf(c_0_85, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_40]), c_0_22])).
% 1.05/1.26  cnf(c_0_86, plain, (k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_84])).
% 1.05/1.26  cnf(c_0_87, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_44]), c_0_31]), c_0_81])).
% 1.05/1.26  cnf(c_0_88, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1))))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_85]), c_0_22]), c_0_22])).
% 1.05/1.26  cnf(c_0_89, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_86]), c_0_31]), c_0_36]), c_0_38]), c_0_34]), c_0_87]), c_0_44]), c_0_31]), c_0_22]), c_0_22]), c_0_88]), c_0_81])).
% 1.05/1.26  cnf(c_0_90, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X1,X2)))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_57]), c_0_41]), c_0_44]), c_0_34]), c_0_42]), c_0_41]), c_0_44]), c_0_34]), c_0_35])).
% 1.05/1.26  cnf(c_0_91, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),X3)))=k5_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_89]), c_0_22])).
% 1.05/1.26  cnf(c_0_92, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X4,X1)))))=k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_88]), c_0_22]), c_0_22]), c_0_22])).
% 1.05/1.26  cnf(c_0_93, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,X1))))=k5_xboole_0(X3,k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_49]), c_0_22]), c_0_22])).
% 1.05/1.26  cnf(c_0_94, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X2)),X3))=k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_90]), c_0_22])).
% 1.05/1.26  cnf(c_0_95, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X1,X2))))=k5_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_91]), c_0_22]), c_0_22]), c_0_22]), c_0_22]), c_0_92]), c_0_93])).
% 1.05/1.26  cnf(c_0_96, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2)))=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_81]), c_0_89])).
% 1.05/1.26  cnf(c_0_97, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X2)),X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_96]), c_0_22])).
% 1.05/1.26  cnf(c_0_98, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X3),X2)))=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_97]), c_0_81]), c_0_89])).
% 1.05/1.26  cnf(c_0_99, plain, (k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,X2)))=k5_xboole_0(k4_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_98, c_0_57])).
% 1.05/1.26  fof(c_0_100, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t98_xboole_1])).
% 1.05/1.26  cnf(c_0_101, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X2),X3))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_69]), c_0_34]), c_0_35])).
% 1.05/1.26  fof(c_0_102, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_100])])])).
% 1.05/1.26  cnf(c_0_103, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_101, c_0_31])).
% 1.05/1.26  cnf(c_0_104, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.05/1.26  cnf(c_0_105, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X2))))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_103, c_0_42])).
% 1.05/1.26  cnf(c_0_106, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_104, c_0_18])).
% 1.05/1.26  cnf(c_0_107, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_37, c_0_105])).
% 1.05/1.26  cnf(c_0_108, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))))!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_35]), c_0_22])).
% 1.05/1.26  cnf(c_0_109, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X1))))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_81, c_0_107])).
% 1.05/1.26  cnf(c_0_110, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_109])]), ['proof']).
% 1.05/1.26  # SZS output end CNFRefutation
% 1.05/1.26  # Proof object total steps             : 111
% 1.05/1.26  # Proof object clause steps            : 88
% 1.05/1.26  # Proof object formula steps           : 23
% 1.05/1.26  # Proof object conjectures             : 7
% 1.05/1.26  # Proof object clause conjectures      : 4
% 1.05/1.26  # Proof object formula conjectures     : 3
% 1.05/1.26  # Proof object initial clauses used    : 12
% 1.05/1.26  # Proof object initial formulas used   : 11
% 1.05/1.26  # Proof object generating inferences   : 62
% 1.05/1.26  # Proof object simplifying inferences  : 107
% 1.05/1.26  # Training examples: 0 positive, 0 negative
% 1.05/1.26  # Parsed axioms                        : 12
% 1.05/1.26  # Removed by relevancy pruning/SinE    : 0
% 1.05/1.26  # Initial clauses                      : 13
% 1.05/1.26  # Removed in clause preprocessing      : 2
% 1.05/1.26  # Initial clauses in saturation        : 11
% 1.05/1.26  # Processed clauses                    : 1829
% 1.05/1.26  # ...of these trivial                  : 771
% 1.05/1.26  # ...subsumed                          : 653
% 1.05/1.26  # ...remaining for further processing  : 405
% 1.05/1.26  # Other redundant clauses eliminated   : 0
% 1.05/1.26  # Clauses deleted for lack of memory   : 0
% 1.05/1.26  # Backward-subsumed                    : 1
% 1.05/1.26  # Backward-rewritten                   : 74
% 1.05/1.26  # Generated clauses                    : 157896
% 1.05/1.26  # ...of the previous two non-trivial   : 59120
% 1.05/1.26  # Contextual simplify-reflections      : 0
% 1.05/1.26  # Paramodulations                      : 157885
% 1.05/1.26  # Factorizations                       : 0
% 1.05/1.26  # Equation resolutions                 : 11
% 1.05/1.26  # Propositional unsat checks           : 0
% 1.05/1.26  #    Propositional check models        : 0
% 1.05/1.26  #    Propositional check unsatisfiable : 0
% 1.05/1.26  #    Propositional clauses             : 0
% 1.05/1.26  #    Propositional clauses after purity: 0
% 1.05/1.26  #    Propositional unsat core size     : 0
% 1.05/1.26  #    Propositional preprocessing time  : 0.000
% 1.05/1.26  #    Propositional encoding time       : 0.000
% 1.05/1.26  #    Propositional solver time         : 0.000
% 1.05/1.26  #    Success case prop preproc time    : 0.000
% 1.05/1.26  #    Success case prop encoding time   : 0.000
% 1.05/1.26  #    Success case prop solver time     : 0.000
% 1.05/1.26  # Current number of processed clauses  : 319
% 1.05/1.26  #    Positive orientable unit clauses  : 292
% 1.05/1.26  #    Positive unorientable unit clauses: 4
% 1.05/1.26  #    Negative unit clauses             : 0
% 1.05/1.26  #    Non-unit-clauses                  : 23
% 1.05/1.26  # Current number of unprocessed clauses: 57151
% 1.05/1.26  # ...number of literals in the above   : 58850
% 1.05/1.26  # Current number of archived formulas  : 0
% 1.05/1.26  # Current number of archived clauses   : 88
% 1.05/1.26  # Clause-clause subsumption calls (NU) : 472
% 1.05/1.26  # Rec. Clause-clause subsumption calls : 472
% 1.05/1.26  # Non-unit clause-clause subsumptions  : 110
% 1.05/1.26  # Unit Clause-clause subsumption calls : 140
% 1.05/1.26  # Rewrite failures with RHS unbound    : 0
% 1.05/1.26  # BW rewrite match attempts            : 5018
% 1.05/1.26  # BW rewrite match successes           : 102
% 1.05/1.26  # Condensation attempts                : 0
% 1.05/1.26  # Condensation successes               : 0
% 1.05/1.26  # Termbank termtop insertions          : 1954512
% 1.05/1.26  
% 1.05/1.26  # -------------------------------------------------
% 1.05/1.26  # User time                : 0.832 s
% 1.05/1.26  # System time              : 0.065 s
% 1.05/1.26  # Total time               : 0.897 s
% 1.05/1.26  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
