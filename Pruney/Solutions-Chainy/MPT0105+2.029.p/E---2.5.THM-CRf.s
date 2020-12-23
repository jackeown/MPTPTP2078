%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:12 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  110 (78864 expanded)
%              Number of clauses        :   83 (36779 expanded)
%              Number of leaves         :   13 (21042 expanded)
%              Depth                    :   26
%              Number of atoms          :  121 (79614 expanded)
%              Number of equality atoms :   93 (78684 expanded)
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

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t87_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t98_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(c_0_13,plain,(
    ! [X29,X30] : k2_xboole_0(X29,X30) = k5_xboole_0(k5_xboole_0(X29,X30),k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_14,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X14,X15),X16) = k4_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X26,X27,X28] : k5_xboole_0(k5_xboole_0(X26,X27),X28) = k5_xboole_0(X26,k5_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X13) = k4_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ( ~ r1_xboole_0(X21,X22)
        | k4_xboole_0(X21,X22) = X21 )
      & ( k4_xboole_0(X21,X22) != X21
        | r1_xboole_0(X21,X22) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_20]),c_0_20])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_25]),c_0_25])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_20])).

fof(c_0_38,plain,(
    ! [X20] : k5_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_30])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_25])).

fof(c_0_42,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_xboole_0(X23,X24)
      | k2_xboole_0(k4_xboole_0(X25,X23),X24) = k4_xboole_0(k2_xboole_0(X25,X24),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).

fof(c_0_43,plain,(
    ! [X19] : k4_xboole_0(k1_xboole_0,X19) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_44,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_40]),c_0_30])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4) ),
    inference(spm,[status(thm)],[c_0_40,c_0_40])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_45])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X2,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_35])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X3,X2),k4_xboole_0(X3,k4_xboole_0(X3,X2))),X1) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X3,X1),X2),k4_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(k4_xboole_0(X3,X1),X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_20]),c_0_20])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_50]),c_0_50]),c_0_45]),c_0_51])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X2),X1))),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_40]),c_0_35])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_41]),c_0_51]),c_0_51]),c_0_52])).

cnf(c_0_59,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,X2)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)))) = k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X3)))),X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_25]),c_0_25])).

cnf(c_0_61,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_56])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X1),X1),X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_35]),c_0_58])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X3,X3)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_47])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)))) = k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X3)))),k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_56]),c_0_25]),c_0_52]),c_0_56]),c_0_25]),c_0_52])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X2,X3),X2)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_35]),c_0_40])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X2,X2),X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_62]),c_0_40]),c_0_35])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_40])).

cnf(c_0_68,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X3)),k4_xboole_0(k4_xboole_0(X3,X3),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_54]),c_0_40]),c_0_35]),c_0_40])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k4_xboole_0(X2,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_50]),c_0_50]),c_0_50]),c_0_45]),c_0_50]),c_0_50]),c_0_45])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),X2) = k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X2),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_62]),c_0_66]),c_0_58])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_35])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k5_xboole_0(k1_xboole_0,X1),k4_xboole_0(k4_xboole_0(X1,X1),X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_69])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),k5_xboole_0(k4_xboole_0(X2,X2),X2)) = k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X2),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_70]),c_0_40]),c_0_35]),c_0_71]),c_0_70]),c_0_40]),c_0_35])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_75,plain,
    ( r1_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_66])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_50]),c_0_50]),c_0_45])).

cnf(c_0_77,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_79,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(k1_xboole_0,X3),X2))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_56])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_78]),c_0_45])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_69]),c_0_56]),c_0_76]),c_0_45]),c_0_25]),c_0_56]),c_0_56]),c_0_40])).

cnf(c_0_82,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(X2,X2),X2)),X2))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_66])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_80]),c_0_51])).

cnf(c_0_84,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_30]),c_0_40]),c_0_30])).

cnf(c_0_85,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_47])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_69]),c_0_52]),c_0_56])).

cnf(c_0_87,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_83]),c_0_40]),c_0_35]),c_0_71]),c_0_78]),c_0_51])).

cnf(c_0_88,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_35]),c_0_40])).

cnf(c_0_89,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),X3)),X2) = k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86]),c_0_86])).

cnf(c_0_90,plain,
    ( r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_84]),c_0_35]),c_0_40])).

cnf(c_0_91,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),X3))) = X1 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_92,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X2),X2))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_86])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_84]),c_0_35]),c_0_40])).

cnf(c_0_94,plain,
    ( r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3),X2)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_56])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_93])).

fof(c_0_97,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t98_xboole_1])).

cnf(c_0_98,plain,
    ( r1_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,X1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_96])).

fof(c_0_100,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_97])])])).

cnf(c_0_101,plain,
    ( r1_xboole_0(X1,k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_102,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_103,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_93])).

cnf(c_0_104,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_101]),c_0_56])).

cnf(c_0_105,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_102,c_0_20])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_104]),c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_105,c_0_25])).

cnf(c_0_108,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.54/2.73  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 2.54/2.73  # and selection function SelectNewComplexAHP.
% 2.54/2.73  #
% 2.54/2.73  # Preprocessing time       : 0.027 s
% 2.54/2.73  # Presaturation interreduction done
% 2.54/2.73  
% 2.54/2.73  # Proof found!
% 2.54/2.73  # SZS status Theorem
% 2.54/2.73  # SZS output start CNFRefutation
% 2.54/2.73  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 2.54/2.73  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.54/2.73  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.54/2.73  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.54/2.73  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.54/2.73  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.54/2.73  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.54/2.73  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.54/2.73  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.54/2.73  fof(t87_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 2.54/2.73  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.54/2.73  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.54/2.73  fof(t98_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.54/2.73  fof(c_0_13, plain, ![X29, X30]:k2_xboole_0(X29,X30)=k5_xboole_0(k5_xboole_0(X29,X30),k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 2.54/2.73  fof(c_0_14, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.54/2.73  fof(c_0_15, plain, ![X14, X15, X16]:k4_xboole_0(k4_xboole_0(X14,X15),X16)=k4_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 2.54/2.73  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.54/2.73  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.54/2.73  fof(c_0_18, plain, ![X4]:k2_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 2.54/2.73  cnf(c_0_19, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.54/2.73  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 2.54/2.73  fof(c_0_21, plain, ![X26, X27, X28]:k5_xboole_0(k5_xboole_0(X26,X27),X28)=k5_xboole_0(X26,k5_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 2.54/2.73  cnf(c_0_22, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.54/2.73  fof(c_0_23, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 2.54/2.73  cnf(c_0_24, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 2.54/2.73  cnf(c_0_25, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.54/2.73  cnf(c_0_26, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[c_0_22, c_0_20])).
% 2.54/2.73  cnf(c_0_27, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.54/2.73  fof(c_0_28, plain, ![X12, X13]:k4_xboole_0(k2_xboole_0(X12,X13),X13)=k4_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 2.54/2.73  fof(c_0_29, plain, ![X21, X22]:((~r1_xboole_0(X21,X22)|k4_xboole_0(X21,X22)=X21)&(k4_xboole_0(X21,X22)!=X21|r1_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 2.54/2.73  cnf(c_0_30, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 2.54/2.73  cnf(c_0_31, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X1))))=X1), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 2.54/2.73  cnf(c_0_32, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_20]), c_0_20])).
% 2.54/2.73  cnf(c_0_33, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.54/2.73  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.54/2.73  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 2.54/2.73  cnf(c_0_36, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_25]), c_0_25])).
% 2.54/2.73  cnf(c_0_37, plain, (k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_20])).
% 2.54/2.73  fof(c_0_38, plain, ![X20]:k5_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t5_boole])).
% 2.54/2.73  cnf(c_0_39, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 2.54/2.73  cnf(c_0_40, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_36]), c_0_30])).
% 2.54/2.73  cnf(c_0_41, plain, (k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_25])).
% 2.54/2.73  fof(c_0_42, plain, ![X23, X24, X25]:(~r1_xboole_0(X23,X24)|k2_xboole_0(k4_xboole_0(X25,X23),X24)=k4_xboole_0(k2_xboole_0(X25,X24),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).
% 2.54/2.73  fof(c_0_43, plain, ![X19]:k4_xboole_0(k1_xboole_0,X19)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 2.54/2.73  fof(c_0_44, plain, ![X11]:k4_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.54/2.73  cnf(c_0_45, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.54/2.73  cnf(c_0_46, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 2.54/2.73  cnf(c_0_47, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_40]), c_0_30])).
% 2.54/2.73  cnf(c_0_48, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,k4_xboole_0(X3,X2)))=k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4)), inference(spm,[status(thm)],[c_0_40, c_0_40])).
% 2.54/2.73  cnf(c_0_49, plain, (k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.54/2.73  cnf(c_0_50, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.54/2.73  cnf(c_0_51, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.54/2.73  cnf(c_0_52, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_45])).
% 2.54/2.73  cnf(c_0_53, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 2.54/2.73  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X2,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_48, c_0_35])).
% 2.54/2.73  cnf(c_0_55, plain, (k4_xboole_0(k5_xboole_0(k5_xboole_0(X3,X2),k4_xboole_0(X3,k4_xboole_0(X3,X2))),X1)=k5_xboole_0(k5_xboole_0(k4_xboole_0(X3,X1),X2),k4_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(k4_xboole_0(X3,X1),X2)))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_20]), c_0_20])).
% 2.54/2.73  cnf(c_0_56, plain, (k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_50]), c_0_50]), c_0_45]), c_0_51])).
% 2.54/2.73  cnf(c_0_57, plain, (k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X2),X1))),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_40]), c_0_35])).
% 2.54/2.73  cnf(c_0_58, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_41]), c_0_51]), c_0_51]), c_0_52])).
% 2.54/2.73  cnf(c_0_59, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,X2))))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 2.54/2.73  cnf(c_0_60, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))))=k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X3)))),X2)|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_25]), c_0_25])).
% 2.54/2.73  cnf(c_0_61, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_39, c_0_56])).
% 2.54/2.73  cnf(c_0_62, plain, (k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X1),X1),X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_35]), c_0_58])).
% 2.54/2.73  cnf(c_0_63, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X3,X3))))), inference(spm,[status(thm)],[c_0_59, c_0_47])).
% 2.54/2.73  cnf(c_0_64, plain, (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3))))=k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X3)))),k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_56]), c_0_25]), c_0_52]), c_0_56]), c_0_25]), c_0_52])).
% 2.54/2.73  cnf(c_0_65, plain, (k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X2,X3),X2))))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_35]), c_0_40])).
% 2.54/2.73  cnf(c_0_66, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X2,X2),X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_62]), c_0_40]), c_0_35])).
% 2.54/2.73  cnf(c_0_67, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_40])).
% 2.54/2.73  cnf(c_0_68, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X3)),k4_xboole_0(k4_xboole_0(X3,X3),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_54]), c_0_40]), c_0_35]), c_0_40])).
% 2.54/2.73  cnf(c_0_69, plain, (k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k4_xboole_0(X2,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_50]), c_0_50]), c_0_50]), c_0_45]), c_0_50]), c_0_50]), c_0_45])).
% 2.54/2.73  cnf(c_0_70, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),X2)=k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X2),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_62]), c_0_66]), c_0_58])).
% 2.54/2.73  cnf(c_0_71, plain, (k5_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_67, c_0_35])).
% 2.54/2.73  cnf(c_0_72, plain, (r1_xboole_0(k5_xboole_0(k1_xboole_0,X1),k4_xboole_0(k4_xboole_0(X1,X1),X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_69])).
% 2.54/2.73  cnf(c_0_73, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),k5_xboole_0(k4_xboole_0(X2,X2),X2))=k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X2),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_70]), c_0_40]), c_0_35]), c_0_71]), c_0_70]), c_0_40]), c_0_35])).
% 2.54/2.73  cnf(c_0_74, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.54/2.73  cnf(c_0_75, plain, (r1_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_66])).
% 2.54/2.73  cnf(c_0_76, plain, (k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_50]), c_0_50]), c_0_45])).
% 2.54/2.73  cnf(c_0_77, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X2,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_53, c_0_40])).
% 2.54/2.73  cnf(c_0_78, plain, (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 2.54/2.73  cnf(c_0_79, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(k1_xboole_0,X3),X2)))), inference(spm,[status(thm)],[c_0_77, c_0_56])).
% 2.54/2.73  cnf(c_0_80, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_78]), c_0_45])).
% 2.54/2.73  cnf(c_0_81, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_69]), c_0_56]), c_0_76]), c_0_45]), c_0_25]), c_0_56]), c_0_56]), c_0_40])).
% 2.54/2.73  cnf(c_0_82, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(X2,X2),X2)),X2)))), inference(spm,[status(thm)],[c_0_79, c_0_66])).
% 2.54/2.73  cnf(c_0_83, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_80]), c_0_51])).
% 2.54/2.73  cnf(c_0_84, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,X2))=k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_30]), c_0_30]), c_0_40]), c_0_30])).
% 2.54/2.73  cnf(c_0_85, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3),X2)=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_40, c_0_47])).
% 2.54/2.73  cnf(c_0_86, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)=k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_69]), c_0_52]), c_0_56])).
% 2.54/2.73  cnf(c_0_87, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_83]), c_0_40]), c_0_35]), c_0_71]), c_0_78]), c_0_51])).
% 2.54/2.73  cnf(c_0_88, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_35]), c_0_40])).
% 2.54/2.73  cnf(c_0_89, plain, (k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),X3)),X2)=k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X3),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86]), c_0_86])).
% 2.54/2.73  cnf(c_0_90, plain, (r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_84]), c_0_35]), c_0_40])).
% 2.54/2.73  cnf(c_0_91, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),X3)))=X1), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 2.54/2.73  cnf(c_0_92, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X2),X2)))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X2)))), inference(spm,[status(thm)],[c_0_40, c_0_86])).
% 2.54/2.73  cnf(c_0_93, plain, (k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_84]), c_0_35]), c_0_40])).
% 2.54/2.73  cnf(c_0_94, plain, (r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3),X2))), inference(spm,[status(thm)],[c_0_90, c_0_56])).
% 2.54/2.73  cnf(c_0_95, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X2)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 2.54/2.73  cnf(c_0_96, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_81, c_0_93])).
% 2.54/2.73  fof(c_0_97, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t98_xboole_1])).
% 2.54/2.73  cnf(c_0_98, plain, (r1_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 2.54/2.73  cnf(c_0_99, plain, (k4_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,X1))=k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_69, c_0_96])).
% 2.54/2.73  fof(c_0_100, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_97])])])).
% 2.54/2.73  cnf(c_0_101, plain, (r1_xboole_0(X1,k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))))), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 2.54/2.73  cnf(c_0_102, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 2.54/2.73  cnf(c_0_103, plain, (k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_93])).
% 2.54/2.73  cnf(c_0_104, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_101]), c_0_56])).
% 2.54/2.73  cnf(c_0_105, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_102, c_0_20])).
% 2.54/2.73  cnf(c_0_106, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_104]), c_0_104])).
% 2.54/2.73  cnf(c_0_107, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))))!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_105, c_0_25])).
% 2.54/2.73  cnf(c_0_108, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_36, c_0_106])).
% 2.54/2.73  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108])]), ['proof']).
% 2.54/2.73  # SZS output end CNFRefutation
% 2.54/2.73  # Proof object total steps             : 110
% 2.54/2.73  # Proof object clause steps            : 83
% 2.54/2.73  # Proof object formula steps           : 27
% 2.54/2.73  # Proof object conjectures             : 7
% 2.54/2.73  # Proof object clause conjectures      : 4
% 2.54/2.73  # Proof object formula conjectures     : 3
% 2.54/2.73  # Proof object initial clauses used    : 14
% 2.54/2.73  # Proof object initial formulas used   : 13
% 2.54/2.73  # Proof object generating inferences   : 52
% 2.54/2.73  # Proof object simplifying inferences  : 95
% 2.54/2.73  # Training examples: 0 positive, 0 negative
% 2.54/2.73  # Parsed axioms                        : 15
% 2.54/2.73  # Removed by relevancy pruning/SinE    : 0
% 2.54/2.73  # Initial clauses                      : 17
% 2.54/2.73  # Removed in clause preprocessing      : 2
% 2.54/2.73  # Initial clauses in saturation        : 15
% 2.54/2.73  # Processed clauses                    : 4547
% 2.54/2.73  # ...of these trivial                  : 1989
% 2.54/2.73  # ...subsumed                          : 1338
% 2.54/2.73  # ...remaining for further processing  : 1220
% 2.54/2.73  # Other redundant clauses eliminated   : 0
% 2.54/2.73  # Clauses deleted for lack of memory   : 0
% 2.54/2.73  # Backward-subsumed                    : 3
% 2.54/2.73  # Backward-rewritten                   : 649
% 2.54/2.73  # Generated clauses                    : 342826
% 2.54/2.73  # ...of the previous two non-trivial   : 198768
% 2.54/2.73  # Contextual simplify-reflections      : 0
% 2.54/2.73  # Paramodulations                      : 342813
% 2.54/2.73  # Factorizations                       : 0
% 2.54/2.73  # Equation resolutions                 : 13
% 2.54/2.73  # Propositional unsat checks           : 0
% 2.54/2.73  #    Propositional check models        : 0
% 2.54/2.73  #    Propositional check unsatisfiable : 0
% 2.54/2.73  #    Propositional clauses             : 0
% 2.54/2.73  #    Propositional clauses after purity: 0
% 2.54/2.73  #    Propositional unsat core size     : 0
% 2.54/2.73  #    Propositional preprocessing time  : 0.000
% 2.54/2.73  #    Propositional encoding time       : 0.000
% 2.54/2.73  #    Propositional solver time         : 0.000
% 2.54/2.73  #    Success case prop preproc time    : 0.000
% 2.54/2.73  #    Success case prop encoding time   : 0.000
% 2.54/2.73  #    Success case prop solver time     : 0.000
% 2.54/2.73  # Current number of processed clauses  : 553
% 2.54/2.73  #    Positive orientable unit clauses  : 485
% 2.54/2.73  #    Positive unorientable unit clauses: 0
% 2.54/2.73  #    Negative unit clauses             : 0
% 2.54/2.73  #    Non-unit-clauses                  : 68
% 2.54/2.73  # Current number of unprocessed clauses: 192669
% 2.54/2.73  # ...number of literals in the above   : 210749
% 2.54/2.73  # Current number of archived formulas  : 0
% 2.54/2.73  # Current number of archived clauses   : 669
% 2.54/2.73  # Clause-clause subsumption calls (NU) : 5640
% 2.54/2.73  # Rec. Clause-clause subsumption calls : 5640
% 2.54/2.73  # Non-unit clause-clause subsumptions  : 1341
% 2.54/2.73  # Unit Clause-clause subsumption calls : 1702
% 2.54/2.73  # Rewrite failures with RHS unbound    : 0
% 2.54/2.73  # BW rewrite match attempts            : 23109
% 2.54/2.73  # BW rewrite match successes           : 341
% 2.54/2.73  # Condensation attempts                : 0
% 2.54/2.73  # Condensation successes               : 0
% 2.54/2.73  # Termbank termtop insertions          : 6583073
% 2.54/2.74  
% 2.54/2.74  # -------------------------------------------------
% 2.54/2.74  # User time                : 2.295 s
% 2.54/2.74  # System time              : 0.105 s
% 2.54/2.74  # Total time               : 2.401 s
% 2.54/2.74  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
