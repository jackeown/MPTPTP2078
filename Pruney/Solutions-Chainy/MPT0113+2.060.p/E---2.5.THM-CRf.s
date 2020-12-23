%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:43 EST 2020

% Result     : Theorem 24.03s
% Output     : CNFRefutation 24.03s
% Verified   : 
% Statistics : Number of formulae       :  121 (15867 expanded)
%              Number of clauses        :   94 (7274 expanded)
%              Number of leaves         :   13 (4295 expanded)
%              Depth                    :   32
%              Number of atoms          :  176 (16827 expanded)
%              Number of equality atoms :   72 (14501 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   12 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(c_0_13,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k5_xboole_0(X23,X24),X25) = k5_xboole_0(X23,k5_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_14,plain,(
    ! [X26] : k5_xboole_0(X26,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_15,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_16,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X27,X28] : k3_xboole_0(X27,X28) = k5_xboole_0(k5_xboole_0(X27,X28),k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_18,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k4_xboole_0(X13,X12)) = k2_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_19,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X17] : k5_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_29,plain,(
    ! [X21,X22] : r1_xboole_0(k4_xboole_0(X21,X22),X22) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_23]),c_0_24])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X1) ),
    inference(rw,[status(thm)],[c_0_28,c_0_19])).

fof(c_0_33,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_19])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_26]),c_0_31])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_23]),c_0_24])).

fof(c_0_40,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_20])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_31])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_31])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r1_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X2,X1))),X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_24])).

cnf(c_0_50,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_46]),c_0_47])])).

cnf(c_0_51,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_19])).

cnf(c_0_53,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_50])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_38]),c_0_20])).

cnf(c_0_55,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_50]),c_0_31])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_27]),c_0_31])).

cnf(c_0_57,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_37])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_59]),c_0_27])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = X3 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_36]),c_0_19])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_50,c_0_60])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_52]),c_0_27])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_38]),c_0_20]),c_0_62])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

fof(c_0_66,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X14,k4_xboole_0(X15,X16)) = k2_xboole_0(k4_xboole_0(X14,X15),k3_xboole_0(X14,X16)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_63])).

cnf(c_0_68,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_64])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_65]),c_0_27])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(k5_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_19]),c_0_20]),c_0_27])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_69])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,X2))
    | ~ r1_tarski(X2,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))))) = k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_23]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(k5_xboole_0(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k5_xboole_0(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_69])).

fof(c_0_77,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))))))))) = k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X3,k2_xboole_0(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_51])).

cnf(c_0_80,plain,
    ( r1_tarski(k2_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_37])).

fof(c_0_81,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X2,X1))))) = k2_xboole_0(k5_xboole_0(X2,k2_xboole_0(X3,X2)),k5_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X3,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_36]),c_0_36]),c_0_36]),c_0_26]),c_0_31])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_85,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_41]),c_0_19])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X2))) = k2_xboole_0(k5_xboole_0(X2,k2_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_36]),c_0_41]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_23]),c_0_24])).

cnf(c_0_88,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_89,plain,
    ( r1_tarski(k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2),X2) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_87,c_0_19])).

cnf(c_0_91,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_88,c_0_24])).

cnf(c_0_92,plain,
    ( k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_79,c_0_89])).

fof(c_0_93,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | ~ r1_xboole_0(X19,X20)
      | r1_xboole_0(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_90,c_0_26])).

cnf(c_0_95,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_91,c_0_19])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_86,c_0_92])).

cnf(c_0_97,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_94,c_0_31])).

cnf(c_0_99,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1)))
    | k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_41]),c_0_19]),c_0_36])).

cnf(c_0_100,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_96]),c_0_69])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = X2
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_52]),c_0_27])).

cnf(c_0_102,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_97,c_0_37])).

cnf(c_0_104,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_20])])).

cnf(c_0_105,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_38]),c_0_20]),c_0_27])).

cnf(c_0_108,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_26]),c_0_31])).

cnf(c_0_109,negated_conjecture,
    ( r1_xboole_0(esk1_0,k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_104])).

cnf(c_0_110,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0
    | ~ r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_107,c_0_37])).

cnf(c_0_111,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( k5_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_113,plain,
    ( r1_tarski(k5_xboole_0(X1,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_100])).

cnf(c_0_114,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_112]),c_0_27])).

cnf(c_0_115,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_116,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_51])).

cnf(c_0_117,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k5_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_36])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116])])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:55:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 24.03/24.24  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 24.03/24.24  # and selection function SelectComplexExceptUniqMaxHorn.
% 24.03/24.24  #
% 24.03/24.24  # Preprocessing time       : 0.027 s
% 24.03/24.24  # Presaturation interreduction done
% 24.03/24.24  
% 24.03/24.24  # Proof found!
% 24.03/24.24  # SZS status Theorem
% 24.03/24.24  # SZS output start CNFRefutation
% 24.03/24.24  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 24.03/24.24  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 24.03/24.24  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 24.03/24.24  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 24.03/24.24  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 24.03/24.24  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 24.03/24.24  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 24.03/24.24  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 24.03/24.24  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 24.03/24.24  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 24.03/24.24  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 24.03/24.24  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 24.03/24.24  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 24.03/24.24  fof(c_0_13, plain, ![X23, X24, X25]:k5_xboole_0(k5_xboole_0(X23,X24),X25)=k5_xboole_0(X23,k5_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 24.03/24.24  fof(c_0_14, plain, ![X26]:k5_xboole_0(X26,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 24.03/24.24  fof(c_0_15, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 24.03/24.24  fof(c_0_16, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 24.03/24.24  fof(c_0_17, plain, ![X27, X28]:k3_xboole_0(X27,X28)=k5_xboole_0(k5_xboole_0(X27,X28),k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 24.03/24.24  fof(c_0_18, plain, ![X12, X13]:k2_xboole_0(X12,k4_xboole_0(X13,X12))=k2_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 24.03/24.24  cnf(c_0_19, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 24.03/24.24  cnf(c_0_20, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 24.03/24.24  fof(c_0_21, plain, ![X17]:k5_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t5_boole])).
% 24.03/24.24  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 24.03/24.24  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 24.03/24.24  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 24.03/24.24  cnf(c_0_25, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 24.03/24.24  cnf(c_0_26, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 24.03/24.24  cnf(c_0_27, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 24.03/24.24  cnf(c_0_28, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 24.03/24.24  fof(c_0_29, plain, ![X21, X22]:r1_xboole_0(k4_xboole_0(X21,X22),X22), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 24.03/24.24  cnf(c_0_30, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_23]), c_0_24])).
% 24.03/24.24  cnf(c_0_31, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_27])).
% 24.03/24.24  cnf(c_0_32, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X1)), inference(rw,[status(thm)],[c_0_28, c_0_19])).
% 24.03/24.24  fof(c_0_33, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 24.03/24.24  cnf(c_0_34, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 24.03/24.24  cnf(c_0_35, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_19])).
% 24.03/24.24  cnf(c_0_36, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_26, c_0_31])).
% 24.03/24.24  cnf(c_0_37, plain, (r1_tarski(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_26]), c_0_31])).
% 24.03/24.24  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 24.03/24.24  cnf(c_0_39, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_23]), c_0_24])).
% 24.03/24.24  fof(c_0_40, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 24.03/24.24  cnf(c_0_41, plain, (k2_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 24.03/24.24  cnf(c_0_42, plain, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_20])).
% 24.03/24.24  cnf(c_0_43, plain, (r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_31])).
% 24.03/24.24  cnf(c_0_44, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X2)), inference(rw,[status(thm)],[c_0_39, c_0_19])).
% 24.03/24.24  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 24.03/24.24  cnf(c_0_46, plain, (k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0))=k2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_31])).
% 24.03/24.24  cnf(c_0_47, plain, (r1_tarski(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 24.03/24.24  cnf(c_0_48, plain, (r1_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X2,X1))),X1)), inference(rw,[status(thm)],[c_0_44, c_0_26])).
% 24.03/24.24  cnf(c_0_49, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_24])).
% 24.03/24.24  cnf(c_0_50, plain, (k2_xboole_0(k1_xboole_0,X1)=k2_xboole_0(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_46]), c_0_47])])).
% 24.03/24.24  cnf(c_0_51, plain, (r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X1)), inference(rw,[status(thm)],[c_0_48, c_0_31])).
% 24.03/24.24  cnf(c_0_52, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_19])).
% 24.03/24.24  cnf(c_0_53, plain, (k2_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_50])).
% 24.03/24.24  cnf(c_0_54, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_38]), c_0_20])).
% 24.03/24.24  cnf(c_0_55, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_50]), c_0_31])).
% 24.03/24.24  cnf(c_0_56, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)|~r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_27]), c_0_31])).
% 24.03/24.24  cnf(c_0_57, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 24.03/24.24  cnf(c_0_58, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 24.03/24.24  cnf(c_0_59, plain, (k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_37])).
% 24.03/24.24  cnf(c_0_60, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_59]), c_0_27])).
% 24.03/24.24  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,X3))))=X3), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_36]), c_0_19])).
% 24.03/24.24  cnf(c_0_62, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_50, c_0_60])).
% 24.03/24.24  cnf(c_0_63, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,X2)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_52]), c_0_27])).
% 24.03/24.24  cnf(c_0_64, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_38]), c_0_20]), c_0_62])).
% 24.03/24.24  cnf(c_0_65, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 24.03/24.24  fof(c_0_66, plain, ![X14, X15, X16]:k4_xboole_0(X14,k4_xboole_0(X15,X16))=k2_xboole_0(k4_xboole_0(X14,X15),k3_xboole_0(X14,X16)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 24.03/24.24  cnf(c_0_67, plain, (k5_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_63])).
% 24.03/24.24  cnf(c_0_68, plain, (r1_tarski(k5_xboole_0(X1,X2),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_64])).
% 24.03/24.24  cnf(c_0_69, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_65]), c_0_27])).
% 24.03/24.24  cnf(c_0_70, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 24.03/24.24  cnf(c_0_71, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_xboole_0(k5_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_19]), c_0_20]), c_0_27])).
% 24.03/24.24  cnf(c_0_72, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_36, c_0_69])).
% 24.03/24.24  cnf(c_0_73, plain, (r1_tarski(X1,k5_xboole_0(X1,X2))|~r1_tarski(X2,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 24.03/24.24  cnf(c_0_74, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))))=k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_23]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 24.03/24.24  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_xboole_0(k5_xboole_0(X2,X1),X2)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 24.03/24.24  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~r1_tarski(k5_xboole_0(X2,X1),X2)), inference(spm,[status(thm)],[c_0_73, c_0_69])).
% 24.03/24.24  fof(c_0_77, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 24.03/24.24  cnf(c_0_78, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))))))))=k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X3,k2_xboole_0(X1,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19])).
% 24.03/24.24  cnf(c_0_79, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_75, c_0_51])).
% 24.03/24.24  cnf(c_0_80, plain, (r1_tarski(k2_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_76, c_0_37])).
% 24.03/24.24  fof(c_0_81, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))&(~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).
% 24.03/24.24  cnf(c_0_82, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X2,X1)))))=k2_xboole_0(k5_xboole_0(X2,k2_xboole_0(X3,X2)),k5_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X3,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_36]), c_0_36]), c_0_36]), c_0_26]), c_0_31])).
% 24.03/24.24  cnf(c_0_83, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 24.03/24.24  cnf(c_0_84, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 24.03/24.24  cnf(c_0_85, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X2))),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_41]), c_0_19])).
% 24.03/24.24  cnf(c_0_86, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X2)))=k2_xboole_0(k5_xboole_0(X2,k2_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_36]), c_0_41]), c_0_83])).
% 24.03/24.24  cnf(c_0_87, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_23]), c_0_24])).
% 24.03/24.24  cnf(c_0_88, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 24.03/24.24  cnf(c_0_89, plain, (r1_tarski(k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2),X2)), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 24.03/24.24  cnf(c_0_90, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)))))), inference(rw,[status(thm)],[c_0_87, c_0_19])).
% 24.03/24.24  cnf(c_0_91, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_88, c_0_24])).
% 24.03/24.24  cnf(c_0_92, plain, (k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2)=X2), inference(spm,[status(thm)],[c_0_79, c_0_89])).
% 24.03/24.24  fof(c_0_93, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|~r1_xboole_0(X19,X20)|r1_xboole_0(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 24.03/24.24  cnf(c_0_94, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[c_0_90, c_0_26])).
% 24.03/24.24  cnf(c_0_95, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_91, c_0_19])).
% 24.03/24.24  cnf(c_0_96, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_86, c_0_92])).
% 24.03/24.24  cnf(c_0_97, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 24.03/24.24  cnf(c_0_98, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_94, c_0_31])).
% 24.03/24.24  cnf(c_0_99, plain, (r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1)))|k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_41]), c_0_19]), c_0_36])).
% 24.03/24.24  cnf(c_0_100, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_96]), c_0_69])).
% 24.03/24.24  cnf(c_0_101, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=X2|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_52]), c_0_27])).
% 24.03/24.24  cnf(c_0_102, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 24.03/24.24  cnf(c_0_103, plain, (r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_97, c_0_37])).
% 24.03/24.24  cnf(c_0_104, plain, (r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_20])])).
% 24.03/24.24  cnf(c_0_105, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_101])).
% 24.03/24.24  cnf(c_0_106, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 24.03/24.24  cnf(c_0_107, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_38]), c_0_20]), c_0_27])).
% 24.03/24.24  cnf(c_0_108, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_26]), c_0_31])).
% 24.03/24.24  cnf(c_0_109, negated_conjecture, (r1_xboole_0(esk1_0,k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_106, c_0_104])).
% 24.03/24.24  cnf(c_0_110, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0|~r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_107, c_0_37])).
% 24.03/24.24  cnf(c_0_111, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0)),esk1_0)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 24.03/24.24  cnf(c_0_112, negated_conjecture, (k5_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 24.03/24.24  cnf(c_0_113, plain, (r1_tarski(k5_xboole_0(X1,k2_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_37, c_0_100])).
% 24.03/24.24  cnf(c_0_114, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_112]), c_0_27])).
% 24.03/24.24  cnf(c_0_115, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 24.03/24.24  cnf(c_0_116, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_102, c_0_51])).
% 24.03/24.24  cnf(c_0_117, plain, (r1_tarski(X1,X2)|~r1_tarski(k5_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_73, c_0_36])).
% 24.03/24.24  cnf(c_0_118, negated_conjecture, (r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 24.03/24.24  cnf(c_0_119, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116])])).
% 24.03/24.24  cnf(c_0_120, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119]), ['proof']).
% 24.03/24.24  # SZS output end CNFRefutation
% 24.03/24.24  # Proof object total steps             : 121
% 24.03/24.24  # Proof object clause steps            : 94
% 24.03/24.24  # Proof object formula steps           : 27
% 24.03/24.24  # Proof object conjectures             : 19
% 24.03/24.24  # Proof object clause conjectures      : 16
% 24.03/24.24  # Proof object formula conjectures     : 3
% 24.03/24.24  # Proof object initial clauses used    : 15
% 24.03/24.24  # Proof object initial formulas used   : 13
% 24.03/24.24  # Proof object generating inferences   : 52
% 24.03/24.24  # Proof object simplifying inferences  : 83
% 24.03/24.24  # Training examples: 0 positive, 0 negative
% 24.03/24.24  # Parsed axioms                        : 13
% 24.03/24.24  # Removed by relevancy pruning/SinE    : 0
% 24.03/24.24  # Initial clauses                      : 15
% 24.03/24.24  # Removed in clause preprocessing      : 2
% 24.03/24.24  # Initial clauses in saturation        : 13
% 24.03/24.24  # Processed clauses                    : 11711
% 24.03/24.24  # ...of these trivial                  : 126
% 24.03/24.24  # ...subsumed                          : 10155
% 24.03/24.24  # ...remaining for further processing  : 1430
% 24.03/24.24  # Other redundant clauses eliminated   : 656
% 24.03/24.24  # Clauses deleted for lack of memory   : 0
% 24.03/24.24  # Backward-subsumed                    : 130
% 24.03/24.24  # Backward-rewritten                   : 161
% 24.03/24.24  # Generated clauses                    : 765296
% 24.03/24.24  # ...of the previous two non-trivial   : 749797
% 24.03/24.24  # Contextual simplify-reflections      : 38
% 24.03/24.24  # Paramodulations                      : 764640
% 24.03/24.24  # Factorizations                       : 0
% 24.03/24.24  # Equation resolutions                 : 656
% 24.03/24.24  # Propositional unsat checks           : 0
% 24.03/24.24  #    Propositional check models        : 0
% 24.03/24.24  #    Propositional check unsatisfiable : 0
% 24.03/24.24  #    Propositional clauses             : 0
% 24.03/24.24  #    Propositional clauses after purity: 0
% 24.03/24.24  #    Propositional unsat core size     : 0
% 24.03/24.24  #    Propositional preprocessing time  : 0.000
% 24.03/24.24  #    Propositional encoding time       : 0.000
% 24.03/24.24  #    Propositional solver time         : 0.000
% 24.03/24.24  #    Success case prop preproc time    : 0.000
% 24.03/24.24  #    Success case prop encoding time   : 0.000
% 24.03/24.24  #    Success case prop solver time     : 0.000
% 24.03/24.24  # Current number of processed clauses  : 1125
% 24.03/24.24  #    Positive orientable unit clauses  : 108
% 24.03/24.24  #    Positive unorientable unit clauses: 110
% 24.03/24.24  #    Negative unit clauses             : 38
% 24.03/24.24  #    Non-unit-clauses                  : 869
% 24.03/24.24  # Current number of unprocessed clauses: 735668
% 24.03/24.24  # ...number of literals in the above   : 1484403
% 24.03/24.24  # Current number of archived formulas  : 0
% 24.03/24.24  # Current number of archived clauses   : 306
% 24.03/24.24  # Clause-clause subsumption calls (NU) : 146481
% 24.03/24.24  # Rec. Clause-clause subsumption calls : 86876
% 24.03/24.24  # Non-unit clause-clause subsumptions  : 5843
% 24.03/24.24  # Unit Clause-clause subsumption calls : 9028
% 24.03/24.24  # Rewrite failures with RHS unbound    : 43
% 24.03/24.24  # BW rewrite match attempts            : 25937
% 24.03/24.24  # BW rewrite match successes           : 1013
% 24.03/24.24  # Condensation attempts                : 0
% 24.03/24.24  # Condensation successes               : 0
% 24.03/24.24  # Termbank termtop insertions          : 66226365
% 24.07/24.31  
% 24.07/24.31  # -------------------------------------------------
% 24.07/24.31  # User time                : 23.172 s
% 24.07/24.31  # System time              : 0.748 s
% 24.07/24.31  # Total time               : 23.920 s
% 24.07/24.31  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
