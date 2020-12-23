%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:12 EST 2020

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 546 expanded)
%              Number of clauses        :   56 ( 247 expanded)
%              Number of leaves         :   15 ( 149 expanded)
%              Depth                    :   16
%              Number of atoms          :   96 ( 672 expanded)
%              Number of equality atoms :   72 ( 493 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(t47_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_15,plain,(
    ! [X37,X38] : r1_tarski(X37,k2_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_16,plain,(
    ! [X15] : k2_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_17,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_18,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_19,plain,(
    ! [X28,X29,X30] : k4_xboole_0(k4_xboole_0(X28,X29),X30) = k4_xboole_0(X28,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_20,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X13,X14] : r1_tarski(k3_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_24,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_25,plain,(
    ! [X26,X27] : k2_xboole_0(X26,k4_xboole_0(X27,X26)) = k2_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_26,plain,(
    ! [X31,X32,X33] : k4_xboole_0(k2_xboole_0(X31,X32),X33) = k2_xboole_0(k4_xboole_0(X31,X33),k4_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_32,plain,(
    ! [X16,X17] : k3_xboole_0(X16,k2_xboole_0(X16,X17)) = X16 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X10,X11,X12] : k3_xboole_0(k3_xboole_0(X10,X11),X12) = k3_xboole_0(X10,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_42,plain,(
    ! [X18,X19] : k2_xboole_0(X18,k3_xboole_0(X18,X19)) = X18 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k4_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_40]),c_0_22])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_40]),c_0_39])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_45])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_36])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_22]),c_0_48])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_44])).

fof(c_0_56,plain,(
    ! [X20,X21] :
      ( k4_xboole_0(X20,X21) != k4_xboole_0(X21,X20)
      | X20 = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_57,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_49])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_55]),c_0_44]),c_0_44])).

cnf(c_0_60,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( r1_tarski(k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_59])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,X2) = X2
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_47]),c_0_38])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_61])).

cnf(c_0_66,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X3,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_30])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_29]),c_0_36])).

cnf(c_0_69,plain,
    ( r1_tarski(k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_54]),c_0_34])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_47]),c_0_37])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_68])).

fof(c_0_73,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t47_xboole_1])).

cnf(c_0_74,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_55])).

cnf(c_0_75,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_71]),c_0_36]),c_0_72])).

fof(c_0_77,negated_conjecture,(
    k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_74])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_75]),c_0_29])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k2_xboole_0(X3,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_54]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X3,X2)) = k4_xboole_0(X1,k3_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_78]),c_0_22])).

cnf(c_0_83,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_79]),c_0_80]),c_0_30]),c_0_50])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_34])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_29]),c_0_50])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.86/1.05  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.86/1.05  # and selection function SelectNewComplexAHP.
% 0.86/1.05  #
% 0.86/1.05  # Preprocessing time       : 0.027 s
% 0.86/1.05  # Presaturation interreduction done
% 0.86/1.05  
% 0.86/1.05  # Proof found!
% 0.86/1.05  # SZS status Theorem
% 0.86/1.05  # SZS output start CNFRefutation
% 0.86/1.05  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.86/1.05  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.86/1.05  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.86/1.05  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.86/1.05  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.86/1.05  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.86/1.05  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.86/1.05  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.86/1.05  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.86/1.05  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.86/1.05  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.86/1.05  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.86/1.05  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.86/1.05  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.86/1.05  fof(t47_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.86/1.05  fof(c_0_15, plain, ![X37, X38]:r1_tarski(X37,k2_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.86/1.05  fof(c_0_16, plain, ![X15]:k2_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.86/1.05  fof(c_0_17, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.86/1.05  fof(c_0_18, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.86/1.05  fof(c_0_19, plain, ![X28, X29, X30]:k4_xboole_0(k4_xboole_0(X28,X29),X30)=k4_xboole_0(X28,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.86/1.05  fof(c_0_20, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.86/1.05  cnf(c_0_21, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.86/1.05  cnf(c_0_22, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.86/1.05  fof(c_0_23, plain, ![X13, X14]:r1_tarski(k3_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.86/1.05  fof(c_0_24, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.86/1.05  fof(c_0_25, plain, ![X26, X27]:k2_xboole_0(X26,k4_xboole_0(X27,X26))=k2_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.86/1.05  fof(c_0_26, plain, ![X31, X32, X33]:k4_xboole_0(k2_xboole_0(X31,X32),X33)=k2_xboole_0(k4_xboole_0(X31,X33),k4_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.86/1.05  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.86/1.05  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.86/1.05  cnf(c_0_29, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.86/1.05  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.86/1.05  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.86/1.05  fof(c_0_32, plain, ![X16, X17]:k3_xboole_0(X16,k2_xboole_0(X16,X17))=X16, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.86/1.05  cnf(c_0_33, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.86/1.05  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.86/1.05  fof(c_0_35, plain, ![X10, X11, X12]:k3_xboole_0(k3_xboole_0(X10,X11),X12)=k3_xboole_0(X10,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.86/1.05  cnf(c_0_36, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.86/1.05  cnf(c_0_37, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.86/1.05  cnf(c_0_38, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.86/1.05  cnf(c_0_39, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_22, c_0_30])).
% 0.86/1.05  cnf(c_0_40, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_31])).
% 0.86/1.05  cnf(c_0_41, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.86/1.05  fof(c_0_42, plain, ![X18, X19]:k2_xboole_0(X18,k3_xboole_0(X18,X19))=X18, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.86/1.05  cnf(c_0_43, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.86/1.05  cnf(c_0_44, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.86/1.05  cnf(c_0_45, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_36, c_0_29])).
% 0.86/1.05  cnf(c_0_46, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k4_xboole_0(X2,k2_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.86/1.05  cnf(c_0_47, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_40]), c_0_22])).
% 0.86/1.05  cnf(c_0_48, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_40]), c_0_39])).
% 0.86/1.05  cnf(c_0_49, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_41, c_0_30])).
% 0.86/1.05  cnf(c_0_50, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.86/1.05  cnf(c_0_51, plain, (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.86/1.05  cnf(c_0_52, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_45])).
% 0.86/1.05  cnf(c_0_53, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_47, c_0_36])).
% 0.86/1.05  cnf(c_0_54, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_22]), c_0_48])).
% 0.86/1.05  cnf(c_0_55, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_44])).
% 0.86/1.05  fof(c_0_56, plain, ![X20, X21]:(k4_xboole_0(X20,X21)!=k4_xboole_0(X21,X20)|X20=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 0.86/1.05  cnf(c_0_57, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_51, c_0_49])).
% 0.86/1.05  cnf(c_0_58, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.86/1.05  cnf(c_0_59, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_55]), c_0_44]), c_0_44])).
% 0.86/1.05  cnf(c_0_60, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.86/1.05  cnf(c_0_61, plain, (r1_tarski(k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.86/1.05  cnf(c_0_62, plain, (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_51, c_0_59])).
% 0.86/1.05  cnf(c_0_63, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_44])).
% 0.86/1.05  cnf(c_0_64, plain, (k2_xboole_0(X1,X2)=X2|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_47]), c_0_38])).
% 0.86/1.05  cnf(c_0_65, plain, (k4_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_61])).
% 0.86/1.05  cnf(c_0_66, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X3,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.86/1.05  cnf(c_0_67, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X1))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_30])).
% 0.86/1.05  cnf(c_0_68, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_37]), c_0_29]), c_0_36])).
% 0.86/1.05  cnf(c_0_69, plain, (r1_tarski(k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.86/1.05  cnf(c_0_70, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_54]), c_0_34])).
% 0.86/1.05  cnf(c_0_71, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3)=k4_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_47]), c_0_37])).
% 0.86/1.05  cnf(c_0_72, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X2,k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_64, c_0_68])).
% 0.86/1.05  fof(c_0_73, negated_conjecture, ~(![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t47_xboole_1])).
% 0.86/1.05  cnf(c_0_74, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_43, c_0_55])).
% 0.86/1.05  cnf(c_0_75, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.86/1.05  cnf(c_0_76, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_71]), c_0_36]), c_0_72])).
% 0.86/1.05  fof(c_0_77, negated_conjecture, k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(esk1_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).
% 0.86/1.05  cnf(c_0_78, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_74])).
% 0.86/1.05  cnf(c_0_79, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_75]), c_0_29])).
% 0.86/1.05  cnf(c_0_80, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k2_xboole_0(X3,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_54]), c_0_76])).
% 0.86/1.05  cnf(c_0_81, negated_conjecture, (k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.86/1.05  cnf(c_0_82, plain, (k4_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X3,X2))=k4_xboole_0(X1,k3_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_78]), c_0_22])).
% 0.86/1.05  cnf(c_0_83, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_79]), c_0_80]), c_0_30]), c_0_50])).
% 0.86/1.05  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))!=k4_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_81, c_0_34])).
% 0.86/1.05  cnf(c_0_85, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_29]), c_0_50])).
% 0.86/1.05  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])]), ['proof']).
% 0.86/1.05  # SZS output end CNFRefutation
% 0.86/1.05  # Proof object total steps             : 87
% 0.86/1.05  # Proof object clause steps            : 56
% 0.86/1.05  # Proof object formula steps           : 31
% 0.86/1.05  # Proof object conjectures             : 6
% 0.86/1.05  # Proof object clause conjectures      : 3
% 0.86/1.05  # Proof object formula conjectures     : 3
% 0.86/1.05  # Proof object initial clauses used    : 15
% 0.86/1.05  # Proof object initial formulas used   : 15
% 0.86/1.05  # Proof object generating inferences   : 39
% 0.86/1.05  # Proof object simplifying inferences  : 30
% 0.86/1.05  # Training examples: 0 positive, 0 negative
% 0.86/1.05  # Parsed axioms                        : 17
% 0.86/1.05  # Removed by relevancy pruning/SinE    : 0
% 0.86/1.05  # Initial clauses                      : 18
% 0.86/1.05  # Removed in clause preprocessing      : 0
% 0.86/1.05  # Initial clauses in saturation        : 18
% 0.86/1.05  # Processed clauses                    : 4520
% 0.86/1.05  # ...of these trivial                  : 2060
% 0.86/1.05  # ...subsumed                          : 1736
% 0.86/1.05  # ...remaining for further processing  : 724
% 0.86/1.05  # Other redundant clauses eliminated   : 0
% 0.86/1.05  # Clauses deleted for lack of memory   : 0
% 0.86/1.05  # Backward-subsumed                    : 0
% 0.86/1.05  # Backward-rewritten                   : 69
% 0.86/1.05  # Generated clauses                    : 145099
% 0.86/1.05  # ...of the previous two non-trivial   : 77332
% 0.86/1.05  # Contextual simplify-reflections      : 0
% 0.86/1.05  # Paramodulations                      : 145097
% 0.86/1.05  # Factorizations                       : 0
% 0.86/1.05  # Equation resolutions                 : 2
% 0.86/1.05  # Propositional unsat checks           : 0
% 0.86/1.05  #    Propositional check models        : 0
% 0.86/1.05  #    Propositional check unsatisfiable : 0
% 0.86/1.05  #    Propositional clauses             : 0
% 0.86/1.05  #    Propositional clauses after purity: 0
% 0.86/1.05  #    Propositional unsat core size     : 0
% 0.86/1.05  #    Propositional preprocessing time  : 0.000
% 0.86/1.05  #    Propositional encoding time       : 0.000
% 0.86/1.05  #    Propositional solver time         : 0.000
% 0.86/1.05  #    Success case prop preproc time    : 0.000
% 0.86/1.05  #    Success case prop encoding time   : 0.000
% 0.86/1.05  #    Success case prop solver time     : 0.000
% 0.86/1.05  # Current number of processed clauses  : 637
% 0.86/1.05  #    Positive orientable unit clauses  : 585
% 0.86/1.05  #    Positive unorientable unit clauses: 8
% 0.86/1.05  #    Negative unit clauses             : 0
% 0.86/1.05  #    Non-unit-clauses                  : 44
% 0.86/1.05  # Current number of unprocessed clauses: 72160
% 0.86/1.05  # ...number of literals in the above   : 75401
% 0.86/1.05  # Current number of archived formulas  : 0
% 0.86/1.05  # Current number of archived clauses   : 87
% 0.86/1.05  # Clause-clause subsumption calls (NU) : 1318
% 0.86/1.05  # Rec. Clause-clause subsumption calls : 1318
% 0.86/1.05  # Non-unit clause-clause subsumptions  : 558
% 0.86/1.05  # Unit Clause-clause subsumption calls : 92
% 0.86/1.05  # Rewrite failures with RHS unbound    : 0
% 0.86/1.05  # BW rewrite match attempts            : 2218
% 0.86/1.05  # BW rewrite match successes           : 338
% 0.86/1.05  # Condensation attempts                : 0
% 0.86/1.05  # Condensation successes               : 0
% 0.86/1.05  # Termbank termtop insertions          : 1287931
% 0.86/1.06  
% 0.86/1.06  # -------------------------------------------------
% 0.86/1.06  # User time                : 0.679 s
% 0.86/1.06  # System time              : 0.043 s
% 0.86/1.06  # Total time               : 0.722 s
% 0.86/1.06  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
