%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:11 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 922 expanded)
%              Number of clauses        :   52 ( 421 expanded)
%              Number of leaves         :   16 ( 250 expanded)
%              Depth                    :   17
%              Number of atoms          :  101 (1116 expanded)
%              Number of equality atoms :   55 ( 667 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t47_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(c_0_16,plain,(
    ! [X46,X47] : r1_tarski(X46,k2_xboole_0(X46,X47)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_17,plain,(
    ! [X8] : k2_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_18,plain,(
    ! [X43,X44,X45] :
      ( ~ r1_tarski(k4_xboole_0(X43,X44),X45)
      | r1_tarski(X43,k2_xboole_0(X44,X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X40,X41,X42] : k4_xboole_0(k2_xboole_0(X40,X41),X42) = k2_xboole_0(k4_xboole_0(X40,X42),k4_xboole_0(X41,X42)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

fof(c_0_22,plain,(
    ! [X35,X36] : k4_xboole_0(k2_xboole_0(X35,X36),X36) = k4_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_23,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_xboole_0(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_26,plain,(
    ! [X18,X19] : r1_tarski(k3_xboole_0(X18,X19),X18) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_27,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_32,plain,(
    ! [X23,X24] : k3_xboole_0(X23,k2_xboole_0(X23,X24)) = X23 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_33,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_34,plain,(
    ! [X33,X34] : r1_tarski(k4_xboole_0(X33,X34),X33) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_tarski(X21,X22)
      | r1_tarski(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_28])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_44,plain,(
    ! [X15,X16,X17] : k3_xboole_0(k3_xboole_0(X15,X16),X17) = k3_xboole_0(X15,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_28])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_29])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_42]),c_0_41])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_41])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_43]),c_0_41])).

cnf(c_0_52,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k3_xboole_0(X28,X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_36])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_52])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X2)) = k4_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_52]),c_0_56])).

cnf(c_0_62,plain,
    ( r1_tarski(k3_xboole_0(X1,k4_xboole_0(X2,X3)),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_56])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_36])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_61])).

cnf(c_0_65,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_30,c_0_64])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_65])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X1) = k4_xboole_0(k2_xboole_0(X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_50]),c_0_28])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,k4_xboole_0(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_66])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_59,c_0_67])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X1) = k4_xboole_0(X3,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_49]),c_0_50])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_69]),c_0_49])).

fof(c_0_73,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t47_xboole_1])).

cnf(c_0_74,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_70]),c_0_71]),c_0_57]),c_0_72])).

fof(c_0_75,negated_conjecture,(
    k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_74]),c_0_41])).

fof(c_0_77,plain,(
    ! [X37,X38,X39] : k4_xboole_0(k4_xboole_0(X37,X38),X39) = k4_xboole_0(X37,k2_xboole_0(X38,X39)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_79,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_70]),c_0_71]),c_0_57]),c_0_66]),c_0_41]),c_0_76])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_35]),c_0_41])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)) != k4_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_36])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_79]),c_0_80]),c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:12:10 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.42  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.18/0.42  # and selection function SelectNewComplexAHP.
% 0.18/0.42  #
% 0.18/0.42  # Preprocessing time       : 0.014 s
% 0.18/0.42  # Presaturation interreduction done
% 0.18/0.42  
% 0.18/0.42  # Proof found!
% 0.18/0.42  # SZS status Theorem
% 0.18/0.42  # SZS output start CNFRefutation
% 0.18/0.42  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.18/0.42  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.18/0.42  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.18/0.42  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.18/0.42  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.18/0.42  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.42  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.18/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.42  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.18/0.42  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.18/0.42  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.18/0.42  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.18/0.42  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.18/0.42  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.18/0.42  fof(t47_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.18/0.42  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.18/0.42  fof(c_0_16, plain, ![X46, X47]:r1_tarski(X46,k2_xboole_0(X46,X47)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.18/0.42  fof(c_0_17, plain, ![X8]:k2_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.18/0.42  fof(c_0_18, plain, ![X43, X44, X45]:(~r1_tarski(k4_xboole_0(X43,X44),X45)|r1_tarski(X43,k2_xboole_0(X44,X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.18/0.42  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_20, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.42  fof(c_0_21, plain, ![X40, X41, X42]:k4_xboole_0(k2_xboole_0(X40,X41),X42)=k2_xboole_0(k4_xboole_0(X40,X42),k4_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.18/0.42  fof(c_0_22, plain, ![X35, X36]:k4_xboole_0(k2_xboole_0(X35,X36),X36)=k4_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.18/0.42  fof(c_0_23, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_xboole_0(X13,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.42  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.42  cnf(c_0_25, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.42  fof(c_0_26, plain, ![X18, X19]:r1_tarski(k3_xboole_0(X18,X19),X18), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.18/0.42  fof(c_0_27, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.42  cnf(c_0_28, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.42  cnf(c_0_29, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.42  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.42  fof(c_0_32, plain, ![X23, X24]:k3_xboole_0(X23,k2_xboole_0(X23,X24))=X23, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.18/0.42  fof(c_0_33, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.18/0.42  fof(c_0_34, plain, ![X33, X34]:r1_tarski(k4_xboole_0(X33,X34),X33), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.18/0.42  cnf(c_0_35, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.42  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.42  fof(c_0_37, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|~r1_tarski(X21,X22)|r1_tarski(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.18/0.42  cnf(c_0_38, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3)=k4_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_28])).
% 0.18/0.42  cnf(c_0_39, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k2_xboole_0(X2,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.18/0.42  cnf(c_0_40, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.42  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.42  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.42  cnf(c_0_43, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.42  fof(c_0_44, plain, ![X15, X16, X17]:k3_xboole_0(k3_xboole_0(X15,X16),X17)=k3_xboole_0(X15,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.18/0.42  cnf(c_0_45, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.42  cnf(c_0_46, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2))), inference(spm,[status(thm)],[c_0_19, c_0_28])).
% 0.18/0.42  cnf(c_0_47, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_29])).
% 0.18/0.42  cnf(c_0_48, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.42  cnf(c_0_49, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_42]), c_0_41])).
% 0.18/0.42  cnf(c_0_50, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_41])).
% 0.18/0.42  cnf(c_0_51, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_43]), c_0_41])).
% 0.18/0.42  cnf(c_0_52, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.42  fof(c_0_53, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k3_xboole_0(X28,X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.18/0.42  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_45, c_0_42])).
% 0.18/0.42  cnf(c_0_55, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.42  cnf(c_0_56, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_36])).
% 0.18/0.42  cnf(c_0_57, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k4_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.18/0.42  cnf(c_0_58, plain, (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_52])).
% 0.18/0.42  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.42  cnf(c_0_60, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.18/0.42  cnf(c_0_61, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X2))=k4_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_52]), c_0_56])).
% 0.18/0.42  cnf(c_0_62, plain, (r1_tarski(k3_xboole_0(X1,k4_xboole_0(X2,X3)),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_58, c_0_56])).
% 0.18/0.42  cnf(c_0_63, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_36])).
% 0.18/0.42  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_35, c_0_61])).
% 0.18/0.42  cnf(c_0_65, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.18/0.42  cnf(c_0_66, plain, (k2_xboole_0(k4_xboole_0(X1,X1),X2)=X2), inference(spm,[status(thm)],[c_0_30, c_0_64])).
% 0.18/0.42  cnf(c_0_67, plain, (r1_tarski(X1,k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_24, c_0_65])).
% 0.18/0.42  cnf(c_0_68, plain, (k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X1)=k4_xboole_0(k2_xboole_0(X2,X3),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_50]), c_0_28])).
% 0.18/0.42  cnf(c_0_69, plain, (r1_tarski(X1,k4_xboole_0(X1,k4_xboole_0(X2,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_66])).
% 0.18/0.42  cnf(c_0_70, plain, (k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_59, c_0_67])).
% 0.18/0.42  cnf(c_0_71, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X1)=k4_xboole_0(X3,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_49]), c_0_50])).
% 0.18/0.42  cnf(c_0_72, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_69]), c_0_49])).
% 0.18/0.42  fof(c_0_73, negated_conjecture, ~(![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t47_xboole_1])).
% 0.18/0.42  cnf(c_0_74, plain, (r1_tarski(k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_70]), c_0_71]), c_0_57]), c_0_72])).
% 0.18/0.42  fof(c_0_75, negated_conjecture, k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(esk1_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).
% 0.18/0.42  cnf(c_0_76, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_74]), c_0_41])).
% 0.18/0.42  fof(c_0_77, plain, ![X37, X38, X39]:k4_xboole_0(k4_xboole_0(X37,X38),X39)=k4_xboole_0(X37,k2_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.18/0.42  cnf(c_0_78, negated_conjecture, (k4_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.18/0.42  cnf(c_0_79, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_70]), c_0_71]), c_0_57]), c_0_66]), c_0_41]), c_0_76])).
% 0.18/0.42  cnf(c_0_80, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.18/0.42  cnf(c_0_81, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_35]), c_0_41])).
% 0.18/0.42  cnf(c_0_82, negated_conjecture, (k4_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))!=k4_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_78, c_0_36])).
% 0.18/0.42  cnf(c_0_83, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_79]), c_0_80]), c_0_81])).
% 0.18/0.42  cnf(c_0_84, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])]), ['proof']).
% 0.18/0.42  # SZS output end CNFRefutation
% 0.18/0.42  # Proof object total steps             : 85
% 0.18/0.42  # Proof object clause steps            : 52
% 0.18/0.42  # Proof object formula steps           : 33
% 0.18/0.42  # Proof object conjectures             : 6
% 0.18/0.42  # Proof object clause conjectures      : 3
% 0.18/0.42  # Proof object formula conjectures     : 3
% 0.18/0.42  # Proof object initial clauses used    : 16
% 0.18/0.42  # Proof object initial formulas used   : 16
% 0.18/0.42  # Proof object generating inferences   : 34
% 0.18/0.42  # Proof object simplifying inferences  : 26
% 0.18/0.42  # Training examples: 0 positive, 0 negative
% 0.18/0.42  # Parsed axioms                        : 20
% 0.18/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.42  # Initial clauses                      : 20
% 0.18/0.42  # Removed in clause preprocessing      : 0
% 0.18/0.42  # Initial clauses in saturation        : 20
% 0.18/0.42  # Processed clauses                    : 1258
% 0.18/0.42  # ...of these trivial                  : 661
% 0.18/0.42  # ...subsumed                          : 290
% 0.18/0.42  # ...remaining for further processing  : 307
% 0.18/0.42  # Other redundant clauses eliminated   : 0
% 0.18/0.42  # Clauses deleted for lack of memory   : 0
% 0.18/0.42  # Backward-subsumed                    : 0
% 0.18/0.42  # Backward-rewritten                   : 29
% 0.18/0.42  # Generated clauses                    : 22849
% 0.18/0.42  # ...of the previous two non-trivial   : 11908
% 0.18/0.42  # Contextual simplify-reflections      : 0
% 0.18/0.42  # Paramodulations                      : 22849
% 0.18/0.42  # Factorizations                       : 0
% 0.18/0.42  # Equation resolutions                 : 0
% 0.18/0.42  # Propositional unsat checks           : 0
% 0.18/0.42  #    Propositional check models        : 0
% 0.18/0.42  #    Propositional check unsatisfiable : 0
% 0.18/0.42  #    Propositional clauses             : 0
% 0.18/0.42  #    Propositional clauses after purity: 0
% 0.18/0.42  #    Propositional unsat core size     : 0
% 0.18/0.42  #    Propositional preprocessing time  : 0.000
% 0.18/0.42  #    Propositional encoding time       : 0.000
% 0.18/0.42  #    Propositional solver time         : 0.000
% 0.18/0.42  #    Success case prop preproc time    : 0.000
% 0.18/0.42  #    Success case prop encoding time   : 0.000
% 0.18/0.42  #    Success case prop solver time     : 0.000
% 0.18/0.42  # Current number of processed clauses  : 258
% 0.18/0.42  #    Positive orientable unit clauses  : 240
% 0.18/0.42  #    Positive unorientable unit clauses: 5
% 0.18/0.42  #    Negative unit clauses             : 0
% 0.18/0.42  #    Non-unit-clauses                  : 13
% 0.18/0.42  # Current number of unprocessed clauses: 10608
% 0.18/0.42  # ...number of literals in the above   : 10864
% 0.18/0.42  # Current number of archived formulas  : 0
% 0.18/0.42  # Current number of archived clauses   : 49
% 0.18/0.42  # Clause-clause subsumption calls (NU) : 130
% 0.18/0.42  # Rec. Clause-clause subsumption calls : 130
% 0.18/0.42  # Non-unit clause-clause subsumptions  : 37
% 0.18/0.42  # Unit Clause-clause subsumption calls : 32
% 0.18/0.42  # Rewrite failures with RHS unbound    : 40
% 0.18/0.42  # BW rewrite match attempts            : 490
% 0.18/0.42  # BW rewrite match successes           : 104
% 0.18/0.42  # Condensation attempts                : 0
% 0.18/0.42  # Condensation successes               : 0
% 0.18/0.42  # Termbank termtop insertions          : 165512
% 0.18/0.42  
% 0.18/0.42  # -------------------------------------------------
% 0.18/0.42  # User time                : 0.092 s
% 0.18/0.42  # System time              : 0.007 s
% 0.18/0.42  # Total time               : 0.099 s
% 0.18/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
