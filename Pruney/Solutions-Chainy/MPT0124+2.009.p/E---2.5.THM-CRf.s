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
% DateTime   : Thu Dec  3 10:35:00 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :  110 (83352 expanded)
%              Number of clauses        :   85 (38591 expanded)
%              Number of leaves         :   12 (21349 expanded)
%              Depth                    :   28
%              Number of atoms          :  136 (124547 expanded)
%              Number of equality atoms :   81 (48148 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

fof(c_0_13,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    & k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X16,X17] : k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_24,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk2_0) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_30]),c_0_31])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk2_0),k4_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_34])).

fof(c_0_37,plain,(
    ! [X28,X29] : r1_tarski(X28,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_38,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | r1_tarski(k2_xboole_0(X30,X32),k2_xboole_0(X31,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_41,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | X22 = k2_xboole_0(X21,k4_xboole_0(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk3_0,esk2_0),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_39])).

fof(c_0_44,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,k2_xboole_0(X19,X20))
      | r1_tarski(k4_xboole_0(X18,X19),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_40])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_47,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_39]),c_0_43])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_20])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_26])).

fof(c_0_53,plain,(
    ! [X25,X26,X27] : k4_xboole_0(X25,k4_xboole_0(X26,X27)) = k2_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X25,X27)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_54,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_52])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_22,c_0_54])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_55,c_0_54])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_29])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_57]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X3,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_40])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_64]),c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_65])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_26]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_67]),c_0_67])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_51]),c_0_61])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_70])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_52]),c_0_71]),c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( k2_xboole_0(X1,k4_xboole_0(esk3_0,esk2_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_55,c_0_39])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_59]),c_0_73])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_74]),c_0_58])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_75]),c_0_51])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),X1) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_76])).

cnf(c_0_81,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_59]),c_0_77]),c_0_51]),c_0_57]),c_0_77]),c_0_51]),c_0_57])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_61])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_85,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_26]),c_0_81]),c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_83])).

cnf(c_0_87,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_71,c_0_75])).

cnf(c_0_88,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_16])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_84,c_0_29])).

cnf(c_0_90,negated_conjecture,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(k4_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_86]),c_0_61])).

cnf(c_0_92,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_88,c_0_52])).

cnf(c_0_94,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0))) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_89,c_0_33])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_33])).

cnf(c_0_96,negated_conjecture,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(k4_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_69])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(X1,k4_xboole_0(esk3_0,X2))) = k2_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)) = k2_xboole_0(k4_xboole_0(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)),k4_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_94,c_0_69])).

cnf(c_0_100,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_51]),c_0_57])).

cnf(c_0_101,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X1),X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_64]),c_0_85]),c_0_85]),c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk3_0,k4_xboole_0(X2,X1))) = k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_66]),c_0_98]),c_0_69])).

cnf(c_0_103,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(X3,k4_xboole_0(X3,X2)))) = k2_xboole_0(X3,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_59])).

cnf(c_0_105,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)))) = k4_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_66]),c_0_66])).

cnf(c_0_106,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_40])).

cnf(c_0_107,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk1_0))),k4_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_85])).

cnf(c_0_108,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))),k4_xboole_0(X1,esk2_0)) = k4_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_85]),c_0_27]),c_0_85]),c_0_106]),c_0_68]),c_0_78]),c_0_51]),c_0_58])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.26/5.41  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 5.26/5.41  # and selection function SelectNewComplexAHP.
% 5.26/5.41  #
% 5.26/5.41  # Preprocessing time       : 0.016 s
% 5.26/5.41  
% 5.26/5.41  # Proof found!
% 5.26/5.41  # SZS status Theorem
% 5.26/5.41  # SZS output start CNFRefutation
% 5.26/5.41  fof(t117_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 5.26/5.41  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.26/5.41  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.26/5.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.26/5.41  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.26/5.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.26/5.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.26/5.41  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.26/5.41  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 5.26/5.41  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 5.26/5.41  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.26/5.41  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 5.26/5.41  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t117_xboole_1])).
% 5.26/5.41  fof(c_0_13, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 5.26/5.41  fof(c_0_14, negated_conjecture, (r1_tarski(esk3_0,esk2_0)&k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 5.26/5.41  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 5.26/5.41  cnf(c_0_16, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.26/5.41  fof(c_0_17, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 5.26/5.41  fof(c_0_18, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 5.26/5.41  cnf(c_0_19, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 5.26/5.41  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.26/5.41  fof(c_0_21, plain, ![X16, X17]:k4_xboole_0(k2_xboole_0(X16,X17),X17)=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 5.26/5.41  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.26/5.41  fof(c_0_23, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 5.26/5.41  fof(c_0_24, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 5.26/5.41  cnf(c_0_25, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 5.26/5.41  cnf(c_0_26, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.26/5.41  cnf(c_0_27, negated_conjecture, (k2_xboole_0(esk3_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_22, c_0_16])).
% 5.26/5.41  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.26/5.41  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.26/5.41  cnf(c_0_30, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 5.26/5.41  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk2_0,esk2_0)=k4_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 5.26/5.41  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_15, c_0_20])).
% 5.26/5.41  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29])).
% 5.26/5.41  cnf(c_0_34, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0)=k4_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_30]), c_0_31])).
% 5.26/5.41  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 5.26/5.41  cnf(c_0_36, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk2_0),k4_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_20, c_0_34])).
% 5.26/5.41  fof(c_0_37, plain, ![X28, X29]:r1_tarski(X28,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 5.26/5.41  fof(c_0_38, plain, ![X30, X31, X32]:(~r1_tarski(X30,X31)|r1_tarski(k2_xboole_0(X30,X32),k2_xboole_0(X31,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 5.26/5.41  cnf(c_0_39, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 5.26/5.41  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 5.26/5.41  fof(c_0_41, plain, ![X21, X22]:(~r1_tarski(X21,X22)|X22=k2_xboole_0(X21,k4_xboole_0(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 5.26/5.41  cnf(c_0_42, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 5.26/5.41  cnf(c_0_43, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk3_0,esk2_0),X1)=X1), inference(spm,[status(thm)],[c_0_22, c_0_39])).
% 5.26/5.41  fof(c_0_44, plain, ![X18, X19, X20]:(~r1_tarski(X18,k2_xboole_0(X19,X20))|r1_tarski(k4_xboole_0(X18,X19),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 5.26/5.41  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_40])).
% 5.26/5.41  cnf(c_0_46, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 5.26/5.41  cnf(c_0_47, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.26/5.41  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_39]), c_0_43])).
% 5.26/5.41  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 5.26/5.41  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_45, c_0_20])).
% 5.26/5.41  cnf(c_0_51, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_26, c_0_46])).
% 5.26/5.41  cnf(c_0_52, negated_conjecture, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_26])).
% 5.26/5.41  fof(c_0_53, plain, ![X25, X26, X27]:k4_xboole_0(X25,k4_xboole_0(X26,X27))=k2_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X25,X27)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 5.26/5.41  cnf(c_0_54, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 5.26/5.41  cnf(c_0_55, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_47, c_0_52])).
% 5.26/5.41  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 5.26/5.41  cnf(c_0_57, plain, (k2_xboole_0(k4_xboole_0(X1,X1),X2)=X2), inference(spm,[status(thm)],[c_0_22, c_0_54])).
% 5.26/5.41  cnf(c_0_58, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_55, c_0_54])).
% 5.26/5.41  cnf(c_0_59, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_56, c_0_29])).
% 5.26/5.41  cnf(c_0_60, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 5.26/5.41  cnf(c_0_61, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_57]), c_0_58])).
% 5.26/5.41  cnf(c_0_62, negated_conjecture, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X3,X1),X2))), inference(spm,[status(thm)],[c_0_42, c_0_48])).
% 5.26/5.41  cnf(c_0_63, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X1)=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_40])).
% 5.26/5.41  cnf(c_0_64, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_46])).
% 5.26/5.41  cnf(c_0_65, negated_conjecture, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 5.26/5.41  cnf(c_0_66, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_64]), c_0_58])).
% 5.26/5.41  cnf(c_0_67, negated_conjecture, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_65])).
% 5.26/5.41  cnf(c_0_68, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_26]), c_0_66])).
% 5.26/5.41  cnf(c_0_69, negated_conjecture, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_67]), c_0_67])).
% 5.26/5.41  cnf(c_0_70, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_51]), c_0_61])).
% 5.26/5.41  cnf(c_0_71, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 5.26/5.41  cnf(c_0_72, negated_conjecture, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3))=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 5.26/5.41  cnf(c_0_73, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_59, c_0_70])).
% 5.26/5.41  cnf(c_0_74, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_64, c_0_64])).
% 5.26/5.41  cnf(c_0_75, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_52]), c_0_71]), c_0_64])).
% 5.26/5.41  cnf(c_0_76, negated_conjecture, (k2_xboole_0(X1,k4_xboole_0(esk3_0,esk2_0))=X1), inference(spm,[status(thm)],[c_0_55, c_0_39])).
% 5.26/5.41  cnf(c_0_77, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_59]), c_0_73])).
% 5.26/5.41  cnf(c_0_78, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_74]), c_0_58])).
% 5.26/5.41  cnf(c_0_79, negated_conjecture, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_75]), c_0_51])).
% 5.26/5.41  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),X1)=k4_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_46, c_0_76])).
% 5.26/5.41  cnf(c_0_81, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_59]), c_0_77]), c_0_51]), c_0_57]), c_0_77]), c_0_51]), c_0_57])).
% 5.26/5.41  cnf(c_0_82, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_61])).
% 5.26/5.41  cnf(c_0_83, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=k4_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_80])).
% 5.26/5.41  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.26/5.41  cnf(c_0_85, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_26]), c_0_81]), c_0_82])).
% 5.26/5.41  cnf(c_0_86, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0)=k4_xboole_0(esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_34, c_0_83])).
% 5.26/5.41  cnf(c_0_87, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_71, c_0_75])).
% 5.26/5.41  cnf(c_0_88, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk3_0))=esk2_0), inference(spm,[status(thm)],[c_0_47, c_0_16])).
% 5.26/5.41  cnf(c_0_89, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[c_0_84, c_0_29])).
% 5.26/5.41  cnf(c_0_90, negated_conjecture, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(k4_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_52, c_0_85])).
% 5.26/5.41  cnf(c_0_91, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,X1)))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_86]), c_0_61])).
% 5.26/5.41  cnf(c_0_92, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_73, c_0_87])).
% 5.26/5.41  cnf(c_0_93, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[c_0_88, c_0_52])).
% 5.26/5.41  cnf(c_0_94, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_89, c_0_33])).
% 5.26/5.41  cnf(c_0_95, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_59, c_0_33])).
% 5.26/5.41  cnf(c_0_96, negated_conjecture, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(k4_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_90, c_0_69])).
% 5.26/5.41  cnf(c_0_97, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(X1,k4_xboole_0(esk3_0,X2)))=k2_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk3_0,X2))), inference(spm,[status(thm)],[c_0_59, c_0_91])).
% 5.26/5.41  cnf(c_0_98, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))=k2_xboole_0(k4_xboole_0(esk2_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 5.26/5.41  cnf(c_0_99, negated_conjecture, (k2_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)),k4_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_94, c_0_69])).
% 5.26/5.41  cnf(c_0_100, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_51]), c_0_57])).
% 5.26/5.41  cnf(c_0_101, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X1),X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_64]), c_0_85]), c_0_85]), c_0_96])).
% 5.26/5.41  cnf(c_0_102, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk3_0,k4_xboole_0(X2,X1)))=k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_66]), c_0_98]), c_0_69])).
% 5.26/5.41  cnf(c_0_103, negated_conjecture, (k2_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_99, c_0_100])).
% 5.26/5.41  cnf(c_0_104, negated_conjecture, (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(X3,k4_xboole_0(X3,X2))))=k2_xboole_0(X3,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_52, c_0_59])).
% 5.26/5.41  cnf(c_0_105, negated_conjecture, (k2_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))))=k4_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_66]), c_0_66])).
% 5.26/5.41  cnf(c_0_106, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_40])).
% 5.26/5.41  cnf(c_0_107, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk1_0))),k4_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_103, c_0_85])).
% 5.26/5.41  cnf(c_0_108, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))),k4_xboole_0(X1,esk2_0))=k4_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_85]), c_0_27]), c_0_85]), c_0_106]), c_0_68]), c_0_78]), c_0_51]), c_0_58])).
% 5.26/5.41  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108])]), ['proof']).
% 5.26/5.41  # SZS output end CNFRefutation
% 5.26/5.41  # Proof object total steps             : 110
% 5.26/5.41  # Proof object clause steps            : 85
% 5.26/5.41  # Proof object formula steps           : 25
% 5.26/5.41  # Proof object conjectures             : 47
% 5.26/5.41  # Proof object clause conjectures      : 44
% 5.26/5.41  # Proof object formula conjectures     : 3
% 5.26/5.41  # Proof object initial clauses used    : 13
% 5.26/5.41  # Proof object initial formulas used   : 12
% 5.26/5.41  # Proof object generating inferences   : 60
% 5.26/5.41  # Proof object simplifying inferences  : 56
% 5.26/5.41  # Training examples: 0 positive, 0 negative
% 5.26/5.41  # Parsed axioms                        : 13
% 5.26/5.41  # Removed by relevancy pruning/SinE    : 0
% 5.26/5.41  # Initial clauses                      : 14
% 5.26/5.41  # Removed in clause preprocessing      : 1
% 5.26/5.41  # Initial clauses in saturation        : 13
% 5.26/5.41  # Processed clauses                    : 29416
% 5.26/5.41  # ...of these trivial                  : 9765
% 5.26/5.41  # ...subsumed                          : 17403
% 5.26/5.41  # ...remaining for further processing  : 2248
% 5.26/5.41  # Other redundant clauses eliminated   : 0
% 5.26/5.41  # Clauses deleted for lack of memory   : 0
% 5.26/5.41  # Backward-subsumed                    : 32
% 5.26/5.41  # Backward-rewritten                   : 1019
% 5.26/5.41  # Generated clauses                    : 756861
% 5.26/5.41  # ...of the previous two non-trivial   : 436811
% 5.26/5.41  # Contextual simplify-reflections      : 0
% 5.26/5.41  # Paramodulations                      : 756861
% 5.26/5.41  # Factorizations                       : 0
% 5.26/5.41  # Equation resolutions                 : 0
% 5.26/5.41  # Propositional unsat checks           : 0
% 5.26/5.41  #    Propositional check models        : 0
% 5.26/5.41  #    Propositional check unsatisfiable : 0
% 5.26/5.41  #    Propositional clauses             : 0
% 5.26/5.41  #    Propositional clauses after purity: 0
% 5.26/5.41  #    Propositional unsat core size     : 0
% 5.26/5.41  #    Propositional preprocessing time  : 0.000
% 5.26/5.41  #    Propositional encoding time       : 0.000
% 5.26/5.41  #    Propositional solver time         : 0.000
% 5.26/5.41  #    Success case prop preproc time    : 0.000
% 5.26/5.41  #    Success case prop encoding time   : 0.000
% 5.26/5.41  #    Success case prop solver time     : 0.000
% 5.26/5.41  # Current number of processed clauses  : 1197
% 5.26/5.41  #    Positive orientable unit clauses  : 818
% 5.26/5.41  #    Positive unorientable unit clauses: 36
% 5.26/5.41  #    Negative unit clauses             : 0
% 5.26/5.41  #    Non-unit-clauses                  : 343
% 5.26/5.41  # Current number of unprocessed clauses: 379799
% 5.26/5.41  # ...number of literals in the above   : 442471
% 5.26/5.41  # Current number of archived formulas  : 0
% 5.26/5.41  # Current number of archived clauses   : 1052
% 5.26/5.41  # Clause-clause subsumption calls (NU) : 108885
% 5.26/5.41  # Rec. Clause-clause subsumption calls : 108885
% 5.26/5.41  # Non-unit clause-clause subsumptions  : 13271
% 5.26/5.41  # Unit Clause-clause subsumption calls : 3734
% 5.26/5.41  # Rewrite failures with RHS unbound    : 3879
% 5.26/5.41  # BW rewrite match attempts            : 22193
% 5.26/5.41  # BW rewrite match successes           : 4110
% 5.26/5.41  # Condensation attempts                : 0
% 5.26/5.41  # Condensation successes               : 0
% 5.26/5.41  # Termbank termtop insertions          : 10983340
% 5.26/5.43  
% 5.26/5.43  # -------------------------------------------------
% 5.26/5.43  # User time                : 4.838 s
% 5.26/5.43  # System time              : 0.255 s
% 5.26/5.43  # Total time               : 5.093 s
% 5.26/5.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
