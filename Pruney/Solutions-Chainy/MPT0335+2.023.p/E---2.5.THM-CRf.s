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
% DateTime   : Thu Dec  3 10:44:43 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 955 expanded)
%              Number of clauses        :   71 ( 431 expanded)
%              Number of leaves         :   17 ( 246 expanded)
%              Depth                    :   15
%              Number of atoms          :  131 (1403 expanded)
%              Number of equality atoms :  103 ( 965 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t53_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t46_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(t111_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    & k3_xboole_0(esk3_0,esk4_0) = k1_tarski(esk5_0)
    & r2_hidden(esk5_0,esk2_0)
    & k3_xboole_0(esk2_0,esk4_0) != k1_tarski(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k3_xboole_0(X13,X14) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_21,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_22,plain,(
    ! [X21,X22] : k4_xboole_0(k2_xboole_0(X21,X22),X22) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] : k4_xboole_0(k4_xboole_0(X23,X24),X25) = k4_xboole_0(X23,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_26,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k3_xboole_0(X28,X29)) = k4_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X20,X19)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_32,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_33,plain,(
    ! [X38,X39,X40] : k4_xboole_0(X38,k2_xboole_0(X39,X40)) = k3_xboole_0(k4_xboole_0(X38,X39),k4_xboole_0(X38,X40)) ),
    inference(variable_rename,[status(thm)],[t53_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk3_0) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk2_0),esk3_0) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_43,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_38]),c_0_40])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,esk2_0),esk3_0) = k4_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_30]),c_0_42])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k4_xboole_0(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_51,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | k2_xboole_0(k1_tarski(X51),X52) = X52 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).

fof(c_0_52,plain,(
    ! [X50] : k2_tarski(X50,X50) = k1_tarski(X50) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_53,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),esk2_0) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_46])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,X1),esk3_0) = k4_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_60,plain,(
    ! [X32,X33,X34] : k3_xboole_0(X32,k4_xboole_0(X33,X34)) = k4_xboole_0(k3_xboole_0(X32,X33),X34) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_61,plain,(
    ! [X15,X16] :
      ( k4_xboole_0(X15,X16) != k4_xboole_0(X16,X15)
      | X15 = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk3_0) = k4_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_38]),c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),esk3_0) = k4_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_54]),c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk2_0),k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_56])).

fof(c_0_68,plain,(
    ! [X8,X9,X10] : k4_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X9)) = k3_xboole_0(k4_xboole_0(X8,X10),X9) ),
    inference(variable_rename,[status(thm)],[t111_xboole_1])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = k2_tarski(esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_58]),c_0_28])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_38])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0))) = k4_xboole_0(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_50])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_28]),c_0_28])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk2_0,esk2_0)) = k4_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_62]),c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk2_0),X1) = k4_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_67]),c_0_55])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_28]),c_0_28])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,X2) = X2
    | k4_xboole_0(k4_xboole_0(X2,X1),X2) != k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_30]),c_0_34])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)),k4_xboole_0(esk2_0,esk2_0)) = k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_49])).

cnf(c_0_85,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,esk2_0),esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_76])).

cnf(c_0_86,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_30])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),X1) = k4_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_65]),c_0_79]),c_0_79])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk2_0))) = k4_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_81]),c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)) = esk3_0
    | k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0))) != k4_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_38]),c_0_85]),c_0_79])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0))) = k4_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_84]),c_0_79]),c_0_79])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk2_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_49])).

cnf(c_0_93,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) = k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
    inference(rw,[status(thm)],[c_0_88,c_0_82])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk2_0)) = k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

cnf(c_0_96,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,esk2_0),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_98,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_93]),c_0_77]),c_0_44])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk2_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_96]),c_0_79])).

cnf(c_0_101,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_40])).

cnf(c_0_102,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)) != k2_tarski(esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_58]),c_0_28])).

cnf(c_0_103,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = k4_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),c_0_65]),c_0_101]),c_0_42])).

cnf(c_0_104,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) != k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_102,c_0_71])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_103]),c_0_77]),c_0_104]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.21/0.51  # and selection function SelectCQArNTNpEqFirst.
% 0.21/0.51  #
% 0.21/0.51  # Preprocessing time       : 0.027 s
% 0.21/0.51  # Presaturation interreduction done
% 0.21/0.51  
% 0.21/0.51  # Proof found!
% 0.21/0.51  # SZS status Theorem
% 0.21/0.51  # SZS output start CNFRefutation
% 0.21/0.51  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 0.21/0.51  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.51  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.51  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.51  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.21/0.51  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.21/0.51  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.21/0.51  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.21/0.51  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.21/0.51  fof(t53_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 0.21/0.51  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.51  fof(t46_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.21/0.51  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.51  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.51  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.21/0.51  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.21/0.51  fof(t111_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_xboole_1)).
% 0.21/0.51  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 0.21/0.51  fof(c_0_18, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.51  fof(c_0_19, negated_conjecture, (((r1_tarski(esk2_0,esk3_0)&k3_xboole_0(esk3_0,esk4_0)=k1_tarski(esk5_0))&r2_hidden(esk5_0,esk2_0))&k3_xboole_0(esk2_0,esk4_0)!=k1_tarski(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.21/0.51  fof(c_0_20, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k3_xboole_0(X13,X14)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.51  fof(c_0_21, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.51  fof(c_0_22, plain, ![X21, X22]:k4_xboole_0(k2_xboole_0(X21,X22),X22)=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.21/0.51  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.51  cnf(c_0_24, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.51  fof(c_0_25, plain, ![X23, X24, X25]:k4_xboole_0(k4_xboole_0(X23,X24),X25)=k4_xboole_0(X23,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.21/0.51  fof(c_0_26, plain, ![X28, X29]:k4_xboole_0(X28,k3_xboole_0(X28,X29))=k4_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.21/0.51  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.51  fof(c_0_29, plain, ![X19, X20]:k2_xboole_0(X19,k4_xboole_0(X20,X19))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.21/0.51  cnf(c_0_30, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.51  cnf(c_0_31, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.51  fof(c_0_32, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.21/0.51  fof(c_0_33, plain, ![X38, X39, X40]:k4_xboole_0(X38,k2_xboole_0(X39,X40))=k3_xboole_0(k4_xboole_0(X38,X39),k4_xboole_0(X38,X40)), inference(variable_rename,[status(thm)],[t53_xboole_1])).
% 0.21/0.51  cnf(c_0_34, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.51  fof(c_0_35, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.51  cnf(c_0_36, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.51  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.51  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.51  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk3_0,esk3_0)=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.51  cnf(c_0_40, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.51  cnf(c_0_41, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.51  cnf(c_0_42, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk2_0),esk3_0)=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.21/0.51  cnf(c_0_43, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.51  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_28])).
% 0.21/0.51  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))=esk2_0), inference(spm,[status(thm)],[c_0_37, c_0_24])).
% 0.21/0.51  cnf(c_0_46, negated_conjecture, (k2_xboole_0(esk3_0,esk2_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_38]), c_0_40])).
% 0.21/0.51  cnf(c_0_47, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_41, c_0_28])).
% 0.21/0.51  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,esk2_0),esk3_0)=k4_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_30]), c_0_42])).
% 0.21/0.51  cnf(c_0_49, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_23, c_0_43])).
% 0.21/0.51  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k4_xboole_0(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.51  fof(c_0_51, plain, ![X51, X52]:(~r2_hidden(X51,X52)|k2_xboole_0(k1_tarski(X51),X52)=X52), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).
% 0.21/0.51  fof(c_0_52, plain, ![X50]:k2_tarski(X50,X50)=k1_tarski(X50), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.51  fof(c_0_53, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.51  cnf(c_0_54, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),esk2_0)=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_46])).
% 0.21/0.51  cnf(c_0_55, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_47, c_0_34])).
% 0.21/0.51  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,X1),esk3_0)=k4_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.21/0.51  cnf(c_0_57, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.51  cnf(c_0_58, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.51  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.51  fof(c_0_60, plain, ![X32, X33, X34]:k3_xboole_0(X32,k4_xboole_0(X33,X34))=k4_xboole_0(k3_xboole_0(X32,X33),X34), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.21/0.51  fof(c_0_61, plain, ![X15, X16]:(k4_xboole_0(X15,X16)!=k4_xboole_0(X16,X15)|X15=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 0.21/0.51  cnf(c_0_62, negated_conjecture, (k4_xboole_0(esk3_0,esk3_0)=k4_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_39, c_0_50])).
% 0.21/0.51  cnf(c_0_63, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_39])).
% 0.21/0.51  cnf(c_0_64, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.51  cnf(c_0_65, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_38]), c_0_34])).
% 0.21/0.51  cnf(c_0_66, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),esk3_0)=k4_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_54]), c_0_55])).
% 0.21/0.51  cnf(c_0_67, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk2_0),k4_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_43, c_0_56])).
% 0.21/0.51  fof(c_0_68, plain, ![X8, X9, X10]:k4_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X9))=k3_xboole_0(k4_xboole_0(X8,X10),X9), inference(variable_rename,[status(thm)],[t111_xboole_1])).
% 0.21/0.51  cnf(c_0_69, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.51  cnf(c_0_70, negated_conjecture, (r2_hidden(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.51  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=k2_tarski(esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_58]), c_0_28])).
% 0.21/0.51  cnf(c_0_72, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.51  cnf(c_0_73, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.51  cnf(c_0_74, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_30, c_0_38])).
% 0.21/0.51  cnf(c_0_75, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)))=k4_xboole_0(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_44, c_0_62])).
% 0.21/0.51  cnf(c_0_76, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_63, c_0_50])).
% 0.21/0.51  cnf(c_0_77, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_28]), c_0_28])).
% 0.21/0.51  cnf(c_0_78, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk2_0,esk2_0))=k4_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_62]), c_0_66])).
% 0.21/0.51  cnf(c_0_79, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk2_0),X1)=k4_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_67]), c_0_55])).
% 0.21/0.51  cnf(c_0_80, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.51  cnf(c_0_81, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.21/0.51  cnf(c_0_82, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_28]), c_0_28])).
% 0.21/0.51  cnf(c_0_83, plain, (k2_xboole_0(X1,X2)=X2|k4_xboole_0(k4_xboole_0(X2,X1),X2)!=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_30]), c_0_34])).
% 0.21/0.51  cnf(c_0_84, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)),k4_xboole_0(esk2_0,esk2_0))=k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_49])).
% 0.21/0.51  cnf(c_0_85, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,esk2_0),esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_76])).
% 0.21/0.51  cnf(c_0_86, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_30])).
% 0.21/0.51  cnf(c_0_87, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),X1)=k4_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_65]), c_0_79]), c_0_79])).
% 0.21/0.51  cnf(c_0_88, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X2)))=k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_28]), c_0_28]), c_0_28])).
% 0.21/0.51  cnf(c_0_89, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk2_0)))=k4_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_81]), c_0_82])).
% 0.21/0.51  cnf(c_0_90, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0))=esk3_0|k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)))!=k4_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_38]), c_0_85]), c_0_79])).
% 0.21/0.51  cnf(c_0_91, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0)))=k4_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_84]), c_0_79]), c_0_79])).
% 0.21/0.51  cnf(c_0_92, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk2_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_49])).
% 0.21/0.51  cnf(c_0_93, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))))=k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2))), inference(rw,[status(thm)],[c_0_88, c_0_82])).
% 0.21/0.51  cnf(c_0_94, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk2_0))=k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_44, c_0_89])).
% 0.21/0.51  cnf(c_0_95, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk2_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 0.21/0.51  cnf(c_0_96, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,esk2_0),X1)=X1), inference(spm,[status(thm)],[c_0_23, c_0_92])).
% 0.21/0.51  cnf(c_0_97, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.51  cnf(c_0_98, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_93]), c_0_77]), c_0_44])).
% 0.21/0.51  cnf(c_0_99, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk2_0))=esk3_0), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 0.21/0.51  cnf(c_0_100, negated_conjecture, (k4_xboole_0(X1,X1)=k4_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_96]), c_0_79])).
% 0.21/0.51  cnf(c_0_101, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_40])).
% 0.21/0.51  cnf(c_0_102, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))!=k2_tarski(esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_58]), c_0_28])).
% 0.21/0.51  cnf(c_0_103, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=k4_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), c_0_65]), c_0_101]), c_0_42])).
% 0.21/0.51  cnf(c_0_104, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))!=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))), inference(rw,[status(thm)],[c_0_102, c_0_71])).
% 0.21/0.51  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_103]), c_0_77]), c_0_104]), ['proof']).
% 0.21/0.51  # SZS output end CNFRefutation
% 0.21/0.51  # Proof object total steps             : 106
% 0.21/0.51  # Proof object clause steps            : 71
% 0.21/0.51  # Proof object formula steps           : 35
% 0.21/0.51  # Proof object conjectures             : 42
% 0.21/0.51  # Proof object clause conjectures      : 39
% 0.21/0.51  # Proof object formula conjectures     : 3
% 0.21/0.51  # Proof object initial clauses used    : 20
% 0.21/0.51  # Proof object initial formulas used   : 17
% 0.21/0.51  # Proof object generating inferences   : 35
% 0.21/0.51  # Proof object simplifying inferences  : 53
% 0.21/0.51  # Training examples: 0 positive, 0 negative
% 0.21/0.51  # Parsed axioms                        : 21
% 0.21/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.51  # Initial clauses                      : 31
% 0.21/0.51  # Removed in clause preprocessing      : 2
% 0.21/0.51  # Initial clauses in saturation        : 29
% 0.21/0.51  # Processed clauses                    : 961
% 0.21/0.51  # ...of these trivial                  : 32
% 0.21/0.51  # ...subsumed                          : 658
% 0.21/0.51  # ...remaining for further processing  : 270
% 0.21/0.51  # Other redundant clauses eliminated   : 6
% 0.21/0.51  # Clauses deleted for lack of memory   : 0
% 0.21/0.51  # Backward-subsumed                    : 1
% 0.21/0.51  # Backward-rewritten                   : 89
% 0.21/0.51  # Generated clauses                    : 9231
% 0.21/0.51  # ...of the previous two non-trivial   : 7272
% 0.21/0.51  # Contextual simplify-reflections      : 0
% 0.21/0.51  # Paramodulations                      : 9225
% 0.21/0.51  # Factorizations                       : 0
% 0.21/0.51  # Equation resolutions                 : 8
% 0.21/0.51  # Propositional unsat checks           : 0
% 0.21/0.51  #    Propositional check models        : 0
% 0.21/0.51  #    Propositional check unsatisfiable : 0
% 0.21/0.51  #    Propositional clauses             : 0
% 0.21/0.51  #    Propositional clauses after purity: 0
% 0.21/0.51  #    Propositional unsat core size     : 0
% 0.21/0.51  #    Propositional preprocessing time  : 0.000
% 0.21/0.51  #    Propositional encoding time       : 0.000
% 0.21/0.51  #    Propositional solver time         : 0.000
% 0.21/0.51  #    Success case prop preproc time    : 0.000
% 0.21/0.51  #    Success case prop encoding time   : 0.000
% 0.21/0.51  #    Success case prop solver time     : 0.000
% 0.21/0.51  # Current number of processed clauses  : 148
% 0.21/0.51  #    Positive orientable unit clauses  : 76
% 0.21/0.51  #    Positive unorientable unit clauses: 2
% 0.21/0.51  #    Negative unit clauses             : 45
% 0.21/0.51  #    Non-unit-clauses                  : 25
% 0.21/0.51  # Current number of unprocessed clauses: 6277
% 0.21/0.51  # ...number of literals in the above   : 6790
% 0.21/0.51  # Current number of archived formulas  : 0
% 0.21/0.51  # Current number of archived clauses   : 120
% 0.21/0.51  # Clause-clause subsumption calls (NU) : 87
% 0.21/0.51  # Rec. Clause-clause subsumption calls : 87
% 0.21/0.51  # Non-unit clause-clause subsumptions  : 17
% 0.21/0.51  # Unit Clause-clause subsumption calls : 549
% 0.21/0.51  # Rewrite failures with RHS unbound    : 5
% 0.21/0.51  # BW rewrite match attempts            : 1094
% 0.21/0.51  # BW rewrite match successes           : 115
% 0.21/0.51  # Condensation attempts                : 0
% 0.21/0.51  # Condensation successes               : 0
% 0.21/0.51  # Termbank termtop insertions          : 153955
% 0.21/0.51  
% 0.21/0.51  # -------------------------------------------------
% 0.21/0.51  # User time                : 0.144 s
% 0.21/0.51  # System time              : 0.019 s
% 0.21/0.51  # Total time               : 0.163 s
% 0.21/0.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
