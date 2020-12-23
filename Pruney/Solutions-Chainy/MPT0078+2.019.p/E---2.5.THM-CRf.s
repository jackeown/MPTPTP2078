%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:58 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  103 (1011 expanded)
%              Number of clauses        :   76 ( 457 expanded)
%              Number of leaves         :   13 ( 270 expanded)
%              Depth                    :   16
%              Number of atoms          :  156 (1436 expanded)
%              Number of equality atoms :   70 ( 926 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t71_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_13,plain,(
    ! [X19] : k3_xboole_0(X19,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_14,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X28,X29] : k2_xboole_0(k3_xboole_0(X28,X29),k4_xboole_0(X28,X29)) = X28 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_16,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_20,plain,(
    ! [X18] : k2_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_21,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X20,X21] : k2_xboole_0(X20,k4_xboole_0(X21,X20)) = k2_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] : k4_xboole_0(k4_xboole_0(X23,X24),X25) = k4_xboole_0(X23,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X3,X2) )
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t71_xboole_1])).

cnf(c_0_33,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_36,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29]),c_0_31]),c_0_29])).

fof(c_0_40,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_41,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk4_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & esk3_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_34])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_31])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_18])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_44]),c_0_33])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = k2_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_29]),c_0_29])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_55,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_57,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk4_0),esk5_0)
    | k4_xboole_0(X1,k2_xboole_0(esk4_0,esk3_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_27]),c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_43]),c_0_27])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_43])).

cnf(c_0_65,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_31])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_53])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_68,plain,
    ( X1 = X2
    | r2_hidden(esk2_1(X2),X2)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_44])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_44])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_29])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_44])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk5_0,esk4_0),k4_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_35]),c_0_27])).

cnf(c_0_76,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(X1,esk5_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_34])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk5_0,esk4_0)) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_74]),c_0_29])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk4_0),k2_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_79])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_44]),c_0_28])).

cnf(c_0_86,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_43]),c_0_28]),c_0_29])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_34]),c_0_31]),c_0_53]),c_0_43]),c_0_34]),c_0_31]),c_0_53]),c_0_43]),c_0_69])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_29])).

cnf(c_0_91,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_1(k4_xboole_0(k2_xboole_0(X1,X2),X2)),k4_xboole_0(k2_xboole_0(X1,X2),X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_87]),c_0_56])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),X2))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk5_0,X1)) = k2_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_90])).

cnf(c_0_95,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_34])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_91]),c_0_72]),c_0_72]),c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,X2))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_35]),c_0_28])).

cnf(c_0_99,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk5_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_99]),c_0_100]),c_0_101]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.07/1.25  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 1.07/1.25  # and selection function SelectLargestOrientable.
% 1.07/1.25  #
% 1.07/1.25  # Preprocessing time       : 0.027 s
% 1.07/1.25  # Presaturation interreduction done
% 1.07/1.25  
% 1.07/1.25  # Proof found!
% 1.07/1.25  # SZS status Theorem
% 1.07/1.25  # SZS output start CNFRefutation
% 1.07/1.25  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.07/1.25  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.07/1.25  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.07/1.25  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.07/1.25  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.07/1.25  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.07/1.25  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.07/1.25  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.07/1.25  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.07/1.25  fof(t71_xboole_1, conjecture, ![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 1.07/1.25  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.07/1.25  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.07/1.25  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.07/1.25  fof(c_0_13, plain, ![X19]:k3_xboole_0(X19,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 1.07/1.25  fof(c_0_14, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.07/1.25  fof(c_0_15, plain, ![X28, X29]:k2_xboole_0(k3_xboole_0(X28,X29),k4_xboole_0(X28,X29))=X28, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 1.07/1.25  fof(c_0_16, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.07/1.25  cnf(c_0_17, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.07/1.25  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.07/1.25  fof(c_0_19, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.07/1.25  fof(c_0_20, plain, ![X18]:k2_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t1_boole])).
% 1.07/1.25  fof(c_0_21, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.07/1.25  cnf(c_0_22, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.07/1.25  fof(c_0_23, plain, ![X20, X21]:k2_xboole_0(X20,k4_xboole_0(X21,X20))=k2_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.07/1.25  cnf(c_0_24, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.07/1.25  fof(c_0_25, plain, ![X23, X24, X25]:k4_xboole_0(k4_xboole_0(X23,X24),X25)=k4_xboole_0(X23,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.07/1.25  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 1.07/1.25  cnf(c_0_27, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.07/1.25  cnf(c_0_28, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.07/1.25  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.25  cnf(c_0_30, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_22, c_0_18])).
% 1.07/1.25  cnf(c_0_31, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.07/1.25  fof(c_0_32, negated_conjecture, ~(![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3)), inference(assume_negation,[status(cth)],[t71_xboole_1])).
% 1.07/1.25  cnf(c_0_33, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_24, c_0_18])).
% 1.07/1.25  cnf(c_0_34, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.07/1.25  cnf(c_0_35, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 1.07/1.25  fof(c_0_36, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 1.07/1.25  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.07/1.25  cnf(c_0_38, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.07/1.25  cnf(c_0_39, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_29]), c_0_31]), c_0_29])).
% 1.07/1.25  fof(c_0_40, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.07/1.25  fof(c_0_41, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk4_0)&r1_xboole_0(esk3_0,esk4_0))&r1_xboole_0(esk5_0,esk4_0))&esk3_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 1.07/1.25  cnf(c_0_42, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))))|~r1_xboole_0(k4_xboole_0(X2,X3),X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_34])).
% 1.07/1.25  cnf(c_0_43, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_31])).
% 1.07/1.25  cnf(c_0_44, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.07/1.25  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_37, c_0_18])).
% 1.07/1.25  cnf(c_0_46, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.07/1.25  cnf(c_0_47, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.07/1.25  cnf(c_0_48, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.07/1.25  cnf(c_0_49, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k4_xboole_0(X2,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_28])).
% 1.07/1.25  cnf(c_0_50, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_44]), c_0_33])).
% 1.07/1.25  cnf(c_0_51, plain, (r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)|r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_46])).
% 1.07/1.25  cnf(c_0_52, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_34])).
% 1.07/1.25  cnf(c_0_53, negated_conjecture, (k2_xboole_0(esk4_0,esk5_0)=k2_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_29]), c_0_29])).
% 1.07/1.25  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 1.07/1.25  cnf(c_0_55, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.07/1.25  cnf(c_0_56, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.07/1.25  fof(c_0_57, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,X17)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.07/1.25  cnf(c_0_58, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk4_0),esk5_0)|k4_xboole_0(X1,k2_xboole_0(esk4_0,esk3_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.07/1.25  cnf(c_0_59, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_27]), c_0_35])).
% 1.07/1.25  cnf(c_0_60, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.07/1.25  cnf(c_0_61, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_43]), c_0_27])).
% 1.07/1.25  cnf(c_0_62, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_34]), c_0_34]), c_0_34])).
% 1.07/1.25  cnf(c_0_63, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.07/1.25  cnf(c_0_64, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_58, c_0_43])).
% 1.07/1.25  cnf(c_0_65, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))|k4_xboole_0(X1,k2_xboole_0(X2,X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_31])).
% 1.07/1.25  cnf(c_0_66, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_53])).
% 1.07/1.25  cnf(c_0_67, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 1.07/1.25  cnf(c_0_68, plain, (X1=X2|r2_hidden(esk2_1(X2),X2)|r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_44, c_0_44])).
% 1.07/1.25  cnf(c_0_69, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 1.07/1.25  cnf(c_0_70, negated_conjecture, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_60, c_0_44])).
% 1.07/1.25  cnf(c_0_71, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_62])).
% 1.07/1.25  cnf(c_0_72, negated_conjecture, (k2_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_29])).
% 1.07/1.25  cnf(c_0_73, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_47, c_0_44])).
% 1.07/1.25  cnf(c_0_74, negated_conjecture, (r1_tarski(k4_xboole_0(esk5_0,esk4_0),k4_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.07/1.25  cnf(c_0_75, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_35]), c_0_27])).
% 1.07/1.25  cnf(c_0_76, plain, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 1.07/1.25  cnf(c_0_77, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_70])).
% 1.07/1.25  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.07/1.25  cnf(c_0_79, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(X1,esk5_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_34])).
% 1.07/1.25  cnf(c_0_80, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_63, c_0_73])).
% 1.07/1.25  cnf(c_0_81, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk5_0,esk4_0))=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_74]), c_0_29])).
% 1.07/1.25  cnf(c_0_82, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 1.07/1.25  cnf(c_0_83, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 1.07/1.25  cnf(c_0_84, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk4_0),k2_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_79])).
% 1.07/1.25  cnf(c_0_85, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_44]), c_0_28])).
% 1.07/1.25  cnf(c_0_86, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_43]), c_0_28]), c_0_29])).
% 1.07/1.25  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk5_0,esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_34]), c_0_31]), c_0_53]), c_0_43]), c_0_34]), c_0_31]), c_0_53]), c_0_43]), c_0_69])).
% 1.07/1.25  cnf(c_0_88, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))|~r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 1.07/1.25  cnf(c_0_89, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 1.07/1.25  cnf(c_0_90, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_84, c_0_29])).
% 1.07/1.25  cnf(c_0_91, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_1(k4_xboole_0(k2_xboole_0(X1,X2),X2)),k4_xboole_0(k2_xboole_0(X1,X2),X2))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 1.07/1.25  cnf(c_0_92, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_87]), c_0_56])])).
% 1.07/1.25  cnf(c_0_93, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),X2)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 1.07/1.25  cnf(c_0_94, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk5_0,X1))=k2_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_90])).
% 1.07/1.25  cnf(c_0_95, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_31, c_0_34])).
% 1.07/1.25  cnf(c_0_96, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk5_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_91]), c_0_72]), c_0_72]), c_0_92])).
% 1.07/1.25  cnf(c_0_97, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,X2)))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 1.07/1.25  cnf(c_0_98, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_35]), c_0_28])).
% 1.07/1.25  cnf(c_0_99, negated_conjecture, (k2_xboole_0(esk3_0,esk5_0)=esk3_0), inference(spm,[status(thm)],[c_0_39, c_0_96])).
% 1.07/1.25  cnf(c_0_100, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.07/1.25  cnf(c_0_101, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 1.07/1.25  cnf(c_0_102, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_99]), c_0_100]), c_0_101]), ['proof']).
% 1.07/1.25  # SZS output end CNFRefutation
% 1.07/1.25  # Proof object total steps             : 103
% 1.07/1.25  # Proof object clause steps            : 76
% 1.07/1.25  # Proof object formula steps           : 27
% 1.07/1.25  # Proof object conjectures             : 32
% 1.07/1.25  # Proof object clause conjectures      : 29
% 1.07/1.25  # Proof object formula conjectures     : 3
% 1.07/1.25  # Proof object initial clauses used    : 17
% 1.07/1.25  # Proof object initial formulas used   : 13
% 1.07/1.25  # Proof object generating inferences   : 51
% 1.07/1.25  # Proof object simplifying inferences  : 46
% 1.07/1.25  # Training examples: 0 positive, 0 negative
% 1.07/1.25  # Parsed axioms                        : 13
% 1.07/1.25  # Removed by relevancy pruning/SinE    : 0
% 1.07/1.25  # Initial clauses                      : 18
% 1.07/1.25  # Removed in clause preprocessing      : 1
% 1.07/1.25  # Initial clauses in saturation        : 17
% 1.07/1.25  # Processed clauses                    : 8067
% 1.07/1.25  # ...of these trivial                  : 476
% 1.07/1.25  # ...subsumed                          : 6763
% 1.07/1.25  # ...remaining for further processing  : 828
% 1.07/1.25  # Other redundant clauses eliminated   : 306
% 1.07/1.25  # Clauses deleted for lack of memory   : 0
% 1.07/1.25  # Backward-subsumed                    : 28
% 1.07/1.25  # Backward-rewritten                   : 264
% 1.07/1.25  # Generated clauses                    : 108380
% 1.07/1.25  # ...of the previous two non-trivial   : 73733
% 1.07/1.25  # Contextual simplify-reflections      : 1
% 1.07/1.25  # Paramodulations                      : 108049
% 1.07/1.25  # Factorizations                       : 24
% 1.07/1.25  # Equation resolutions                 : 306
% 1.07/1.25  # Propositional unsat checks           : 0
% 1.07/1.25  #    Propositional check models        : 0
% 1.07/1.25  #    Propositional check unsatisfiable : 0
% 1.07/1.25  #    Propositional clauses             : 0
% 1.07/1.25  #    Propositional clauses after purity: 0
% 1.07/1.25  #    Propositional unsat core size     : 0
% 1.07/1.25  #    Propositional preprocessing time  : 0.000
% 1.07/1.25  #    Propositional encoding time       : 0.000
% 1.07/1.25  #    Propositional solver time         : 0.000
% 1.07/1.25  #    Success case prop preproc time    : 0.000
% 1.07/1.25  #    Success case prop encoding time   : 0.000
% 1.07/1.25  #    Success case prop solver time     : 0.000
% 1.07/1.25  # Current number of processed clauses  : 518
% 1.07/1.25  #    Positive orientable unit clauses  : 185
% 1.07/1.25  #    Positive unorientable unit clauses: 3
% 1.07/1.25  #    Negative unit clauses             : 41
% 1.07/1.25  #    Non-unit-clauses                  : 289
% 1.07/1.25  # Current number of unprocessed clauses: 64795
% 1.07/1.25  # ...number of literals in the above   : 189319
% 1.07/1.25  # Current number of archived formulas  : 0
% 1.07/1.25  # Current number of archived clauses   : 311
% 1.07/1.25  # Clause-clause subsumption calls (NU) : 63233
% 1.07/1.25  # Rec. Clause-clause subsumption calls : 35229
% 1.07/1.25  # Non-unit clause-clause subsumptions  : 3189
% 1.07/1.25  # Unit Clause-clause subsumption calls : 4541
% 1.07/1.25  # Rewrite failures with RHS unbound    : 0
% 1.07/1.25  # BW rewrite match attempts            : 1124
% 1.07/1.25  # BW rewrite match successes           : 256
% 1.07/1.25  # Condensation attempts                : 0
% 1.07/1.25  # Condensation successes               : 0
% 1.07/1.25  # Termbank termtop insertions          : 1624047
% 1.07/1.25  
% 1.07/1.25  # -------------------------------------------------
% 1.07/1.25  # User time                : 0.863 s
% 1.07/1.25  # System time              : 0.043 s
% 1.07/1.25  # Total time               : 0.906 s
% 1.07/1.25  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
