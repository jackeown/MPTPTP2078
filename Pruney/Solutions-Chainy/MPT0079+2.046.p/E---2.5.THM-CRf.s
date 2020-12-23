%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:06 EST 2020

% Result     : Theorem 1.03s
% Output     : CNFRefutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  123 (1580 expanded)
%              Number of clauses        :   94 ( 724 expanded)
%              Number of leaves         :   14 ( 413 expanded)
%              Depth                    :   24
%              Number of atoms          :  171 (2321 expanded)
%              Number of equality atoms :   78 (1393 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_14,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_15,plain,(
    ! [X29,X30] : k4_xboole_0(X29,k4_xboole_0(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X17] : k2_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_17,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X21] : k4_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_21,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r1_xboole_0(X9,X10)
        | r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X14,k3_xboole_0(X12,X13))
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_22,plain,(
    ! [X22,X23] : k4_xboole_0(k2_xboole_0(X22,X23),X23) = k4_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_28,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k3_xboole_0(X27,X28)) = k4_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk2_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_35,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & r1_xboole_0(esk5_0,esk3_0)
    & r1_xboole_0(esk6_0,esk4_0)
    & esk5_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

fof(c_0_41,plain,(
    ! [X31,X32,X33] : k2_xboole_0(k2_xboole_0(X31,X32),X33) = k2_xboole_0(X31,k2_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_42,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X20,X19)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_19])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_26])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_37])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_26])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_44])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_39])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) = k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_48])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_34]),c_0_23])).

fof(c_0_57,plain,(
    ! [X24,X25,X26] : k4_xboole_0(k4_xboole_0(X24,X25),X26) = k4_xboole_0(X24,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_39])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_38])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_26]),c_0_34]),c_0_34])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_49]),c_0_24])).

cnf(c_0_63,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_49])).

cnf(c_0_65,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_34])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_48])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_63])).

cnf(c_0_71,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_67])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_63])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_24])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(esk5_0,esk6_0)),esk3_0) = k4_xboole_0(k2_xboole_0(X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_49])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_63])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_54])).

cnf(c_0_82,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_34]),c_0_23]),c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk3_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_24]),c_0_64]),c_0_24])).

cnf(c_0_84,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk4_0,esk3_0)) = k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_77]),c_0_73])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_32])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk6_0,esk4_0),X2))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,plain,
    ( r2_hidden(esk1_2(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))
    | r1_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_44])).

cnf(c_0_89,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk3_0))) = k2_xboole_0(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_48]),c_0_84])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_26])).

cnf(c_0_91,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_48])).

cnf(c_0_92,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_76]),c_0_49]),c_0_24])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( r1_xboole_0(esk6_0,k4_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk6_0,esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk6_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_24]),c_0_91]),c_0_24]),c_0_92]),c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_49])).

cnf(c_0_97,negated_conjecture,
    ( r1_xboole_0(esk6_0,k4_xboole_0(esk6_0,k2_xboole_0(X1,k4_xboole_0(esk6_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_24])).

cnf(c_0_98,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_95]),c_0_96])).

cnf(c_0_99,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_63]),c_0_50])).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(esk6_0,k4_xboole_0(esk6_0,k2_xboole_0(X1,k4_xboole_0(esk3_0,esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

fof(c_0_101,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_102,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_99]),c_0_26])).

cnf(c_0_103,negated_conjecture,
    ( r1_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_82])).

cnf(c_0_104,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_105,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_38]),c_0_23])).

cnf(c_0_106,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_48])).

cnf(c_0_107,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk6_0,esk3_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_103]),c_0_44])).

cnf(c_0_108,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_54])).

cnf(c_0_109,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) = k2_xboole_0(esk5_0,esk3_0)
    | r2_hidden(esk2_1(k4_xboole_0(esk6_0,esk3_0)),k4_xboole_0(esk6_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) = k2_xboole_0(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_113,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X2))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_111])).

cnf(c_0_114,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = k4_xboole_0(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_112]),c_0_32])).

cnf(c_0_115,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(X2,k4_xboole_0(esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_113,c_0_24])).

cnf(c_0_116,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = k4_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_95]),c_0_32])).

cnf(c_0_117,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk3_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(X2,k4_xboole_0(esk5_0,esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk4_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_90]),c_0_24]),c_0_93])).

cnf(c_0_120,negated_conjecture,
    ( esk5_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_121,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_82])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_119]),c_0_120]),c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.03/1.21  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 1.03/1.21  # and selection function SelectLargestOrientable.
% 1.03/1.21  #
% 1.03/1.21  # Preprocessing time       : 0.038 s
% 1.03/1.21  # Presaturation interreduction done
% 1.03/1.21  
% 1.03/1.21  # Proof found!
% 1.03/1.21  # SZS status Theorem
% 1.03/1.21  # SZS output start CNFRefutation
% 1.03/1.21  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.03/1.21  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.03/1.21  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.03/1.21  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.03/1.21  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.03/1.21  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.03/1.21  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.03/1.21  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 1.03/1.21  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.03/1.21  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.03/1.21  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.03/1.21  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.03/1.21  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.03/1.21  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.03/1.21  fof(c_0_14, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 1.03/1.21  fof(c_0_15, plain, ![X29, X30]:k4_xboole_0(X29,k4_xboole_0(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.03/1.21  fof(c_0_16, plain, ![X17]:k2_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t1_boole])).
% 1.03/1.21  fof(c_0_17, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.03/1.21  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.03/1.21  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.03/1.21  fof(c_0_20, plain, ![X21]:k4_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.03/1.21  fof(c_0_21, plain, ![X9, X10, X12, X13, X14]:((r1_xboole_0(X9,X10)|r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)))&(~r2_hidden(X14,k3_xboole_0(X12,X13))|~r1_xboole_0(X12,X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.03/1.21  fof(c_0_22, plain, ![X22, X23]:k4_xboole_0(k2_xboole_0(X22,X23),X23)=k4_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 1.03/1.21  cnf(c_0_23, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.03/1.21  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.03/1.21  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 1.03/1.21  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.03/1.21  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 1.03/1.21  fof(c_0_28, plain, ![X27, X28]:k4_xboole_0(X27,k3_xboole_0(X27,X28))=k4_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 1.03/1.21  cnf(c_0_29, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.03/1.21  fof(c_0_30, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk2_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 1.03/1.21  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.03/1.21  cnf(c_0_32, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.03/1.21  cnf(c_0_33, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.03/1.21  cnf(c_0_34, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 1.03/1.21  fof(c_0_35, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)&r1_xboole_0(esk5_0,esk3_0))&r1_xboole_0(esk6_0,esk4_0))&esk5_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 1.03/1.21  cnf(c_0_36, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.03/1.21  cnf(c_0_37, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_29, c_0_19])).
% 1.03/1.21  cnf(c_0_38, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.03/1.21  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_31, c_0_19])).
% 1.03/1.21  cnf(c_0_40, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 1.03/1.21  fof(c_0_41, plain, ![X31, X32, X33]:k2_xboole_0(k2_xboole_0(X31,X32),X33)=k2_xboole_0(X31,k2_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 1.03/1.21  cnf(c_0_42, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.03/1.21  fof(c_0_43, plain, ![X19, X20]:k2_xboole_0(X19,k4_xboole_0(X20,X19))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.03/1.21  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_19])).
% 1.03/1.21  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_26])).
% 1.03/1.21  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_37])).
% 1.03/1.21  cnf(c_0_47, plain, (r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)|r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_26])).
% 1.03/1.21  cnf(c_0_48, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.03/1.21  cnf(c_0_49, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_42, c_0_24])).
% 1.03/1.21  cnf(c_0_50, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.03/1.21  cnf(c_0_51, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_37, c_0_44])).
% 1.03/1.21  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_39])).
% 1.03/1.21  cnf(c_0_53, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.03/1.21  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.03/1.21  cnf(c_0_55, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))=k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_48])).
% 1.03/1.21  cnf(c_0_56, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_34]), c_0_23])).
% 1.03/1.21  fof(c_0_57, plain, ![X24, X25, X26]:k4_xboole_0(k4_xboole_0(X24,X25),X26)=k4_xboole_0(X24,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.03/1.21  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_51, c_0_39])).
% 1.03/1.21  cnf(c_0_59, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(X2),X2)), inference(spm,[status(thm)],[c_0_26, c_0_38])).
% 1.03/1.21  cnf(c_0_60, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_26]), c_0_34]), c_0_34])).
% 1.03/1.21  cnf(c_0_61, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.03/1.21  cnf(c_0_62, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_49]), c_0_24])).
% 1.03/1.21  cnf(c_0_63, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.03/1.21  cnf(c_0_64, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0)=k4_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_49])).
% 1.03/1.21  cnf(c_0_65, plain, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X2,X1)|~r1_xboole_0(X2,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_34])).
% 1.03/1.21  cnf(c_0_66, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 1.03/1.21  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_38])).
% 1.03/1.21  cnf(c_0_68, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3)=k4_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_32, c_0_48])).
% 1.03/1.21  cnf(c_0_69, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_62])).
% 1.03/1.21  cnf(c_0_70, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_63])).
% 1.03/1.21  cnf(c_0_71, plain, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 1.03/1.21  cnf(c_0_72, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_67])).
% 1.03/1.21  cnf(c_0_73, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_50, c_0_63])).
% 1.03/1.21  cnf(c_0_74, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_24])).
% 1.03/1.21  cnf(c_0_75, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(esk5_0,esk6_0)),esk3_0)=k4_xboole_0(k2_xboole_0(X1,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_49])).
% 1.03/1.21  cnf(c_0_76, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_32]), c_0_50])).
% 1.03/1.21  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 1.03/1.21  cnf(c_0_78, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_37, c_0_71])).
% 1.03/1.21  cnf(c_0_79, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.03/1.21  cnf(c_0_80, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))|~r1_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_51, c_0_63])).
% 1.03/1.21  cnf(c_0_81, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_72, c_0_54])).
% 1.03/1.21  cnf(c_0_82, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_34]), c_0_23]), c_0_74])).
% 1.03/1.21  cnf(c_0_83, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk3_0)=k4_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_24]), c_0_64]), c_0_24])).
% 1.03/1.21  cnf(c_0_84, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk4_0,esk3_0))=k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_77]), c_0_73])).
% 1.03/1.21  cnf(c_0_85, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_51, c_0_32])).
% 1.03/1.21  cnf(c_0_86, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 1.03/1.21  cnf(c_0_87, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk6_0,esk4_0),X2)))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 1.03/1.21  cnf(c_0_88, plain, (r2_hidden(esk1_2(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))|r1_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_39, c_0_44])).
% 1.03/1.21  cnf(c_0_89, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk3_0)))=k2_xboole_0(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_48]), c_0_84])).
% 1.03/1.21  cnf(c_0_90, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_26])).
% 1.03/1.21  cnf(c_0_91, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_24, c_0_48])).
% 1.03/1.21  cnf(c_0_92, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_76]), c_0_49]), c_0_24])).
% 1.03/1.21  cnf(c_0_93, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 1.03/1.21  cnf(c_0_94, negated_conjecture, (r1_xboole_0(esk6_0,k4_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk6_0,esk4_0),X1)))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 1.03/1.21  cnf(c_0_95, negated_conjecture, (k2_xboole_0(esk4_0,esk6_0)=k2_xboole_0(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_24]), c_0_91]), c_0_24]), c_0_92]), c_0_93])).
% 1.03/1.21  cnf(c_0_96, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_74, c_0_49])).
% 1.03/1.21  cnf(c_0_97, negated_conjecture, (r1_xboole_0(esk6_0,k4_xboole_0(esk6_0,k2_xboole_0(X1,k4_xboole_0(esk6_0,esk4_0))))), inference(spm,[status(thm)],[c_0_94, c_0_24])).
% 1.03/1.21  cnf(c_0_98, negated_conjecture, (k4_xboole_0(esk6_0,esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_95]), c_0_96])).
% 1.03/1.21  cnf(c_0_99, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_63]), c_0_50])).
% 1.03/1.21  cnf(c_0_100, negated_conjecture, (r1_xboole_0(esk6_0,k4_xboole_0(esk6_0,k2_xboole_0(X1,k4_xboole_0(esk3_0,esk4_0))))), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 1.03/1.21  fof(c_0_101, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 1.03/1.21  cnf(c_0_102, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_99]), c_0_26])).
% 1.03/1.21  cnf(c_0_103, negated_conjecture, (r1_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk3_0))), inference(spm,[status(thm)],[c_0_100, c_0_82])).
% 1.03/1.21  cnf(c_0_104, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 1.03/1.21  cnf(c_0_105, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_38]), c_0_23])).
% 1.03/1.21  cnf(c_0_106, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X2)))), inference(spm,[status(thm)],[c_0_102, c_0_48])).
% 1.03/1.21  cnf(c_0_107, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk6_0,esk3_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_103]), c_0_44])).
% 1.03/1.21  cnf(c_0_108, negated_conjecture, (r1_xboole_0(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_104, c_0_54])).
% 1.03/1.21  cnf(c_0_109, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)=k2_xboole_0(esk5_0,esk3_0)|r2_hidden(esk2_1(k4_xboole_0(esk6_0,esk3_0)),k4_xboole_0(esk6_0,esk3_0))), inference(spm,[status(thm)],[c_0_62, c_0_105])).
% 1.03/1.21  cnf(c_0_110, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk6_0,esk3_0))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 1.03/1.21  cnf(c_0_111, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)),X1)), inference(spm,[status(thm)],[c_0_72, c_0_108])).
% 1.03/1.21  cnf(c_0_112, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)=k2_xboole_0(esk5_0,esk3_0)), inference(sr,[status(thm)],[c_0_109, c_0_110])).
% 1.03/1.21  cnf(c_0_113, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X2)))), inference(spm,[status(thm)],[c_0_80, c_0_111])).
% 1.03/1.21  cnf(c_0_114, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=k4_xboole_0(esk5_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_112]), c_0_32])).
% 1.03/1.21  cnf(c_0_115, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(X2,k4_xboole_0(esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_113, c_0_24])).
% 1.03/1.21  cnf(c_0_116, negated_conjecture, (k4_xboole_0(esk4_0,esk6_0)=k4_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_95]), c_0_32])).
% 1.03/1.21  cnf(c_0_117, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk3_0))=esk4_0), inference(spm,[status(thm)],[c_0_82, c_0_114])).
% 1.03/1.21  cnf(c_0_118, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(X2,k4_xboole_0(esk5_0,esk6_0))))), inference(rw,[status(thm)],[c_0_115, c_0_116])).
% 1.03/1.21  cnf(c_0_119, negated_conjecture, (k2_xboole_0(esk5_0,esk4_0)=esk4_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_90]), c_0_24]), c_0_93])).
% 1.03/1.21  cnf(c_0_120, negated_conjecture, (esk5_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.03/1.21  cnf(c_0_121, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_118, c_0_82])).
% 1.03/1.21  cnf(c_0_122, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_119]), c_0_120]), c_0_121]), ['proof']).
% 1.03/1.21  # SZS output end CNFRefutation
% 1.03/1.21  # Proof object total steps             : 123
% 1.03/1.21  # Proof object clause steps            : 94
% 1.03/1.21  # Proof object formula steps           : 29
% 1.03/1.21  # Proof object conjectures             : 48
% 1.03/1.21  # Proof object clause conjectures      : 45
% 1.03/1.21  # Proof object formula conjectures     : 3
% 1.03/1.21  # Proof object initial clauses used    : 18
% 1.03/1.21  # Proof object initial formulas used   : 14
% 1.03/1.21  # Proof object generating inferences   : 63
% 1.03/1.21  # Proof object simplifying inferences  : 55
% 1.03/1.21  # Training examples: 0 positive, 0 negative
% 1.03/1.21  # Parsed axioms                        : 14
% 1.03/1.21  # Removed by relevancy pruning/SinE    : 0
% 1.03/1.21  # Initial clauses                      : 18
% 1.03/1.21  # Removed in clause preprocessing      : 1
% 1.03/1.21  # Initial clauses in saturation        : 17
% 1.03/1.21  # Processed clauses                    : 8505
% 1.03/1.21  # ...of these trivial                  : 680
% 1.03/1.21  # ...subsumed                          : 6763
% 1.03/1.21  # ...remaining for further processing  : 1062
% 1.03/1.21  # Other redundant clauses eliminated   : 7
% 1.03/1.21  # Clauses deleted for lack of memory   : 0
% 1.03/1.21  # Backward-subsumed                    : 46
% 1.03/1.21  # Backward-rewritten                   : 499
% 1.03/1.21  # Generated clauses                    : 132546
% 1.03/1.21  # ...of the previous two non-trivial   : 85095
% 1.03/1.21  # Contextual simplify-reflections      : 6
% 1.03/1.21  # Paramodulations                      : 132526
% 1.03/1.21  # Factorizations                       : 10
% 1.03/1.21  # Equation resolutions                 : 7
% 1.03/1.21  # Propositional unsat checks           : 0
% 1.03/1.21  #    Propositional check models        : 0
% 1.03/1.21  #    Propositional check unsatisfiable : 0
% 1.03/1.21  #    Propositional clauses             : 0
% 1.03/1.21  #    Propositional clauses after purity: 0
% 1.03/1.21  #    Propositional unsat core size     : 0
% 1.03/1.21  #    Propositional preprocessing time  : 0.000
% 1.03/1.21  #    Propositional encoding time       : 0.000
% 1.03/1.21  #    Propositional solver time         : 0.000
% 1.03/1.21  #    Success case prop preproc time    : 0.000
% 1.03/1.21  #    Success case prop encoding time   : 0.000
% 1.03/1.21  #    Success case prop solver time     : 0.000
% 1.03/1.21  # Current number of processed clauses  : 497
% 1.03/1.21  #    Positive orientable unit clauses  : 195
% 1.03/1.21  #    Positive unorientable unit clauses: 3
% 1.03/1.21  #    Negative unit clauses             : 50
% 1.03/1.21  #    Non-unit-clauses                  : 249
% 1.03/1.21  # Current number of unprocessed clauses: 74058
% 1.03/1.21  # ...number of literals in the above   : 220740
% 1.03/1.21  # Current number of archived formulas  : 0
% 1.03/1.21  # Current number of archived clauses   : 566
% 1.03/1.21  # Clause-clause subsumption calls (NU) : 87337
% 1.03/1.21  # Rec. Clause-clause subsumption calls : 58143
% 1.03/1.21  # Non-unit clause-clause subsumptions  : 3807
% 1.03/1.21  # Unit Clause-clause subsumption calls : 6139
% 1.03/1.21  # Rewrite failures with RHS unbound    : 0
% 1.03/1.21  # BW rewrite match attempts            : 942
% 1.03/1.21  # BW rewrite match successes           : 225
% 1.03/1.21  # Condensation attempts                : 0
% 1.03/1.21  # Condensation successes               : 0
% 1.03/1.21  # Termbank termtop insertions          : 2072347
% 1.03/1.21  
% 1.03/1.21  # -------------------------------------------------
% 1.03/1.21  # User time                : 0.836 s
% 1.03/1.21  # System time              : 0.034 s
% 1.03/1.21  # Total time               : 0.870 s
% 1.03/1.21  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
