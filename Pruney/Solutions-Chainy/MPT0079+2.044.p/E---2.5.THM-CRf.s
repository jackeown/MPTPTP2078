%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:06 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  165 (17821 expanded)
%              Number of clauses        :  134 (8044 expanded)
%              Number of leaves         :   15 (4722 expanded)
%              Depth                    :   33
%              Number of atoms          :  217 (25034 expanded)
%              Number of equality atoms :  101 (16351 expanded)
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

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(c_0_15,plain,(
    ! [X19] : k3_xboole_0(X19,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_16,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X18] : k2_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_18,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_22,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X23,X24] : k4_xboole_0(k2_xboole_0(X23,X24),X24) = k4_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X16] :
      ( X16 = k1_xboole_0
      | r2_hidden(esk2_1(X16),X16) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_34,plain,(
    ! [X25,X26,X27] : k4_xboole_0(k4_xboole_0(X25,X26),X27) = k4_xboole_0(X25,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_35,plain,(
    ! [X20,X21] : k2_xboole_0(X20,k4_xboole_0(X21,X20)) = k2_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_36,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_27])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_36])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_39])).

fof(c_0_46,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & r1_xboole_0(esk5_0,esk3_0)
    & r1_xboole_0(esk6_0,esk4_0)
    & esk5_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_41]),c_0_42])).

fof(c_0_48,plain,(
    ! [X30,X31,X32] : k2_xboole_0(k2_xboole_0(X30,X31),X32) = k2_xboole_0(X30,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_50,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_47]),c_0_27])).

cnf(c_0_53,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_33]),c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_57,plain,(
    ! [X33,X34] : k2_xboole_0(k3_xboole_0(X33,X34),k4_xboole_0(X33,X34)) = X33 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_41]),c_0_41])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_60,plain,
    ( X1 = X2
    | r2_hidden(esk2_1(X2),X2)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

fof(c_0_62,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_64,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),X2))
    | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_33]),c_0_24])).

cnf(c_0_66,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)))
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_25])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_42])).

cnf(c_0_72,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_64,c_0_20])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_25]),c_0_31]),c_0_31])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_25])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X3,X2)))
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_25]),c_0_42]),c_0_25])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_53])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_31]),c_0_42])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_66])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_76])).

fof(c_0_84,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_71]),c_0_41]),c_0_78]),c_0_79]),c_0_25]),c_0_42]),c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,k2_xboole_0(k4_xboole_0(esk3_0,esk5_0),X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_41])).

cnf(c_0_87,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_83]),c_0_42]),c_0_25]),c_0_76])).

cnf(c_0_88,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) = k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_76]),c_0_53])).

cnf(c_0_89,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(k4_xboole_0(esk3_0,esk5_0),X2))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_87]),c_0_33])).

cnf(c_0_93,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0))) = k2_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_87])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_53])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(X2,k4_xboole_0(esk3_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_25])).

cnf(c_0_96,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk5_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_24])).

cnf(c_0_97,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) = k2_xboole_0(esk5_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_79]),c_0_89]),c_0_79]),c_0_25])).

cnf(c_0_98,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk5_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_94]),c_0_76]),c_0_76]),c_0_79]),c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_101,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_102,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_66])).

cnf(c_0_103,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk4_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_76])).

cnf(c_0_105,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk6_0,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_102]),c_0_41])).

cnf(c_0_106,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk4_0)) = k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_103]),c_0_91]),c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,k2_xboole_0(X2,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_25])).

cnf(c_0_108,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_106]),c_0_101]),c_0_41]),c_0_41])).

cnf(c_0_109,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_25]),c_0_53])).

cnf(c_0_110,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(X1,esk3_0)) = k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_25])).

cnf(c_0_111,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_37]),c_0_24])).

cnf(c_0_112,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))
    | ~ r1_xboole_0(k2_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_100])).

cnf(c_0_113,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_51])).

cnf(c_0_115,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(X1,k2_xboole_0(esk4_0,esk6_0))) = k2_xboole_0(X1,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_100])).

cnf(c_0_116,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)) = k2_xboole_0(esk4_0,X1)
    | r2_hidden(esk2_1(k4_xboole_0(esk3_0,X1)),k4_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_117,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_89])).

cnf(c_0_118,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113])])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_37])).

cnf(c_0_120,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk6_0,esk4_0),X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_114]),c_0_41])).

cnf(c_0_121,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk6_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117]),c_0_79]),c_0_89]),c_0_108]),c_0_108]),c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk6_0,esk4_0),X2))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_121]),c_0_104])).

cnf(c_0_125,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_122,c_0_51])).

cnf(c_0_126,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,k2_xboole_0(X2,k4_xboole_0(esk6_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_123,c_0_25])).

cnf(c_0_127,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_51])).

cnf(c_0_128,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk4_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_124]),c_0_106])).

cnf(c_0_129,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_92]),c_0_53]),c_0_24]),c_0_53]),c_0_25])).

cnf(c_0_131,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,k2_xboole_0(X2,k4_xboole_0(esk3_0,esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_126,c_0_124])).

cnf(c_0_132,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_127])).

cnf(c_0_133,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk4_0)) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_106,c_0_128])).

cnf(c_0_134,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_111])).

cnf(c_0_135,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_129,c_0_124])).

cnf(c_0_136,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) = k2_xboole_0(esk5_0,esk3_0)
    | r2_hidden(esk2_1(k4_xboole_0(esk6_0,esk3_0)),k4_xboole_0(esk6_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_111])).

cnf(c_0_137,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_78])).

cnf(c_0_138,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_132]),c_0_41])).

cnf(c_0_139,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_135])).

cnf(c_0_140,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) = k2_xboole_0(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X2))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_138])).

cnf(c_0_142,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = k4_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_121]),c_0_31])).

cnf(c_0_143,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk6_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_139])).

cnf(c_0_144,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_78])).

cnf(c_0_145,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = k4_xboole_0(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_140]),c_0_31])).

cnf(c_0_146,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk5_0,esk6_0),X2))) ),
    inference(rw,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_147,negated_conjecture,
    ( esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_143]),c_0_99])).

cnf(c_0_148,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_83]),c_0_41])).

cnf(c_0_149,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_41])).

cnf(c_0_150,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_68])).

cnf(c_0_151,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X1)) = k2_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_152,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X2))) ),
    inference(rw,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_153,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_148,c_0_140]),c_0_149])).

cnf(c_0_154,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_150]),c_0_41])).

cnf(c_0_155,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X1) = k2_xboole_0(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_151]),c_0_152])).

cnf(c_0_156,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,X1))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_153])).

cnf(c_0_157,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X2))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_154])).

cnf(c_0_158,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk3_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_155]),c_0_41]),c_0_156])).

cnf(c_0_159,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(X2,k4_xboole_0(esk5_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_157,c_0_25])).

cnf(c_0_160,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk3_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_145])).

cnf(c_0_161,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk4_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_158])).

cnf(c_0_162,negated_conjecture,
    ( esk5_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_163,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_159,c_0_160])).

cnf(c_0_164,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_161]),c_0_162]),c_0_163]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.26  % Computer   : n014.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 16:25:52 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  # Version: 2.5pre002
% 0.06/0.26  # No SInE strategy applied
% 0.06/0.26  # Trying AutoSched0 for 299 seconds
% 1.44/1.66  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 1.44/1.66  # and selection function SelectLargestOrientable.
% 1.44/1.66  #
% 1.44/1.66  # Preprocessing time       : 0.012 s
% 1.44/1.66  # Presaturation interreduction done
% 1.44/1.66  
% 1.44/1.66  # Proof found!
% 1.44/1.66  # SZS status Theorem
% 1.44/1.66  # SZS output start CNFRefutation
% 1.44/1.66  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.44/1.66  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.44/1.66  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.44/1.66  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.44/1.66  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.44/1.66  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.44/1.66  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.44/1.66  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.44/1.66  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.44/1.66  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.44/1.66  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 1.44/1.66  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.44/1.66  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.44/1.66  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.44/1.66  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.44/1.66  fof(c_0_15, plain, ![X19]:k3_xboole_0(X19,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 1.44/1.66  fof(c_0_16, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.44/1.66  fof(c_0_17, plain, ![X18]:k2_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t1_boole])).
% 1.44/1.66  fof(c_0_18, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.44/1.66  cnf(c_0_19, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.44/1.66  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.44/1.66  fof(c_0_21, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.44/1.66  fof(c_0_22, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.44/1.66  fof(c_0_23, plain, ![X23, X24]:k4_xboole_0(k2_xboole_0(X23,X24),X24)=k4_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 1.44/1.66  cnf(c_0_24, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.44/1.66  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.44/1.66  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 1.44/1.66  cnf(c_0_27, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.44/1.66  cnf(c_0_28, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.44/1.66  fof(c_0_29, plain, ![X16]:(X16=k1_xboole_0|r2_hidden(esk2_1(X16),X16)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 1.44/1.66  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.44/1.66  cnf(c_0_31, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.44/1.66  cnf(c_0_32, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.44/1.66  cnf(c_0_33, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 1.44/1.66  fof(c_0_34, plain, ![X25, X26, X27]:k4_xboole_0(k4_xboole_0(X25,X26),X27)=k4_xboole_0(X25,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.44/1.66  fof(c_0_35, plain, ![X20, X21]:k2_xboole_0(X20,k4_xboole_0(X21,X20))=k2_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.44/1.66  cnf(c_0_36, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_28, c_0_20])).
% 1.44/1.66  cnf(c_0_37, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.44/1.66  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_30, c_0_20])).
% 1.44/1.66  cnf(c_0_39, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 1.44/1.66  fof(c_0_40, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 1.44/1.66  cnf(c_0_41, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.44/1.66  cnf(c_0_42, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.44/1.66  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_33]), c_0_27])).
% 1.44/1.66  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_36])).
% 1.44/1.66  cnf(c_0_45, plain, (r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)|r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_39])).
% 1.44/1.66  fof(c_0_46, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)&r1_xboole_0(esk5_0,esk3_0))&r1_xboole_0(esk6_0,esk4_0))&esk5_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).
% 1.44/1.66  cnf(c_0_47, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_41]), c_0_42])).
% 1.44/1.66  fof(c_0_48, plain, ![X30, X31, X32]:k2_xboole_0(k2_xboole_0(X30,X31),X32)=k2_xboole_0(X30,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 1.44/1.66  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 1.44/1.66  cnf(c_0_50, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.44/1.66  cnf(c_0_51, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.44/1.66  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_47]), c_0_27])).
% 1.44/1.66  cnf(c_0_53, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.44/1.66  cnf(c_0_54, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_33]), c_0_33])).
% 1.44/1.66  cnf(c_0_55, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.44/1.66  cnf(c_0_56, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.44/1.66  fof(c_0_57, plain, ![X33, X34]:k2_xboole_0(k3_xboole_0(X33,X34),k4_xboole_0(X33,X34))=X33, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 1.44/1.66  cnf(c_0_58, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))))|~r1_xboole_0(k4_xboole_0(X2,X3),X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_41]), c_0_41])).
% 1.44/1.66  cnf(c_0_59, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 1.44/1.66  cnf(c_0_60, plain, (X1=X2|r2_hidden(esk2_1(X2),X2)|r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_37, c_0_37])).
% 1.44/1.66  cnf(c_0_61, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_55])).
% 1.44/1.66  fof(c_0_62, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 1.44/1.66  cnf(c_0_63, plain, (~r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)))|~r1_xboole_0(k2_xboole_0(X2,X3),X3)), inference(spm,[status(thm)],[c_0_36, c_0_31])).
% 1.44/1.66  cnf(c_0_64, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.44/1.66  cnf(c_0_65, plain, (~r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),X2))|~r1_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_33]), c_0_24])).
% 1.44/1.66  cnf(c_0_66, plain, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 1.44/1.66  cnf(c_0_67, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.44/1.66  cnf(c_0_68, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.44/1.66  cnf(c_0_69, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.44/1.66  cnf(c_0_70, plain, (~r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)))|~r1_xboole_0(k2_xboole_0(X2,X3),X2)), inference(spm,[status(thm)],[c_0_63, c_0_25])).
% 1.44/1.66  cnf(c_0_71, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_31, c_0_42])).
% 1.44/1.66  cnf(c_0_72, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_64, c_0_20])).
% 1.44/1.66  cnf(c_0_73, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k4_xboole_0(X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_25]), c_0_31]), c_0_31])).
% 1.44/1.66  cnf(c_0_74, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_36, c_0_66])).
% 1.44/1.66  cnf(c_0_75, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.44/1.66  cnf(c_0_76, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_69, c_0_25])).
% 1.44/1.66  cnf(c_0_77, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X3,X2)))|~r1_xboole_0(k2_xboole_0(X2,X3),X2)), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 1.44/1.66  cnf(c_0_78, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_25]), c_0_42]), c_0_25])).
% 1.44/1.66  cnf(c_0_79, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_53])).
% 1.44/1.66  cnf(c_0_80, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_31]), c_0_42])).
% 1.44/1.66  cnf(c_0_81, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k4_xboole_0(X2,X3),X2)), inference(spm,[status(thm)],[c_0_73, c_0_66])).
% 1.44/1.66  cnf(c_0_82, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 1.44/1.66  cnf(c_0_83, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0)=k4_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_76])).
% 1.44/1.66  fof(c_0_84, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 1.44/1.66  cnf(c_0_85, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_71]), c_0_41]), c_0_78]), c_0_79]), c_0_25]), c_0_42]), c_0_80])).
% 1.44/1.66  cnf(c_0_86, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,k2_xboole_0(k4_xboole_0(esk3_0,esk5_0),X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_41])).
% 1.44/1.66  cnf(c_0_87, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_83]), c_0_42]), c_0_25]), c_0_76])).
% 1.44/1.66  cnf(c_0_88, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))=k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_76]), c_0_53])).
% 1.44/1.66  cnf(c_0_89, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_84])).
% 1.44/1.66  cnf(c_0_90, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(k4_xboole_0(esk3_0,esk5_0),X2)))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 1.44/1.66  cnf(c_0_91, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 1.44/1.66  cnf(c_0_92, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_87]), c_0_33])).
% 1.44/1.66  cnf(c_0_93, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0)))=k2_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_88, c_0_87])).
% 1.44/1.66  cnf(c_0_94, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_89, c_0_53])).
% 1.44/1.66  cnf(c_0_95, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(X2,k4_xboole_0(esk3_0,esk5_0))))), inference(spm,[status(thm)],[c_0_90, c_0_25])).
% 1.44/1.66  cnf(c_0_96, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk5_0))=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_24])).
% 1.44/1.66  cnf(c_0_97, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))=k2_xboole_0(esk5_0,k2_xboole_0(esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_79]), c_0_89]), c_0_79]), c_0_25])).
% 1.44/1.66  cnf(c_0_98, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk5_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_94]), c_0_76]), c_0_76]), c_0_79]), c_0_89])).
% 1.44/1.66  cnf(c_0_99, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 1.44/1.66  cnf(c_0_100, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 1.44/1.66  cnf(c_0_101, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_25])).
% 1.44/1.66  cnf(c_0_102, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_99, c_0_66])).
% 1.44/1.66  cnf(c_0_103, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk4_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_31, c_0_100])).
% 1.44/1.66  cnf(c_0_104, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_101, c_0_76])).
% 1.44/1.66  cnf(c_0_105, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk6_0,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_102]), c_0_41])).
% 1.44/1.66  cnf(c_0_106, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk4_0))=k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_103]), c_0_91]), c_0_104])).
% 1.44/1.66  cnf(c_0_107, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,k2_xboole_0(X2,esk6_0)))), inference(spm,[status(thm)],[c_0_105, c_0_25])).
% 1.44/1.66  cnf(c_0_108, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_106]), c_0_101]), c_0_41]), c_0_41])).
% 1.44/1.66  cnf(c_0_109, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_25]), c_0_53])).
% 1.44/1.66  cnf(c_0_110, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(X1,esk3_0))=k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))), inference(spm,[status(thm)],[c_0_88, c_0_25])).
% 1.44/1.66  cnf(c_0_111, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_37]), c_0_24])).
% 1.44/1.66  cnf(c_0_112, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))|~r1_xboole_0(k2_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_85, c_0_100])).
% 1.44/1.66  cnf(c_0_113, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 1.44/1.66  cnf(c_0_114, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0)))), inference(spm,[status(thm)],[c_0_74, c_0_51])).
% 1.44/1.66  cnf(c_0_115, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(X1,k2_xboole_0(esk4_0,esk6_0)))=k2_xboole_0(X1,k2_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_109, c_0_100])).
% 1.44/1.66  cnf(c_0_116, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))=k2_xboole_0(esk4_0,X1)|r2_hidden(esk2_1(k4_xboole_0(esk3_0,X1)),k4_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 1.44/1.66  cnf(c_0_117, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_89])).
% 1.44/1.66  cnf(c_0_118, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113])])).
% 1.44/1.66  cnf(c_0_119, negated_conjecture, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_37])).
% 1.44/1.66  cnf(c_0_120, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk6_0,esk4_0),X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_114]), c_0_41])).
% 1.44/1.66  cnf(c_0_121, negated_conjecture, (k2_xboole_0(esk4_0,esk6_0)=k2_xboole_0(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117]), c_0_79]), c_0_89]), c_0_108]), c_0_108]), c_0_118])).
% 1.44/1.66  cnf(c_0_122, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_119])).
% 1.44/1.66  cnf(c_0_123, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk6_0,esk4_0),X2)))), inference(spm,[status(thm)],[c_0_85, c_0_120])).
% 1.44/1.66  cnf(c_0_124, negated_conjecture, (k4_xboole_0(esk6_0,esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_121]), c_0_104])).
% 1.44/1.66  cnf(c_0_125, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_122, c_0_51])).
% 1.44/1.66  cnf(c_0_126, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk6_0,k2_xboole_0(X2,k4_xboole_0(esk6_0,esk4_0))))), inference(spm,[status(thm)],[c_0_123, c_0_25])).
% 1.44/1.66  cnf(c_0_127, negated_conjecture, (r1_xboole_0(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_67, c_0_51])).
% 1.44/1.66  cnf(c_0_128, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk4_0))=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_124]), c_0_106])).
% 1.44/1.66  cnf(c_0_129, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0)))), inference(spm,[status(thm)],[c_0_56, c_0_125])).
% 1.44/1.66  cnf(c_0_130, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_92]), c_0_53]), c_0_24]), c_0_53]), c_0_25])).
% 1.44/1.66  cnf(c_0_131, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk6_0,k2_xboole_0(X2,k4_xboole_0(esk3_0,esk4_0))))), inference(rw,[status(thm)],[c_0_126, c_0_124])).
% 1.44/1.66  cnf(c_0_132, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_74, c_0_127])).
% 1.44/1.66  cnf(c_0_133, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk4_0))=esk6_0), inference(rw,[status(thm)],[c_0_106, c_0_128])).
% 1.44/1.66  cnf(c_0_134, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_111])).
% 1.44/1.66  cnf(c_0_135, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_129, c_0_124])).
% 1.44/1.66  cnf(c_0_136, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)=k2_xboole_0(esk5_0,esk3_0)|r2_hidden(esk2_1(k4_xboole_0(esk6_0,esk3_0)),k4_xboole_0(esk6_0,esk3_0))), inference(spm,[status(thm)],[c_0_130, c_0_111])).
% 1.44/1.66  cnf(c_0_137, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk6_0,esk3_0))), inference(spm,[status(thm)],[c_0_131, c_0_78])).
% 1.44/1.66  cnf(c_0_138, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_132]), c_0_41])).
% 1.44/1.66  cnf(c_0_139, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_135])).
% 1.44/1.66  cnf(c_0_140, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)=k2_xboole_0(esk5_0,esk3_0)), inference(sr,[status(thm)],[c_0_136, c_0_137])).
% 1.44/1.66  cnf(c_0_141, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X2)))), inference(spm,[status(thm)],[c_0_85, c_0_138])).
% 1.44/1.66  cnf(c_0_142, negated_conjecture, (k4_xboole_0(esk4_0,esk6_0)=k4_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_121]), c_0_31])).
% 1.44/1.66  cnf(c_0_143, negated_conjecture, (k2_xboole_0(esk3_0,esk6_0)=esk3_0), inference(spm,[status(thm)],[c_0_78, c_0_139])).
% 1.44/1.66  cnf(c_0_144, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k2_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_53, c_0_78])).
% 1.44/1.66  cnf(c_0_145, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=k4_xboole_0(esk5_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_140]), c_0_31])).
% 1.44/1.66  cnf(c_0_146, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk5_0,esk6_0),X2)))), inference(rw,[status(thm)],[c_0_141, c_0_142])).
% 1.44/1.66  cnf(c_0_147, negated_conjecture, (esk6_0=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_143]), c_0_99])).
% 1.44/1.66  cnf(c_0_148, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_83]), c_0_41])).
% 1.44/1.66  cnf(c_0_149, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_31]), c_0_41])).
% 1.44/1.66  cnf(c_0_150, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_74, c_0_68])).
% 1.44/1.66  cnf(c_0_151, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X1))=k2_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 1.44/1.66  cnf(c_0_152, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X2)))), inference(rw,[status(thm)],[c_0_146, c_0_147])).
% 1.44/1.66  cnf(c_0_153, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_148, c_0_140]), c_0_149])).
% 1.44/1.66  cnf(c_0_154, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk5_0,k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_150]), c_0_41])).
% 1.44/1.66  cnf(c_0_155, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X1)=k2_xboole_0(esk4_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_151]), c_0_152])).
% 1.44/1.66  cnf(c_0_156, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,X1)))=esk4_0), inference(spm,[status(thm)],[c_0_78, c_0_153])).
% 1.44/1.66  cnf(c_0_157, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X2)))), inference(spm,[status(thm)],[c_0_85, c_0_154])).
% 1.44/1.66  cnf(c_0_158, negated_conjecture, (k4_xboole_0(esk5_0,esk3_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_155]), c_0_41]), c_0_156])).
% 1.44/1.66  cnf(c_0_159, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(X2,k4_xboole_0(esk5_0,esk3_0))))), inference(spm,[status(thm)],[c_0_157, c_0_25])).
% 1.44/1.66  cnf(c_0_160, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk3_0))=esk4_0), inference(spm,[status(thm)],[c_0_78, c_0_145])).
% 1.44/1.66  cnf(c_0_161, negated_conjecture, (k2_xboole_0(esk5_0,esk4_0)=esk5_0), inference(spm,[status(thm)],[c_0_78, c_0_158])).
% 1.44/1.66  cnf(c_0_162, negated_conjecture, (esk5_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.44/1.66  cnf(c_0_163, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_159, c_0_160])).
% 1.44/1.66  cnf(c_0_164, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_161]), c_0_162]), c_0_163]), ['proof']).
% 1.44/1.66  # SZS output end CNFRefutation
% 1.44/1.66  # Proof object total steps             : 165
% 1.44/1.66  # Proof object clause steps            : 134
% 1.44/1.66  # Proof object formula steps           : 31
% 1.44/1.66  # Proof object conjectures             : 81
% 1.44/1.66  # Proof object clause conjectures      : 78
% 1.44/1.66  # Proof object formula conjectures     : 3
% 1.44/1.66  # Proof object initial clauses used    : 19
% 1.44/1.66  # Proof object initial formulas used   : 15
% 1.44/1.66  # Proof object generating inferences   : 95
% 1.44/1.66  # Proof object simplifying inferences  : 93
% 1.44/1.66  # Training examples: 0 positive, 0 negative
% 1.44/1.66  # Parsed axioms                        : 15
% 1.44/1.66  # Removed by relevancy pruning/SinE    : 0
% 1.44/1.66  # Initial clauses                      : 19
% 1.44/1.66  # Removed in clause preprocessing      : 1
% 1.44/1.66  # Initial clauses in saturation        : 18
% 1.44/1.66  # Processed clauses                    : 11830
% 1.44/1.66  # ...of these trivial                  : 899
% 1.44/1.66  # ...subsumed                          : 9705
% 1.44/1.66  # ...remaining for further processing  : 1226
% 1.44/1.66  # Other redundant clauses eliminated   : 14
% 1.44/1.66  # Clauses deleted for lack of memory   : 0
% 1.44/1.66  # Backward-subsumed                    : 50
% 1.44/1.66  # Backward-rewritten                   : 731
% 1.44/1.66  # Generated clauses                    : 229320
% 1.44/1.66  # ...of the previous two non-trivial   : 173174
% 1.44/1.66  # Contextual simplify-reflections      : 3
% 1.44/1.66  # Paramodulations                      : 229294
% 1.44/1.66  # Factorizations                       : 10
% 1.44/1.66  # Equation resolutions                 : 14
% 1.44/1.66  # Propositional unsat checks           : 0
% 1.44/1.66  #    Propositional check models        : 0
% 1.44/1.66  #    Propositional check unsatisfiable : 0
% 1.44/1.66  #    Propositional clauses             : 0
% 1.44/1.66  #    Propositional clauses after purity: 0
% 1.44/1.66  #    Propositional unsat core size     : 0
% 1.44/1.66  #    Propositional preprocessing time  : 0.000
% 1.44/1.66  #    Propositional encoding time       : 0.000
% 1.44/1.66  #    Propositional solver time         : 0.000
% 1.44/1.66  #    Success case prop preproc time    : 0.000
% 1.44/1.66  #    Success case prop encoding time   : 0.000
% 1.44/1.66  #    Success case prop solver time     : 0.000
% 1.44/1.66  # Current number of processed clauses  : 425
% 1.44/1.66  #    Positive orientable unit clauses  : 138
% 1.44/1.66  #    Positive unorientable unit clauses: 5
% 1.44/1.66  #    Negative unit clauses             : 29
% 1.44/1.66  #    Non-unit-clauses                  : 253
% 1.44/1.66  # Current number of unprocessed clauses: 156568
% 1.44/1.66  # ...number of literals in the above   : 457463
% 1.44/1.66  # Current number of archived formulas  : 0
% 1.44/1.66  # Current number of archived clauses   : 802
% 1.44/1.66  # Clause-clause subsumption calls (NU) : 101004
% 1.44/1.66  # Rec. Clause-clause subsumption calls : 63219
% 1.44/1.66  # Non-unit clause-clause subsumptions  : 4685
% 1.44/1.66  # Unit Clause-clause subsumption calls : 5627
% 1.44/1.66  # Rewrite failures with RHS unbound    : 0
% 1.44/1.66  # BW rewrite match attempts            : 1413
% 1.44/1.66  # BW rewrite match successes           : 474
% 1.44/1.66  # Condensation attempts                : 0
% 1.44/1.66  # Condensation successes               : 0
% 1.44/1.66  # Termbank termtop insertions          : 3740542
% 1.44/1.67  
% 1.44/1.67  # -------------------------------------------------
% 1.44/1.67  # User time                : 1.341 s
% 1.44/1.67  # System time              : 0.067 s
% 1.44/1.67  # Total time               : 1.408 s
% 1.44/1.67  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
