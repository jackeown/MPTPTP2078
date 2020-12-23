%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:03 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  118 (6631 expanded)
%              Number of clauses        :   87 (2906 expanded)
%              Number of leaves         :   15 (1820 expanded)
%              Depth                    :   20
%              Number of atoms          :  161 (7727 expanded)
%              Number of equality atoms :   86 (6690 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_16,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & r1_xboole_0(esk5_0,esk3_0)
    & r1_xboole_0(esk6_0,esk4_0)
    & esk5_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_18,plain,(
    ! [X19] : k3_xboole_0(X19,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_19,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X23,X24] : k4_xboole_0(k2_xboole_0(X23,X24),X24) = k4_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X18] : k2_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_27,plain,(
    ! [X20,X21] : k2_xboole_0(X20,k4_xboole_0(X21,X20)) = k2_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_30,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_36,plain,(
    ! [X25,X26,X27] : k4_xboole_0(k4_xboole_0(X25,X26),X27) = k4_xboole_0(X25,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X16] :
      ( X16 = k1_xboole_0
      | r2_hidden(esk2_1(X16),X16) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_42,plain,(
    ! [X32,X33,X34] : k2_xboole_0(k2_xboole_0(X32,X33),X34) = k2_xboole_0(X32,k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_34]),c_0_22]),c_0_29])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_40]),c_0_41])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_43]),c_0_41])).

fof(c_0_51,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_44]),c_0_34])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_45])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_35]),c_0_44])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_50]),c_0_49]),c_0_31]),c_0_49]),c_0_22])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_52]),c_0_33])).

cnf(c_0_60,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_55]),c_0_56]),c_0_22]),c_0_57])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_25]),c_0_25])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

fof(c_0_66,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k3_xboole_0(X28,X29)) = k4_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_49])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk4_0,esk5_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_31])).

cnf(c_0_70,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_64]),c_0_22])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_41]),c_0_31]),c_0_65])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_46])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),X1)) = k2_xboole_0(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_69])).

cnf(c_0_76,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_64])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_25])).

cnf(c_0_79,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X2,X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_73]),c_0_41]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0))) = k2_xboole_0(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_22])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk4_0))) = k4_xboole_0(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_80]),c_0_28]),c_0_44]),c_0_22])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_44])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_61]),c_0_64])).

fof(c_0_86,plain,(
    ! [X9] : k2_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_87,negated_conjecture,
    ( k2_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk6_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_83]),c_0_64]),c_0_83]),c_0_34]),c_0_22])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X2))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_64])).

cnf(c_0_90,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_49])).

cnf(c_0_91,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X1)) = k2_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_87])).

cnf(c_0_93,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_46])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(X2,k4_xboole_0(esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_22])).

cnf(c_0_95,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_78])).

cnf(c_0_96,plain,
    ( r2_hidden(esk1_2(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))
    | r1_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_64]),c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(esk5_0,esk6_0)),esk3_0) = k4_xboole_0(k2_xboole_0(X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_29])).

cnf(c_0_98,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( k2_xboole_0(esk5_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_76]),c_0_64])).

cnf(c_0_100,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X2,k2_xboole_0(X3,X1))),k4_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_62])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_87])).

cnf(c_0_102,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_64])).

cnf(c_0_103,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_105,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),esk3_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_35])).

cnf(c_0_106,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk4_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_22]),c_0_87]),c_0_22]),c_0_87]),c_0_101])).

cnf(c_0_107,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_52]),c_0_33]),c_0_33])).

cnf(c_0_108,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_79])).

cnf(c_0_109,negated_conjecture,
    ( r1_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = k4_xboole_0(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_107,c_0_49])).

cnf(c_0_112,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk3_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_110]),c_0_64]),c_0_110]),c_0_34]),c_0_22])).

cnf(c_0_114,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_46]),c_0_33])).

cnf(c_0_115,negated_conjecture,
    ( esk5_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_116,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_22]),c_0_106]),c_0_115]),c_0_116]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:50:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 2.14/2.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 2.14/2.35  # and selection function SelectLargestOrientable.
% 2.14/2.35  #
% 2.14/2.35  # Preprocessing time       : 0.025 s
% 2.14/2.35  # Presaturation interreduction done
% 2.14/2.35  
% 2.14/2.35  # Proof found!
% 2.14/2.35  # SZS status Theorem
% 2.14/2.35  # SZS output start CNFRefutation
% 2.14/2.35  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 2.14/2.35  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.14/2.35  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.14/2.35  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.14/2.35  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.14/2.35  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.14/2.35  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.14/2.35  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.14/2.35  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.14/2.35  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.14/2.35  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.14/2.35  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.14/2.35  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.14/2.35  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.14/2.35  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.14/2.35  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 2.14/2.35  fof(c_0_16, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)&r1_xboole_0(esk5_0,esk3_0))&r1_xboole_0(esk6_0,esk4_0))&esk5_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 2.14/2.35  fof(c_0_17, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.14/2.35  fof(c_0_18, plain, ![X19]:k3_xboole_0(X19,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 2.14/2.35  fof(c_0_19, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.14/2.35  fof(c_0_20, plain, ![X23, X24]:k4_xboole_0(k2_xboole_0(X23,X24),X24)=k4_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 2.14/2.35  cnf(c_0_21, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.14/2.35  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.14/2.35  fof(c_0_23, plain, ![X18]:k2_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t1_boole])).
% 2.14/2.35  cnf(c_0_24, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.14/2.35  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.14/2.35  fof(c_0_26, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.14/2.35  fof(c_0_27, plain, ![X20, X21]:k2_xboole_0(X20,k4_xboole_0(X21,X20))=k2_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 2.14/2.35  cnf(c_0_28, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.14/2.35  cnf(c_0_29, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 2.14/2.35  fof(c_0_30, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 2.14/2.35  cnf(c_0_31, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.14/2.35  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 2.14/2.35  cnf(c_0_33, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.14/2.35  cnf(c_0_34, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.14/2.35  cnf(c_0_35, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0)=k4_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 2.14/2.35  fof(c_0_36, plain, ![X25, X26, X27]:k4_xboole_0(k4_xboole_0(X25,X26),X27)=k4_xboole_0(X25,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 2.14/2.35  cnf(c_0_37, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.14/2.35  fof(c_0_38, plain, ![X16]:(X16=k1_xboole_0|r2_hidden(esk2_1(X16),X16)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 2.14/2.35  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.14/2.35  cnf(c_0_40, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_31, c_0_22])).
% 2.14/2.35  cnf(c_0_41, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 2.14/2.35  fof(c_0_42, plain, ![X32, X33, X34]:k2_xboole_0(k2_xboole_0(X32,X33),X34)=k2_xboole_0(X32,k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 2.14/2.35  cnf(c_0_43, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_34]), c_0_22]), c_0_29])).
% 2.14/2.35  cnf(c_0_44, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.14/2.35  cnf(c_0_45, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_37, c_0_25])).
% 2.14/2.35  cnf(c_0_46, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.14/2.35  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_39, c_0_25])).
% 2.14/2.35  cnf(c_0_48, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_40]), c_0_41])).
% 2.14/2.35  cnf(c_0_49, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.14/2.35  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_43]), c_0_41])).
% 2.14/2.35  fof(c_0_51, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.14/2.35  cnf(c_0_52, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_44]), c_0_34])).
% 2.14/2.35  cnf(c_0_53, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_45])).
% 2.14/2.35  cnf(c_0_54, plain, (r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)|r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_48])).
% 2.14/2.35  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_35]), c_0_44])).
% 2.14/2.35  cnf(c_0_56, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_22, c_0_49])).
% 2.14/2.35  cnf(c_0_57, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_50]), c_0_49]), c_0_31]), c_0_49]), c_0_22])).
% 2.14/2.35  cnf(c_0_58, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 2.14/2.35  cnf(c_0_59, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_52]), c_0_33])).
% 2.14/2.35  cnf(c_0_60, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 2.14/2.35  cnf(c_0_61, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.14/2.35  cnf(c_0_62, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_34, c_0_44])).
% 2.14/2.35  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_55]), c_0_56]), c_0_22]), c_0_57])).
% 2.14/2.35  cnf(c_0_64, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_25]), c_0_25])).
% 2.14/2.35  cnf(c_0_65, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 2.14/2.35  fof(c_0_66, plain, ![X28, X29]:k4_xboole_0(X28,k3_xboole_0(X28,X29))=k4_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 2.14/2.35  cnf(c_0_67, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X2)))), inference(spm,[status(thm)],[c_0_59, c_0_49])).
% 2.14/2.35  cnf(c_0_68, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 2.14/2.35  cnf(c_0_69, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk4_0,esk5_0))=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_31])).
% 2.14/2.35  cnf(c_0_70, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_64]), c_0_22])).
% 2.14/2.35  cnf(c_0_71, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_41]), c_0_31]), c_0_65])).
% 2.14/2.35  cnf(c_0_72, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 2.14/2.35  cnf(c_0_73, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(X2),X2)), inference(spm,[status(thm)],[c_0_33, c_0_46])).
% 2.14/2.35  cnf(c_0_74, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 2.14/2.35  cnf(c_0_75, negated_conjecture, (k2_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),X1))=k2_xboole_0(esk6_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_69])).
% 2.14/2.35  cnf(c_0_76, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 2.14/2.35  cnf(c_0_77, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_45, c_0_64])).
% 2.14/2.35  cnf(c_0_78, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_25])).
% 2.14/2.35  cnf(c_0_79, plain, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X2,X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_73]), c_0_41]), c_0_74])).
% 2.14/2.35  cnf(c_0_80, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0)))=k2_xboole_0(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_22])).
% 2.14/2.35  cnf(c_0_81, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k4_xboole_0(X2,X3),X2)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 2.14/2.35  cnf(c_0_82, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_45, c_0_79])).
% 2.14/2.35  cnf(c_0_83, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk4_0)))=k4_xboole_0(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_80]), c_0_28]), c_0_44]), c_0_22])).
% 2.14/2.35  cnf(c_0_84, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))|~r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_81, c_0_44])).
% 2.14/2.35  cnf(c_0_85, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_61]), c_0_64])).
% 2.14/2.35  fof(c_0_86, plain, ![X9]:k2_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 2.14/2.35  cnf(c_0_87, negated_conjecture, (k2_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk6_0))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_83]), c_0_64]), c_0_83]), c_0_34]), c_0_22])).
% 2.14/2.35  cnf(c_0_88, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X2)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 2.14/2.35  cnf(c_0_89, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_78, c_0_64])).
% 2.14/2.35  cnf(c_0_90, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3)=k4_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_28, c_0_49])).
% 2.14/2.35  cnf(c_0_91, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_86])).
% 2.14/2.35  cnf(c_0_92, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X1))=k2_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_87])).
% 2.14/2.35  cnf(c_0_93, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(X2),X2)), inference(spm,[status(thm)],[c_0_31, c_0_46])).
% 2.14/2.35  cnf(c_0_94, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(X2,k4_xboole_0(esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_88, c_0_22])).
% 2.14/2.35  cnf(c_0_95, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_45, c_0_78])).
% 2.14/2.35  cnf(c_0_96, plain, (r2_hidden(esk1_2(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))|r1_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_64]), c_0_89])).
% 2.14/2.35  cnf(c_0_97, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(esk5_0,esk6_0)),esk3_0)=k4_xboole_0(k2_xboole_0(X1,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_90, c_0_29])).
% 2.14/2.35  cnf(c_0_98, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_91])).
% 2.14/2.35  cnf(c_0_99, negated_conjecture, (k2_xboole_0(esk5_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))=k2_xboole_0(esk5_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_76]), c_0_64])).
% 2.14/2.35  cnf(c_0_100, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X3))=X1|r2_hidden(esk2_1(k4_xboole_0(X2,k2_xboole_0(X3,X1))),k4_xboole_0(X2,k2_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_93, c_0_62])).
% 2.14/2.35  cnf(c_0_101, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_94, c_0_87])).
% 2.14/2.35  cnf(c_0_102, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_95, c_0_64])).
% 2.14/2.35  cnf(c_0_103, plain, (r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_96])).
% 2.14/2.35  cnf(c_0_104, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.14/2.35  cnf(c_0_105, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),esk3_0)=k4_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_35])).
% 2.14/2.35  cnf(c_0_106, negated_conjecture, (k2_xboole_0(esk5_0,esk4_0)=esk5_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_22]), c_0_87]), c_0_22]), c_0_87]), c_0_101])).
% 2.14/2.35  cnf(c_0_107, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_52]), c_0_33]), c_0_33])).
% 2.14/2.35  cnf(c_0_108, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_95, c_0_79])).
% 2.14/2.35  cnf(c_0_109, negated_conjecture, (r1_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 2.14/2.35  cnf(c_0_110, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=k4_xboole_0(esk5_0,esk3_0)), inference(rw,[status(thm)],[c_0_105, c_0_106])).
% 2.14/2.35  cnf(c_0_111, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,X2)),X2)), inference(spm,[status(thm)],[c_0_107, c_0_49])).
% 2.14/2.35  cnf(c_0_112, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 2.14/2.35  cnf(c_0_113, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk3_0))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_110]), c_0_64]), c_0_110]), c_0_34]), c_0_22])).
% 2.14/2.35  cnf(c_0_114, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_46]), c_0_33])).
% 2.14/2.35  cnf(c_0_115, negated_conjecture, (esk5_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.14/2.35  cnf(c_0_116, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 2.14/2.35  cnf(c_0_117, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_22]), c_0_106]), c_0_115]), c_0_116]), ['proof']).
% 2.14/2.35  # SZS output end CNFRefutation
% 2.14/2.35  # Proof object total steps             : 118
% 2.14/2.35  # Proof object clause steps            : 87
% 2.14/2.35  # Proof object formula steps           : 31
% 2.14/2.35  # Proof object conjectures             : 36
% 2.14/2.35  # Proof object clause conjectures      : 33
% 2.14/2.35  # Proof object formula conjectures     : 3
% 2.14/2.35  # Proof object initial clauses used    : 19
% 2.14/2.35  # Proof object initial formulas used   : 15
% 2.14/2.35  # Proof object generating inferences   : 59
% 2.14/2.35  # Proof object simplifying inferences  : 61
% 2.14/2.35  # Training examples: 0 positive, 0 negative
% 2.14/2.35  # Parsed axioms                        : 15
% 2.14/2.35  # Removed by relevancy pruning/SinE    : 0
% 2.14/2.35  # Initial clauses                      : 19
% 2.14/2.35  # Removed in clause preprocessing      : 1
% 2.14/2.35  # Initial clauses in saturation        : 18
% 2.14/2.35  # Processed clauses                    : 14318
% 2.14/2.35  # ...of these trivial                  : 909
% 2.14/2.35  # ...subsumed                          : 12053
% 2.14/2.35  # ...remaining for further processing  : 1356
% 2.14/2.35  # Other redundant clauses eliminated   : 18
% 2.14/2.35  # Clauses deleted for lack of memory   : 0
% 2.14/2.35  # Backward-subsumed                    : 83
% 2.14/2.35  # Backward-rewritten                   : 668
% 2.14/2.35  # Generated clauses                    : 309118
% 2.14/2.35  # ...of the previous two non-trivial   : 250344
% 2.14/2.35  # Contextual simplify-reflections      : 7
% 2.14/2.35  # Paramodulations                      : 309093
% 2.14/2.35  # Factorizations                       : 6
% 2.14/2.35  # Equation resolutions                 : 18
% 2.14/2.35  # Propositional unsat checks           : 0
% 2.14/2.35  #    Propositional check models        : 0
% 2.14/2.35  #    Propositional check unsatisfiable : 0
% 2.14/2.35  #    Propositional clauses             : 0
% 2.14/2.35  #    Propositional clauses after purity: 0
% 2.14/2.35  #    Propositional unsat core size     : 0
% 2.14/2.35  #    Propositional preprocessing time  : 0.000
% 2.14/2.35  #    Propositional encoding time       : 0.000
% 2.14/2.35  #    Propositional solver time         : 0.000
% 2.14/2.35  #    Success case prop preproc time    : 0.000
% 2.14/2.35  #    Success case prop encoding time   : 0.000
% 2.14/2.35  #    Success case prop solver time     : 0.000
% 2.14/2.35  # Current number of processed clauses  : 586
% 2.14/2.35  #    Positive orientable unit clauses  : 158
% 2.14/2.35  #    Positive unorientable unit clauses: 9
% 2.14/2.35  #    Negative unit clauses             : 34
% 2.14/2.35  #    Non-unit-clauses                  : 385
% 2.14/2.35  # Current number of unprocessed clauses: 231062
% 2.14/2.35  # ...number of literals in the above   : 695585
% 2.14/2.35  # Current number of archived formulas  : 0
% 2.14/2.35  # Current number of archived clauses   : 771
% 2.14/2.35  # Clause-clause subsumption calls (NU) : 277586
% 2.14/2.35  # Rec. Clause-clause subsumption calls : 188655
% 2.14/2.35  # Non-unit clause-clause subsumptions  : 8030
% 2.14/2.35  # Unit Clause-clause subsumption calls : 9789
% 2.14/2.35  # Rewrite failures with RHS unbound    : 0
% 2.14/2.35  # BW rewrite match attempts            : 1406
% 2.14/2.35  # BW rewrite match successes           : 424
% 2.14/2.35  # Condensation attempts                : 0
% 2.14/2.35  # Condensation successes               : 0
% 2.14/2.35  # Termbank termtop insertions          : 5344330
% 2.14/2.36  
% 2.14/2.36  # -------------------------------------------------
% 2.14/2.36  # User time                : 1.927 s
% 2.14/2.36  # System time              : 0.091 s
% 2.14/2.36  # Total time               : 2.017 s
% 2.14/2.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
