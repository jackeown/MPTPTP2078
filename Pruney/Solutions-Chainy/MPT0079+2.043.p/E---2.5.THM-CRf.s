%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:06 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  124 (2134 expanded)
%              Number of clauses        :   95 (1002 expanded)
%              Number of leaves         :   14 ( 550 expanded)
%              Depth                    :   22
%              Number of atoms          :  177 (3305 expanded)
%              Number of equality atoms :   65 (1577 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_14,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,k2_xboole_0(X24,X25))
      | r1_tarski(k4_xboole_0(X23,X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_15,plain,(
    ! [X33,X34] : r1_tarski(X33,k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_16,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k3_xboole_0(X26,X27)) = k4_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_19,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_20,plain,(
    ! [X21,X22] : k4_xboole_0(k2_xboole_0(X21,X22),X22) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

cnf(c_0_33,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

fof(c_0_35,plain,(
    ! [X16] :
      ( X16 = k1_xboole_0
      | r2_hidden(esk2_1(X16),X16) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_28])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_39,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & r1_xboole_0(esk5_0,esk3_0)
    & r1_xboole_0(esk6_0,esk4_0)
    & esk5_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

fof(c_0_40,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,k1_xboole_0),k4_xboole_0(X1,X1))
    | r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_45,plain,(
    ! [X30,X31,X32] : k2_xboole_0(k2_xboole_0(X30,X31),X32) = k2_xboole_0(X30,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_42]),c_0_33])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)
    | r1_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_54,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_58,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) = k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_52])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_44])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_2(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_66,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_53]),c_0_47])).

cnf(c_0_67,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_52])).

cnf(c_0_71,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,k2_xboole_0(esk6_0,X1))) = k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_66]),c_0_52]),c_0_52])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk5_0,esk3_0),k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_47])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_29])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_74])).

cnf(c_0_80,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_47,c_0_37])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk6_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_75]),c_0_76])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_42]),c_0_28])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[c_0_79,c_0_76])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_57])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_88,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_84]),c_0_47])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_42])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_65])).

cnf(c_0_92,negated_conjecture,
    ( r1_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)),k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_59])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_66])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk3_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_60]),c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = k4_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100]),c_0_100])).

cnf(c_0_104,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_52])).

cnf(c_0_105,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_47])).

cnf(c_0_108,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(X1,esk6_0)) = k2_xboole_0(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_100])).

cnf(c_0_109,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_90])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk3_0),esk4_0)
    | ~ r1_tarski(X1,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_53])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,X1),k2_xboole_0(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk3_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_109]),c_0_28])).

cnf(c_0_114,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0)),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_47]),c_0_29]),c_0_113])).

cnf(c_0_116,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_80])).

cnf(c_0_117,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_115])).

cnf(c_0_119,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_116,c_0_44])).

cnf(c_0_120,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk6_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_103]),c_0_117]),c_0_28])).

cnf(c_0_121,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_118]),c_0_116]),c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( esk5_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_120]),c_0_121]),c_0_28]),c_0_122]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.31  % Computer   : n011.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 09:42:12 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.31  # Version: 2.5pre002
% 0.16/0.31  # No SInE strategy applied
% 0.16/0.31  # Trying AutoSched0 for 299 seconds
% 2.84/3.02  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 2.84/3.02  # and selection function SelectLargestOrientable.
% 2.84/3.02  #
% 2.84/3.02  # Preprocessing time       : 0.016 s
% 2.84/3.02  # Presaturation interreduction done
% 2.84/3.02  
% 2.84/3.02  # Proof found!
% 2.84/3.02  # SZS status Theorem
% 2.84/3.02  # SZS output start CNFRefutation
% 2.84/3.02  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.84/3.02  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.84/3.02  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.84/3.02  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.84/3.02  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.84/3.02  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.84/3.02  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.84/3.02  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.84/3.02  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 2.84/3.02  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.84/3.02  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.84/3.02  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.84/3.02  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.84/3.02  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.84/3.02  fof(c_0_14, plain, ![X23, X24, X25]:(~r1_tarski(X23,k2_xboole_0(X24,X25))|r1_tarski(k4_xboole_0(X23,X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 2.84/3.02  fof(c_0_15, plain, ![X33, X34]:r1_tarski(X33,k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 2.84/3.02  fof(c_0_16, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 2.84/3.02  fof(c_0_17, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.84/3.02  fof(c_0_18, plain, ![X26, X27]:k4_xboole_0(X26,k3_xboole_0(X26,X27))=k4_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 2.84/3.02  fof(c_0_19, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.84/3.02  fof(c_0_20, plain, ![X21, X22]:k4_xboole_0(k2_xboole_0(X21,X22),X22)=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 2.84/3.02  fof(c_0_21, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 2.84/3.02  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.84/3.02  cnf(c_0_23, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.84/3.02  cnf(c_0_24, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.84/3.02  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.84/3.02  cnf(c_0_26, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.84/3.02  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.84/3.02  cnf(c_0_28, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.84/3.02  cnf(c_0_29, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.84/3.02  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.84/3.02  cnf(c_0_31, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 2.84/3.02  fof(c_0_32, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 2.84/3.02  cnf(c_0_33, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 2.84/3.02  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 2.84/3.02  fof(c_0_35, plain, ![X16]:(X16=k1_xboole_0|r2_hidden(esk2_1(X16),X16)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 2.84/3.02  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_27, c_0_25])).
% 2.84/3.02  cnf(c_0_37, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_28])).
% 2.84/3.02  cnf(c_0_38, plain, (k2_xboole_0(k4_xboole_0(X1,X1),X2)=X2), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 2.84/3.02  fof(c_0_39, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)&r1_xboole_0(esk5_0,esk3_0))&r1_xboole_0(esk6_0,esk4_0))&esk5_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 2.84/3.02  fof(c_0_40, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.84/3.02  cnf(c_0_41, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.84/3.02  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.84/3.02  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,k1_xboole_0),k4_xboole_0(X1,X1))|r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 2.84/3.02  cnf(c_0_44, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.84/3.02  fof(c_0_45, plain, ![X30, X31, X32]:k2_xboole_0(k2_xboole_0(X30,X31),X32)=k2_xboole_0(X30,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 2.84/3.02  cnf(c_0_46, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.84/3.02  cnf(c_0_47, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.84/3.02  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 2.84/3.02  cnf(c_0_49, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(X2),X2)), inference(spm,[status(thm)],[c_0_28, c_0_42])).
% 2.84/3.02  cnf(c_0_50, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_42]), c_0_33])).
% 2.84/3.02  cnf(c_0_51, plain, (r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)|r1_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 2.84/3.02  cnf(c_0_52, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.84/3.02  cnf(c_0_53, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 2.84/3.02  fof(c_0_54, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 2.84/3.02  cnf(c_0_55, plain, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X2,X1)|~r1_xboole_0(X2,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 2.84/3.02  cnf(c_0_56, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 2.84/3.02  cnf(c_0_57, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.84/3.02  fof(c_0_58, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 2.84/3.02  cnf(c_0_59, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))=k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_52])).
% 2.84/3.02  cnf(c_0_60, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 2.84/3.02  cnf(c_0_61, plain, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X2,X1)|~r1_xboole_0(X2,k1_xboole_0)), inference(rw,[status(thm)],[c_0_55, c_0_44])).
% 2.84/3.02  cnf(c_0_62, negated_conjecture, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 2.84/3.02  cnf(c_0_63, plain, (r2_hidden(esk1_2(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))|r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 2.84/3.02  cnf(c_0_64, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.84/3.02  cnf(c_0_65, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.84/3.02  cnf(c_0_66, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_53]), c_0_47])).
% 2.84/3.02  cnf(c_0_67, plain, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 2.84/3.02  cnf(c_0_68, plain, (r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_63])).
% 2.84/3.02  cnf(c_0_69, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 2.84/3.02  cnf(c_0_70, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_23, c_0_52])).
% 2.84/3.02  cnf(c_0_71, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,k2_xboole_0(esk6_0,X1)))=k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_66]), c_0_52]), c_0_52])).
% 2.84/3.02  cnf(c_0_72, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_41, c_0_67])).
% 2.84/3.02  cnf(c_0_73, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 2.84/3.02  cnf(c_0_74, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_23, c_0_60])).
% 2.84/3.02  cnf(c_0_75, negated_conjecture, (r1_tarski(k2_xboole_0(esk5_0,esk3_0),k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 2.84/3.02  cnf(c_0_76, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_47])).
% 2.84/3.02  cnf(c_0_77, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_41, c_0_29])).
% 2.84/3.02  cnf(c_0_78, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 2.84/3.02  cnf(c_0_79, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_74])).
% 2.84/3.02  cnf(c_0_80, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_47, c_0_37])).
% 2.84/3.02  cnf(c_0_81, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk6_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_75]), c_0_76])).
% 2.84/3.02  cnf(c_0_82, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_42]), c_0_28])).
% 2.84/3.02  cnf(c_0_83, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 2.84/3.02  cnf(c_0_84, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[c_0_79, c_0_76])).
% 2.84/3.02  cnf(c_0_85, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_80])).
% 2.84/3.02  cnf(c_0_86, negated_conjecture, (r1_xboole_0(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_57])).
% 2.84/3.02  cnf(c_0_87, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk6_0,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 2.84/3.02  cnf(c_0_88, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_84]), c_0_47])).
% 2.84/3.02  cnf(c_0_89, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_41, c_0_28])).
% 2.84/3.02  cnf(c_0_90, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_85, c_0_42])).
% 2.84/3.02  cnf(c_0_91, negated_conjecture, (r1_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_68, c_0_65])).
% 2.84/3.02  cnf(c_0_92, negated_conjecture, (r1_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_68, c_0_86])).
% 2.84/3.02  cnf(c_0_93, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)),k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_59])).
% 2.84/3.02  cnf(c_0_94, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_29, c_0_66])).
% 2.84/3.02  cnf(c_0_95, negated_conjecture, (r1_tarski(esk3_0,esk6_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 2.84/3.02  cnf(c_0_96, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 2.84/3.02  cnf(c_0_97, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_72, c_0_91])).
% 2.84/3.02  cnf(c_0_98, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_72, c_0_92])).
% 2.84/3.02  cnf(c_0_99, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_60]), c_0_94])).
% 2.84/3.02  cnf(c_0_100, negated_conjecture, (k2_xboole_0(esk3_0,esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_30, c_0_95])).
% 2.84/3.02  cnf(c_0_101, negated_conjecture, (r1_tarski(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 2.84/3.02  cnf(c_0_102, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_77, c_0_98])).
% 2.84/3.02  cnf(c_0_103, negated_conjecture, (k4_xboole_0(esk4_0,esk6_0)=k4_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100]), c_0_100])).
% 2.84/3.02  cnf(c_0_104, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_47]), c_0_52])).
% 2.84/3.02  cnf(c_0_105, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)),X1)=X1), inference(spm,[status(thm)],[c_0_30, c_0_101])).
% 2.84/3.02  cnf(c_0_106, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0)))), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 2.84/3.02  cnf(c_0_107, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_22, c_0_47])).
% 2.84/3.02  cnf(c_0_108, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(X1,esk6_0))=k2_xboole_0(X1,esk6_0)), inference(spm,[status(thm)],[c_0_104, c_0_100])).
% 2.84/3.02  cnf(c_0_109, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_105])).
% 2.84/3.02  cnf(c_0_110, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0)),X1)), inference(spm,[status(thm)],[c_0_106, c_0_90])).
% 2.84/3.02  cnf(c_0_111, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk3_0),esk4_0)|~r1_tarski(X1,k2_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_107, c_0_53])).
% 2.84/3.02  cnf(c_0_112, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,X1),k2_xboole_0(X1,esk6_0))), inference(spm,[status(thm)],[c_0_70, c_0_108])).
% 2.84/3.02  cnf(c_0_113, negated_conjecture, (k4_xboole_0(esk5_0,esk3_0)=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_109]), c_0_28])).
% 2.84/3.02  cnf(c_0_114, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0)),X1)=X1), inference(spm,[status(thm)],[c_0_30, c_0_110])).
% 2.84/3.02  cnf(c_0_115, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_47]), c_0_29]), c_0_113])).
% 2.84/3.02  cnf(c_0_116, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_80])).
% 2.84/3.02  cnf(c_0_117, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_114])).
% 2.84/3.02  cnf(c_0_118, negated_conjecture, (k2_xboole_0(esk5_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_30, c_0_115])).
% 2.84/3.02  cnf(c_0_119, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_116, c_0_44])).
% 2.84/3.02  cnf(c_0_120, negated_conjecture, (k4_xboole_0(esk5_0,esk6_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_103]), c_0_117]), c_0_28])).
% 2.84/3.02  cnf(c_0_121, negated_conjecture, (k4_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_118]), c_0_116]), c_0_119])).
% 2.84/3.02  cnf(c_0_122, negated_conjecture, (esk5_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.84/3.02  cnf(c_0_123, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_120]), c_0_121]), c_0_28]), c_0_122]), ['proof']).
% 2.84/3.02  # SZS output end CNFRefutation
% 2.84/3.02  # Proof object total steps             : 124
% 2.84/3.02  # Proof object clause steps            : 95
% 2.84/3.02  # Proof object formula steps           : 29
% 2.84/3.02  # Proof object conjectures             : 47
% 2.84/3.02  # Proof object clause conjectures      : 44
% 2.84/3.02  # Proof object formula conjectures     : 3
% 2.84/3.02  # Proof object initial clauses used    : 18
% 2.84/3.02  # Proof object initial formulas used   : 14
% 2.84/3.02  # Proof object generating inferences   : 66
% 2.84/3.02  # Proof object simplifying inferences  : 37
% 2.84/3.02  # Training examples: 0 positive, 0 negative
% 2.84/3.02  # Parsed axioms                        : 14
% 2.84/3.02  # Removed by relevancy pruning/SinE    : 0
% 2.84/3.02  # Initial clauses                      : 18
% 2.84/3.02  # Removed in clause preprocessing      : 1
% 2.84/3.02  # Initial clauses in saturation        : 17
% 2.84/3.02  # Processed clauses                    : 15247
% 2.84/3.02  # ...of these trivial                  : 1509
% 2.84/3.02  # ...subsumed                          : 11907
% 2.84/3.02  # ...remaining for further processing  : 1831
% 2.84/3.02  # Other redundant clauses eliminated   : 8
% 2.84/3.02  # Clauses deleted for lack of memory   : 0
% 2.84/3.02  # Backward-subsumed                    : 135
% 2.84/3.02  # Backward-rewritten                   : 884
% 2.84/3.02  # Generated clauses                    : 229923
% 2.84/3.02  # ...of the previous two non-trivial   : 153341
% 2.84/3.02  # Contextual simplify-reflections      : 15
% 2.84/3.02  # Paramodulations                      : 229894
% 2.84/3.02  # Factorizations                       : 20
% 2.84/3.02  # Equation resolutions                 : 8
% 2.84/3.02  # Propositional unsat checks           : 0
% 2.84/3.02  #    Propositional check models        : 0
% 2.84/3.02  #    Propositional check unsatisfiable : 0
% 2.84/3.02  #    Propositional clauses             : 0
% 2.84/3.02  #    Propositional clauses after purity: 0
% 2.84/3.02  #    Propositional unsat core size     : 0
% 2.84/3.02  #    Propositional preprocessing time  : 0.000
% 2.84/3.02  #    Propositional encoding time       : 0.000
% 2.84/3.02  #    Propositional solver time         : 0.000
% 2.84/3.02  #    Success case prop preproc time    : 0.000
% 2.84/3.02  #    Success case prop encoding time   : 0.000
% 2.84/3.02  #    Success case prop solver time     : 0.000
% 2.84/3.02  # Current number of processed clauses  : 794
% 2.84/3.02  #    Positive orientable unit clauses  : 346
% 2.84/3.02  #    Positive unorientable unit clauses: 6
% 2.84/3.02  #    Negative unit clauses             : 29
% 2.84/3.02  #    Non-unit-clauses                  : 413
% 2.84/3.02  # Current number of unprocessed clauses: 131130
% 2.84/3.02  # ...number of literals in the above   : 374599
% 2.84/3.02  # Current number of archived formulas  : 0
% 2.84/3.02  # Current number of archived clauses   : 1038
% 2.84/3.02  # Clause-clause subsumption calls (NU) : 198041
% 2.84/3.02  # Rec. Clause-clause subsumption calls : 121362
% 2.84/3.02  # Non-unit clause-clause subsumptions  : 6968
% 2.84/3.02  # Unit Clause-clause subsumption calls : 7709
% 2.84/3.02  # Rewrite failures with RHS unbound    : 0
% 2.84/3.02  # BW rewrite match attempts            : 2057
% 2.84/3.02  # BW rewrite match successes           : 593
% 2.84/3.02  # Condensation attempts                : 0
% 2.84/3.02  # Condensation successes               : 0
% 2.84/3.02  # Termbank termtop insertions          : 3647357
% 2.84/3.03  
% 2.84/3.03  # -------------------------------------------------
% 2.84/3.03  # User time                : 2.637 s
% 2.84/3.03  # System time              : 0.075 s
% 2.84/3.03  # Total time               : 2.712 s
% 2.84/3.03  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
