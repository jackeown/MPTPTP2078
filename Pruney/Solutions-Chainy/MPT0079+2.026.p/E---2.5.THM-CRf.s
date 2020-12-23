%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:03 EST 2020

% Result     : Theorem 9.88s
% Output     : CNFRefutation 9.88s
% Verified   : 
% Statistics : Number of formulae       :  128 (7811 expanded)
%              Number of clauses        :   99 (3361 expanded)
%              Number of leaves         :   14 (2148 expanded)
%              Depth                    :   19
%              Number of atoms          :  161 (9417 expanded)
%              Number of equality atoms :  113 (8144 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_15,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & r1_xboole_0(esk5_0,esk3_0)
    & r1_xboole_0(esk6_0,esk4_0)
    & esk5_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_17,plain,(
    ! [X33,X34] : k2_xboole_0(k3_xboole_0(X33,X34),k4_xboole_0(X33,X34)) = X33 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_18,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,plain,(
    ! [X21,X22] : k4_xboole_0(k2_xboole_0(X21,X22),X22) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X17] : k2_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X18,X19] : k2_xboole_0(X18,k4_xboole_0(X19,X18)) = k2_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_28,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,plain,(
    ! [X30,X31,X32] : k2_xboole_0(k2_xboole_0(X30,X31),X32) = k2_xboole_0(X30,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_21]),c_0_31]),c_0_21])).

fof(c_0_37,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_31]),c_0_21]),c_0_27])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_24]),c_0_24])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk5_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_38]),c_0_21]),c_0_21]),c_0_39])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

fof(c_0_46,plain,(
    ! [X23,X24,X25] : k4_xboole_0(k4_xboole_0(X23,X24),X25) = k4_xboole_0(X23,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_44]),c_0_45])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

fof(c_0_50,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r1_xboole_0(X9,X10)
        | r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X14,k3_xboole_0(X12,X13))
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_51,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) = k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_40])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_44]),c_0_41]),c_0_48]),c_0_43]),c_0_49])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0))) = k2_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_39])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)),k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_51])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,k2_xboole_0(X1,X2)))) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_40]),c_0_40])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk5_0,X1)) = k2_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_24])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_38]),c_0_21]),c_0_44])).

fof(c_0_64,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk2_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk5_0,esk3_0)) = k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_38]),c_0_21]),c_0_21])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_41]),c_0_21]),c_0_36])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(esk5_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_60]),c_0_45])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_52]),c_0_52])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_49]),c_0_52])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_41])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_24])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_27])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_63]),c_0_45])).

fof(c_0_77,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k3_xboole_0(X26,X27)) = k4_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_79,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk6_0,esk5_0)) = k2_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_65]),c_0_59]),c_0_49])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_52])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_21])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X3,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_83,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_68]),c_0_27]),c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(X1,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_49]),c_0_47]),c_0_35])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X2)))))
    | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),X4),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_49]),c_0_40]),c_0_40]),c_0_49]),c_0_72])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X1),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_52])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_39]),c_0_45])).

cnf(c_0_88,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_75]),c_0_76]),c_0_43])).

cnf(c_0_91,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_92,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_78]),c_0_43])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk3_0)) = k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_79]),c_0_49]),c_0_52]),c_0_52])).

cnf(c_0_94,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_95,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk3_0),k4_xboole_0(esk6_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_47]),c_0_84])).

cnf(c_0_96,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X4,k4_xboole_0(X3,X2))))
    | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),X4),X2) ),
    inference(rw,[status(thm)],[c_0_85,c_0_81])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(k4_xboole_0(esk4_0,esk3_0),X1)) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_32]),c_0_87]),c_0_35])).

cnf(c_0_98,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk4_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_32]),c_0_87]),c_0_35])).

cnf(c_0_99,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_100,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k4_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_72])).

cnf(c_0_101,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),X1)) = k4_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_90])).

cnf(c_0_102,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_32]),c_0_52])).

cnf(c_0_103,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_91,c_0_24])).

cnf(c_0_104,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = X3
    | r2_hidden(esk2_1(k4_xboole_0(X3,k4_xboole_0(X1,X2))),k4_xboole_0(X3,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_92]),c_0_52]),c_0_81])).

cnf(c_0_105,negated_conjecture,
    ( k2_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk3_0)) = k2_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_93]),c_0_81])).

cnf(c_0_106,negated_conjecture,
    ( k4_xboole_0(esk6_0,k2_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk3_0))) = k4_xboole_0(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_49]),c_0_93]),c_0_81])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk6_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_99])])).

cnf(c_0_108,negated_conjecture,
    ( k4_xboole_0(esk6_0,k2_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0))) = k4_xboole_0(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_21])).

cnf(c_0_109,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_83]),c_0_102])).

cnf(c_0_110,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_78]),c_0_43])).

cnf(c_0_111,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk5_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_87]),c_0_29])).

cnf(c_0_112,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_113,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_67]),c_0_49])).

cnf(c_0_114,negated_conjecture,
    ( k2_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk4_0))) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_108]),c_0_31])).

cnf(c_0_115,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) = esk4_0
    | r2_hidden(esk2_1(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)))),k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_109]),c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112]),c_0_21])).

cnf(c_0_117,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))))
    | ~ r1_xboole_0(k2_xboole_0(esk3_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_109])).

cnf(c_0_118,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_119,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),k4_xboole_0(esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_90])).

cnf(c_0_120,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk6_0) = esk4_0
    | r2_hidden(esk2_1(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0))),k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116]),c_0_116]),c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_116]),c_0_116]),c_0_118])])).

cnf(c_0_122,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_119]),c_0_52]),c_0_38]),c_0_21]),c_0_52]),c_0_59]),c_0_81]),c_0_41])).

cnf(c_0_123,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk3_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_112]),c_0_45]),c_0_29])).

cnf(c_0_124,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk6_0) = esk4_0 ),
    inference(sr,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_125,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123]),c_0_45]),c_0_29])).

cnf(c_0_126,negated_conjecture,
    ( esk5_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_127,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_124]),c_0_125]),c_0_126]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:58:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 9.88/10.12  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 9.88/10.12  # and selection function SelectLargestOrientable.
% 9.88/10.12  #
% 9.88/10.12  # Preprocessing time       : 0.027 s
% 9.88/10.12  # Presaturation interreduction done
% 9.88/10.12  
% 9.88/10.12  # Proof found!
% 9.88/10.12  # SZS status Theorem
% 9.88/10.12  # SZS output start CNFRefutation
% 9.88/10.12  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 9.88/10.12  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.88/10.12  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 9.88/10.12  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.88/10.12  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 9.88/10.12  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.88/10.12  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.88/10.12  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.88/10.12  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 9.88/10.12  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.88/10.12  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.88/10.12  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.88/10.12  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.88/10.12  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 9.88/10.12  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 9.88/10.12  fof(c_0_15, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)&r1_xboole_0(esk5_0,esk3_0))&r1_xboole_0(esk6_0,esk4_0))&esk5_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 9.88/10.12  fof(c_0_16, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 9.88/10.12  fof(c_0_17, plain, ![X33, X34]:k2_xboole_0(k3_xboole_0(X33,X34),k4_xboole_0(X33,X34))=X33, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 9.88/10.12  fof(c_0_18, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 9.88/10.12  fof(c_0_19, plain, ![X21, X22]:k4_xboole_0(k2_xboole_0(X21,X22),X22)=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 9.88/10.12  cnf(c_0_20, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.88/10.12  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 9.88/10.12  fof(c_0_22, plain, ![X17]:k2_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t1_boole])).
% 9.88/10.12  cnf(c_0_23, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.88/10.12  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 9.88/10.12  fof(c_0_25, plain, ![X18, X19]:k2_xboole_0(X18,k4_xboole_0(X19,X18))=k2_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 9.88/10.12  cnf(c_0_26, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 9.88/10.12  cnf(c_0_27, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 9.88/10.12  fof(c_0_28, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 9.88/10.12  cnf(c_0_29, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 9.88/10.12  cnf(c_0_30, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 9.88/10.12  cnf(c_0_31, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 9.88/10.12  cnf(c_0_32, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0)=k4_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 9.88/10.12  fof(c_0_33, plain, ![X30, X31, X32]:k2_xboole_0(k2_xboole_0(X30,X31),X32)=k2_xboole_0(X30,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 9.88/10.12  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 9.88/10.12  cnf(c_0_35, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 9.88/10.12  cnf(c_0_36, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_21]), c_0_31]), c_0_21])).
% 9.88/10.12  fof(c_0_37, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 9.88/10.12  cnf(c_0_38, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_31])).
% 9.88/10.12  cnf(c_0_39, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_31]), c_0_21]), c_0_27])).
% 9.88/10.12  cnf(c_0_40, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 9.88/10.12  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_24]), c_0_24])).
% 9.88/10.12  cnf(c_0_42, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 9.88/10.12  cnf(c_0_43, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 9.88/10.12  cnf(c_0_44, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk5_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_38]), c_0_21]), c_0_21]), c_0_39])).
% 9.88/10.12  cnf(c_0_45, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 9.88/10.12  fof(c_0_46, plain, ![X23, X24, X25]:k4_xboole_0(k4_xboole_0(X23,X24),X25)=k4_xboole_0(X23,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 9.88/10.12  cnf(c_0_47, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 9.88/10.12  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_44]), c_0_45])).
% 9.88/10.12  cnf(c_0_49, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 9.88/10.12  fof(c_0_50, plain, ![X9, X10, X12, X13, X14]:((r1_xboole_0(X9,X10)|r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)))&(~r2_hidden(X14,k3_xboole_0(X12,X13))|~r1_xboole_0(X12,X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 9.88/10.12  cnf(c_0_51, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))=k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_27]), c_0_40])).
% 9.88/10.12  cnf(c_0_52, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 9.88/10.12  cnf(c_0_53, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k2_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_40, c_0_36])).
% 9.88/10.12  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_44]), c_0_41]), c_0_48]), c_0_43]), c_0_49])).
% 9.88/10.12  cnf(c_0_55, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 9.88/10.12  cnf(c_0_56, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0)))=k2_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_51, c_0_39])).
% 9.88/10.12  cnf(c_0_57, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)),k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_26, c_0_51])).
% 9.88/10.12  cnf(c_0_58, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,k2_xboole_0(X1,X2))))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_40]), c_0_40])).
% 9.88/10.12  cnf(c_0_59, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_31, c_0_52])).
% 9.88/10.12  cnf(c_0_60, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk5_0,X1))=k2_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 9.88/10.12  cnf(c_0_61, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_55, c_0_24])).
% 9.88/10.12  cnf(c_0_62, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 9.88/10.12  cnf(c_0_63, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_38]), c_0_21]), c_0_44])).
% 9.88/10.12  fof(c_0_64, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk2_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 9.88/10.12  cnf(c_0_65, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk5_0,esk3_0))=k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_38]), c_0_21]), c_0_21])).
% 9.88/10.12  cnf(c_0_66, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3)=k4_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 9.88/10.12  cnf(c_0_67, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1)))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 9.88/10.12  cnf(c_0_68, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 9.88/10.12  cnf(c_0_69, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_41]), c_0_21]), c_0_36])).
% 9.88/10.12  cnf(c_0_70, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(esk5_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_60]), c_0_45])).
% 9.88/10.12  cnf(c_0_71, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))))|~r1_xboole_0(k4_xboole_0(X2,X3),X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_52]), c_0_52])).
% 9.88/10.12  cnf(c_0_72, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_49]), c_0_52])).
% 9.88/10.12  cnf(c_0_73, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_61, c_0_41])).
% 9.88/10.12  cnf(c_0_74, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_62, c_0_24])).
% 9.88/10.12  cnf(c_0_75, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_27])).
% 9.88/10.12  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_63]), c_0_45])).
% 9.88/10.12  fof(c_0_77, plain, ![X26, X27]:k4_xboole_0(X26,k3_xboole_0(X26,X27))=k4_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 9.88/10.12  cnf(c_0_78, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 9.88/10.12  cnf(c_0_79, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk6_0,esk5_0))=k2_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_65]), c_0_59]), c_0_49])).
% 9.88/10.12  cnf(c_0_80, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_52])).
% 9.88/10.12  cnf(c_0_81, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_59, c_0_21])).
% 9.88/10.12  cnf(c_0_82, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X3,X1))=k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 9.88/10.12  cnf(c_0_83, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_68]), c_0_27]), c_0_21])).
% 9.88/10.12  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(X1,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_49]), c_0_47]), c_0_35])).
% 9.88/10.12  cnf(c_0_85, plain, (~r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X2)))))|~r1_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),X4),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_49]), c_0_40]), c_0_40]), c_0_49]), c_0_72])).
% 9.88/10.12  cnf(c_0_86, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X1),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_52])).
% 9.88/10.12  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_39]), c_0_45])).
% 9.88/10.12  cnf(c_0_88, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 9.88/10.12  cnf(c_0_89, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.88/10.12  cnf(c_0_90, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk3_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_75]), c_0_76]), c_0_43])).
% 9.88/10.12  cnf(c_0_91, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 9.88/10.12  cnf(c_0_92, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_78]), c_0_43])).
% 9.88/10.12  cnf(c_0_93, negated_conjecture, (k4_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk3_0))=k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_79]), c_0_49]), c_0_52]), c_0_52])).
% 9.88/10.12  cnf(c_0_94, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 9.88/10.12  cnf(c_0_95, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk3_0),k4_xboole_0(esk6_0,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_47]), c_0_84])).
% 9.88/10.12  cnf(c_0_96, plain, (~r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X4,k4_xboole_0(X3,X2))))|~r1_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),X4),X2)), inference(rw,[status(thm)],[c_0_85, c_0_81])).
% 9.88/10.12  cnf(c_0_97, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(k4_xboole_0(esk4_0,esk3_0),X1))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_32]), c_0_87]), c_0_35])).
% 9.88/10.12  cnf(c_0_98, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk4_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_32]), c_0_87]), c_0_35])).
% 9.88/10.12  cnf(c_0_99, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 9.88/10.12  cnf(c_0_100, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k4_xboole_0(X2,k2_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_72])).
% 9.88/10.12  cnf(c_0_101, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),X1))=k4_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_90])).
% 9.88/10.12  cnf(c_0_102, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_32]), c_0_52])).
% 9.88/10.12  cnf(c_0_103, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_91, c_0_24])).
% 9.88/10.12  cnf(c_0_104, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=X3|r2_hidden(esk2_1(k4_xboole_0(X3,k4_xboole_0(X1,X2))),k4_xboole_0(X3,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_92]), c_0_52]), c_0_81])).
% 9.88/10.12  cnf(c_0_105, negated_conjecture, (k2_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk3_0))=k2_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_93]), c_0_81])).
% 9.88/10.12  cnf(c_0_106, negated_conjecture, (k4_xboole_0(esk6_0,k2_xboole_0(esk5_0,k4_xboole_0(esk4_0,esk3_0)))=k4_xboole_0(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_49]), c_0_93]), c_0_81])).
% 9.88/10.12  cnf(c_0_107, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk6_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_99])])).
% 9.88/10.12  cnf(c_0_108, negated_conjecture, (k4_xboole_0(esk6_0,k2_xboole_0(esk5_0,k4_xboole_0(esk3_0,esk4_0)))=k4_xboole_0(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_21])).
% 9.88/10.12  cnf(c_0_109, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_83]), c_0_102])).
% 9.88/10.12  cnf(c_0_110, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_78]), c_0_43])).
% 9.88/10.12  cnf(c_0_111, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk5_0))=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_87]), c_0_29])).
% 9.88/10.12  cnf(c_0_112, negated_conjecture, (k4_xboole_0(esk3_0,esk5_0)=esk3_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106]), c_0_107])).
% 9.88/10.12  cnf(c_0_113, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),X3)=k4_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_67]), c_0_49])).
% 9.88/10.12  cnf(c_0_114, negated_conjecture, (k2_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk4_0)))=k2_xboole_0(esk5_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_108]), c_0_31])).
% 9.88/10.12  cnf(c_0_115, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))=esk4_0|r2_hidden(esk2_1(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)))),k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_109]), c_0_109])).
% 9.88/10.12  cnf(c_0_116, negated_conjecture, (k2_xboole_0(esk3_0,esk6_0)=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_112]), c_0_21])).
% 9.88/10.12  cnf(c_0_117, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))))|~r1_xboole_0(k2_xboole_0(esk3_0,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_109])).
% 9.88/10.12  cnf(c_0_118, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.88/10.12  cnf(c_0_119, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),k4_xboole_0(esk3_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_90])).
% 9.88/10.12  cnf(c_0_120, negated_conjecture, (k4_xboole_0(esk5_0,esk6_0)=esk4_0|r2_hidden(esk2_1(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0))),k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116]), c_0_116]), c_0_116])).
% 9.88/10.12  cnf(c_0_121, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_116]), c_0_116]), c_0_118])])).
% 9.88/10.12  cnf(c_0_122, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))=k2_xboole_0(esk5_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_119]), c_0_52]), c_0_38]), c_0_21]), c_0_52]), c_0_59]), c_0_81]), c_0_41])).
% 9.88/10.12  cnf(c_0_123, negated_conjecture, (k4_xboole_0(esk5_0,esk3_0)=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_112]), c_0_45]), c_0_29])).
% 9.88/10.12  cnf(c_0_124, negated_conjecture, (k4_xboole_0(esk5_0,esk6_0)=esk4_0), inference(sr,[status(thm)],[c_0_120, c_0_121])).
% 9.88/10.12  cnf(c_0_125, negated_conjecture, (k2_xboole_0(esk5_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_123]), c_0_45]), c_0_29])).
% 9.88/10.12  cnf(c_0_126, negated_conjecture, (esk5_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.88/10.12  cnf(c_0_127, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_124]), c_0_125]), c_0_126]), ['proof']).
% 9.88/10.12  # SZS output end CNFRefutation
% 9.88/10.12  # Proof object total steps             : 128
% 9.88/10.12  # Proof object clause steps            : 99
% 9.88/10.12  # Proof object formula steps           : 29
% 9.88/10.12  # Proof object conjectures             : 53
% 9.88/10.12  # Proof object clause conjectures      : 50
% 9.88/10.12  # Proof object formula conjectures     : 3
% 9.88/10.12  # Proof object initial clauses used    : 18
% 9.88/10.12  # Proof object initial formulas used   : 14
% 9.88/10.12  # Proof object generating inferences   : 65
% 9.88/10.12  # Proof object simplifying inferences  : 113
% 9.88/10.12  # Training examples: 0 positive, 0 negative
% 9.88/10.12  # Parsed axioms                        : 14
% 9.88/10.12  # Removed by relevancy pruning/SinE    : 0
% 9.88/10.12  # Initial clauses                      : 18
% 9.88/10.12  # Removed in clause preprocessing      : 1
% 9.88/10.12  # Initial clauses in saturation        : 17
% 9.88/10.12  # Processed clauses                    : 34184
% 9.88/10.12  # ...of these trivial                  : 1902
% 9.88/10.12  # ...subsumed                          : 29644
% 9.88/10.12  # ...remaining for further processing  : 2638
% 9.88/10.12  # Other redundant clauses eliminated   : 31
% 9.88/10.12  # Clauses deleted for lack of memory   : 0
% 9.88/10.12  # Backward-subsumed                    : 126
% 9.88/10.12  # Backward-rewritten                   : 1264
% 9.88/10.12  # Generated clauses                    : 1225793
% 9.88/10.12  # ...of the previous two non-trivial   : 993747
% 9.88/10.12  # Contextual simplify-reflections      : 7
% 9.88/10.12  # Paramodulations                      : 1225749
% 9.88/10.12  # Factorizations                       : 12
% 9.88/10.12  # Equation resolutions                 : 31
% 9.88/10.12  # Propositional unsat checks           : 0
% 9.88/10.12  #    Propositional check models        : 0
% 9.88/10.12  #    Propositional check unsatisfiable : 0
% 9.88/10.12  #    Propositional clauses             : 0
% 9.88/10.12  #    Propositional clauses after purity: 0
% 9.88/10.12  #    Propositional unsat core size     : 0
% 9.88/10.12  #    Propositional preprocessing time  : 0.000
% 9.88/10.12  #    Propositional encoding time       : 0.000
% 9.88/10.12  #    Propositional solver time         : 0.000
% 9.88/10.12  #    Success case prop preproc time    : 0.000
% 9.88/10.12  #    Success case prop encoding time   : 0.000
% 9.88/10.12  #    Success case prop solver time     : 0.000
% 9.88/10.12  # Current number of processed clauses  : 1230
% 9.88/10.12  #    Positive orientable unit clauses  : 381
% 9.88/10.12  #    Positive unorientable unit clauses: 15
% 9.88/10.12  #    Negative unit clauses             : 41
% 9.88/10.12  #    Non-unit-clauses                  : 793
% 9.88/10.12  # Current number of unprocessed clauses: 948956
% 9.88/10.12  # ...number of literals in the above   : 2657623
% 9.88/10.12  # Current number of archived formulas  : 0
% 9.88/10.12  # Current number of archived clauses   : 1409
% 9.88/10.12  # Clause-clause subsumption calls (NU) : 923156
% 9.88/10.12  # Rec. Clause-clause subsumption calls : 558994
% 9.88/10.12  # Non-unit clause-clause subsumptions  : 18304
% 9.88/10.12  # Unit Clause-clause subsumption calls : 30198
% 9.88/10.12  # Rewrite failures with RHS unbound    : 0
% 9.88/10.12  # BW rewrite match attempts            : 6263
% 9.88/10.12  # BW rewrite match successes           : 746
% 9.88/10.12  # Condensation attempts                : 0
% 9.88/10.12  # Condensation successes               : 0
% 9.88/10.12  # Termbank termtop insertions          : 24594839
% 9.98/10.16  
% 9.98/10.16  # -------------------------------------------------
% 9.98/10.16  # User time                : 9.403 s
% 9.98/10.16  # System time              : 0.422 s
% 9.98/10.16  # Total time               : 9.825 s
% 9.98/10.16  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
