%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:04 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 839 expanded)
%              Number of clauses        :   55 ( 380 expanded)
%              Number of leaves         :   13 ( 219 expanded)
%              Depth                    :   17
%              Number of atoms          :  117 (1546 expanded)
%              Number of equality atoms :   72 ( 770 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(c_0_13,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_18,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = k2_xboole_0(esk4_0,esk5_0)
    & r1_xboole_0(esk4_0,esk2_0)
    & r1_xboole_0(esk5_0,esk3_0)
    & esk4_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_22,plain,(
    ! [X16] : k3_xboole_0(X16,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_23,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k3_xboole_0(X25,X26)) = k4_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X19] : k4_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X22,X23,X24] : k4_xboole_0(k4_xboole_0(X22,X23),X24) = k4_xboole_0(X22,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_37,plain,(
    ! [X17,X18] : k2_xboole_0(X17,k4_xboole_0(X18,X17)) = k2_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_38,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_33])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = k2_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_35])).

fof(c_0_48,plain,(
    ! [X9] : k2_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_41])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,X1)) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_47])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_49]),c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_42]),c_0_53])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk4_0,X1)) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_55]),c_0_56])).

fof(c_0_60,plain,(
    ! [X29,X30,X31] : k2_xboole_0(k2_xboole_0(X29,X30),X31) = k2_xboole_0(X29,k2_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_25])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_54])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_42])])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) = k2_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_59])).

fof(c_0_66,plain,(
    ! [X20,X21] : k4_xboole_0(k2_xboole_0(X20,X21),X21) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(X1,esk3_0)) = k2_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_46])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_46]),c_0_63])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk4_0) = k2_xboole_0(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_51]),c_0_46]),c_0_69]),c_0_53])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_33])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_44])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_71]),c_0_35])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_72]),c_0_70]),c_0_54])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_73]),c_0_35])).

cnf(c_0_78,negated_conjecture,
    ( esk4_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_79,negated_conjecture,
    ( esk3_0 = k4_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_62]),c_0_46]),c_0_51]),c_0_72]),c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk2_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_76]),c_0_46]),c_0_72]),c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n007.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 12:03:36 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.32  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.36  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.17/0.36  # and selection function SelectNewComplexAHP.
% 0.17/0.36  #
% 0.17/0.36  # Preprocessing time       : 0.026 s
% 0.17/0.36  
% 0.17/0.36  # Proof found!
% 0.17/0.36  # SZS status Theorem
% 0.17/0.36  # SZS output start CNFRefutation
% 0.17/0.36  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.17/0.36  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.17/0.36  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.17/0.36  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.17/0.36  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.17/0.36  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.17/0.36  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.17/0.36  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.17/0.36  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.17/0.36  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.17/0.36  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.17/0.36  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.17/0.36  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.17/0.36  fof(c_0_13, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk1_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk1_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.17/0.36  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.36  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.36  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.17/0.36  fof(c_0_17, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.17/0.36  fof(c_0_18, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.17/0.36  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.17/0.36  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.36  fof(c_0_21, negated_conjecture, (((k2_xboole_0(esk2_0,esk3_0)=k2_xboole_0(esk4_0,esk5_0)&r1_xboole_0(esk4_0,esk2_0))&r1_xboole_0(esk5_0,esk3_0))&esk4_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.17/0.36  fof(c_0_22, plain, ![X16]:k3_xboole_0(X16,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.17/0.36  fof(c_0_23, plain, ![X25, X26]:k4_xboole_0(X25,k3_xboole_0(X25,X26))=k4_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.17/0.36  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.36  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.36  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.17/0.36  cnf(c_0_27, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.36  cnf(c_0_28, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.36  fof(c_0_29, plain, ![X19]:k4_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.17/0.36  cnf(c_0_30, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.36  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.17/0.36  cnf(c_0_32, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.17/0.36  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.36  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_28, c_0_25])).
% 0.17/0.36  cnf(c_0_35, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.17/0.36  fof(c_0_36, plain, ![X22, X23, X24]:k4_xboole_0(k4_xboole_0(X22,X23),X24)=k4_xboole_0(X22,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.17/0.36  fof(c_0_37, plain, ![X17, X18]:k2_xboole_0(X17,k4_xboole_0(X18,X17))=k2_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.17/0.36  fof(c_0_38, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.17/0.36  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_25])).
% 0.17/0.36  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.17/0.36  cnf(c_0_41, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_33])).
% 0.17/0.36  cnf(c_0_42, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.17/0.36  cnf(c_0_43, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.17/0.36  cnf(c_0_44, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.17/0.36  cnf(c_0_45, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=k2_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.36  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.17/0.36  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk3_0,esk5_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_35])).
% 0.17/0.36  fof(c_0_48, plain, ![X9]:k2_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.17/0.36  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_41])).
% 0.17/0.36  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.17/0.36  cnf(c_0_51, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=k2_xboole_0(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.17/0.36  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,X1))=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_47])).
% 0.17/0.36  cnf(c_0_53, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.17/0.36  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk2_0,esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_49]), c_0_35])).
% 0.17/0.36  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.17/0.36  cnf(c_0_56, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_42]), c_0_53])).
% 0.17/0.36  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.36  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk4_0,X1))=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_54])).
% 0.17/0.36  cnf(c_0_59, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_55]), c_0_56])).
% 0.17/0.36  fof(c_0_60, plain, ![X29, X30, X31]:k2_xboole_0(k2_xboole_0(X29,X30),X31)=k2_xboole_0(X29,k2_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.17/0.36  cnf(c_0_61, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_57, c_0_25])).
% 0.17/0.36  cnf(c_0_62, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_54])).
% 0.17/0.36  cnf(c_0_63, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.17/0.36  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_42])])).
% 0.17/0.36  cnf(c_0_65, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))=k2_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_59])).
% 0.17/0.36  fof(c_0_66, plain, ![X20, X21]:k4_xboole_0(k2_xboole_0(X20,X21),X21)=k4_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.17/0.36  cnf(c_0_67, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_64])).
% 0.17/0.36  cnf(c_0_68, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(X1,esk3_0))=k2_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_65, c_0_46])).
% 0.17/0.36  cnf(c_0_69, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_46]), c_0_63])).
% 0.17/0.36  cnf(c_0_70, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.17/0.36  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_67])).
% 0.17/0.36  cnf(c_0_72, negated_conjecture, (k2_xboole_0(esk5_0,esk4_0)=k2_xboole_0(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_51]), c_0_46]), c_0_69]), c_0_53])).
% 0.17/0.36  cnf(c_0_73, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_33])).
% 0.17/0.36  cnf(c_0_74, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_70, c_0_44])).
% 0.17/0.36  cnf(c_0_75, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_71]), c_0_35])).
% 0.17/0.36  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk5_0,esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_72]), c_0_70]), c_0_54])).
% 0.17/0.36  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk4_0,esk2_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_73]), c_0_35])).
% 0.17/0.36  cnf(c_0_78, negated_conjecture, (esk4_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.36  cnf(c_0_79, negated_conjecture, (esk3_0=k4_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_62]), c_0_46]), c_0_51]), c_0_72]), c_0_75])).
% 0.17/0.36  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk2_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_76]), c_0_46]), c_0_72]), c_0_77])).
% 0.17/0.36  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79]), c_0_80])]), ['proof']).
% 0.17/0.36  # SZS output end CNFRefutation
% 0.17/0.36  # Proof object total steps             : 82
% 0.17/0.36  # Proof object clause steps            : 55
% 0.17/0.36  # Proof object formula steps           : 27
% 0.17/0.36  # Proof object conjectures             : 32
% 0.17/0.36  # Proof object clause conjectures      : 29
% 0.17/0.36  # Proof object formula conjectures     : 3
% 0.17/0.36  # Proof object initial clauses used    : 19
% 0.17/0.36  # Proof object initial formulas used   : 13
% 0.17/0.36  # Proof object generating inferences   : 29
% 0.17/0.36  # Proof object simplifying inferences  : 33
% 0.17/0.36  # Training examples: 0 positive, 0 negative
% 0.17/0.36  # Parsed axioms                        : 13
% 0.17/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.36  # Initial clauses                      : 19
% 0.17/0.36  # Removed in clause preprocessing      : 1
% 0.17/0.36  # Initial clauses in saturation        : 18
% 0.17/0.36  # Processed clauses                    : 136
% 0.17/0.36  # ...of these trivial                  : 22
% 0.17/0.36  # ...subsumed                          : 16
% 0.17/0.36  # ...remaining for further processing  : 97
% 0.17/0.36  # Other redundant clauses eliminated   : 0
% 0.17/0.36  # Clauses deleted for lack of memory   : 0
% 0.17/0.36  # Backward-subsumed                    : 1
% 0.17/0.36  # Backward-rewritten                   : 43
% 0.17/0.36  # Generated clauses                    : 888
% 0.17/0.36  # ...of the previous two non-trivial   : 625
% 0.17/0.36  # Contextual simplify-reflections      : 0
% 0.17/0.36  # Paramodulations                      : 887
% 0.17/0.36  # Factorizations                       : 0
% 0.17/0.36  # Equation resolutions                 : 1
% 0.17/0.36  # Propositional unsat checks           : 0
% 0.17/0.36  #    Propositional check models        : 0
% 0.17/0.36  #    Propositional check unsatisfiable : 0
% 0.17/0.36  #    Propositional clauses             : 0
% 0.17/0.36  #    Propositional clauses after purity: 0
% 0.17/0.36  #    Propositional unsat core size     : 0
% 0.17/0.36  #    Propositional preprocessing time  : 0.000
% 0.17/0.36  #    Propositional encoding time       : 0.000
% 0.17/0.36  #    Propositional solver time         : 0.000
% 0.17/0.36  #    Success case prop preproc time    : 0.000
% 0.17/0.36  #    Success case prop encoding time   : 0.000
% 0.17/0.36  #    Success case prop solver time     : 0.000
% 0.17/0.36  # Current number of processed clauses  : 53
% 0.17/0.36  #    Positive orientable unit clauses  : 33
% 0.17/0.36  #    Positive unorientable unit clauses: 3
% 0.17/0.36  #    Negative unit clauses             : 0
% 0.17/0.36  #    Non-unit-clauses                  : 17
% 0.17/0.36  # Current number of unprocessed clauses: 487
% 0.17/0.36  # ...number of literals in the above   : 508
% 0.17/0.36  # Current number of archived formulas  : 0
% 0.17/0.36  # Current number of archived clauses   : 45
% 0.17/0.36  # Clause-clause subsumption calls (NU) : 42
% 0.17/0.36  # Rec. Clause-clause subsumption calls : 42
% 0.17/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.17/0.36  # Unit Clause-clause subsumption calls : 8
% 0.17/0.36  # Rewrite failures with RHS unbound    : 0
% 0.17/0.36  # BW rewrite match attempts            : 84
% 0.17/0.36  # BW rewrite match successes           : 48
% 0.17/0.36  # Condensation attempts                : 0
% 0.17/0.36  # Condensation successes               : 0
% 0.17/0.36  # Termbank termtop insertions          : 8741
% 0.17/0.36  
% 0.17/0.36  # -------------------------------------------------
% 0.17/0.36  # User time                : 0.039 s
% 0.17/0.36  # System time              : 0.002 s
% 0.17/0.36  # Total time               : 0.041 s
% 0.17/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
