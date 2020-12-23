%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:58 EST 2020

% Result     : Theorem 0.45s
% Output     : CNFRefutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   85 (1031 expanded)
%              Number of clauses        :   56 ( 478 expanded)
%              Number of leaves         :   14 ( 267 expanded)
%              Depth                    :   14
%              Number of atoms          :  124 (1449 expanded)
%              Number of equality atoms :   55 ( 850 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X4)
        & r1_xboole_0(X2,X4)
        & r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t87_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_xboole_0(X1,X4)
          & r1_xboole_0(X2,X4)
          & r1_xboole_0(X3,X4) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) ) ),
    inference(assume_negation,[status(cth)],[t114_xboole_1])).

fof(c_0_15,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X12,X13)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_16,plain,(
    ! [X32,X33] : k2_xboole_0(X32,X33) = k5_xboole_0(X32,k4_xboole_0(X33,X32)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_17,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_18,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_19,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_21,plain,(
    ! [X24,X25] :
      ( ( ~ r1_xboole_0(X24,X25)
        | k4_xboole_0(X24,X25) = X24 )
      & ( k4_xboole_0(X24,X25) != X24
        | r1_xboole_0(X24,X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_22,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0)
    & r1_xboole_0(esk2_0,esk4_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

fof(c_0_34,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_xboole_0(X26,X27)
      | k2_xboole_0(k4_xboole_0(X28,X26),X27) = k4_xboole_0(k2_xboole_0(X28,X27),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_36,plain,(
    ! [X22,X23] : r1_xboole_0(k4_xboole_0(X22,X23),k4_xboole_0(X23,X22)) ),
    inference(variable_rename,[status(thm)],[t82_xboole_1])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_35])).

fof(c_0_44,plain,(
    ! [X19,X20,X21] :
      ( ( r1_xboole_0(X19,k2_xboole_0(X20,X21))
        | ~ r1_xboole_0(X19,X20)
        | ~ r1_xboole_0(X19,X21) )
      & ( r1_xboole_0(X19,X20)
        | ~ r1_xboole_0(X19,k2_xboole_0(X20,X21)) )
      & ( r1_xboole_0(X19,X21)
        | ~ r1_xboole_0(X19,k2_xboole_0(X20,X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X1) = k5_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_24]),c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_43]),c_0_41])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk4_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,esk1_0),k4_xboole_0(esk4_0,k4_xboole_0(X1,esk1_0))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(esk4_0,X1)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

fof(c_0_57,plain,(
    ! [X16,X17,X18] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_51]),c_0_48])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk1_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_56]),c_0_41]),c_0_48])).

cnf(c_0_64,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_65,plain,(
    ! [X29,X30,X31] : k5_xboole_0(k5_xboole_0(X29,X30),X31) = k5_xboole_0(X29,k5_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(X1,k4_xboole_0(esk2_0,X1)))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_70,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(X1,k4_xboole_0(esk3_0,X1)))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_70]),c_0_73])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_45])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)),esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk3_0,k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_24]),c_0_24])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)),esk4_0),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)),esk4_0) = k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_76]),c_0_41]),c_0_48])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_70]),c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_82]),c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:59:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.45/0.63  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.45/0.63  # and selection function SelectComplexG.
% 0.45/0.63  #
% 0.45/0.63  # Preprocessing time       : 0.026 s
% 0.45/0.63  
% 0.45/0.63  # Proof found!
% 0.45/0.63  # SZS status Theorem
% 0.45/0.63  # SZS output start CNFRefutation
% 0.45/0.63  fof(t114_xboole_1, conjecture, ![X1, X2, X3, X4]:(((r1_xboole_0(X1,X4)&r1_xboole_0(X2,X4))&r1_xboole_0(X3,X4))=>r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_xboole_1)).
% 0.45/0.63  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.45/0.63  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.45/0.63  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.45/0.63  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.45/0.63  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.45/0.63  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.45/0.63  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.45/0.63  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.45/0.63  fof(t87_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 0.45/0.63  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 0.45/0.63  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.45/0.63  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.45/0.63  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.45/0.63  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_xboole_0(X1,X4)&r1_xboole_0(X2,X4))&r1_xboole_0(X3,X4))=>r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4))), inference(assume_negation,[status(cth)],[t114_xboole_1])).
% 0.45/0.63  fof(c_0_15, plain, ![X12, X13]:k4_xboole_0(X12,k2_xboole_0(X12,X13))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.45/0.63  fof(c_0_16, plain, ![X32, X33]:k2_xboole_0(X32,X33)=k5_xboole_0(X32,k4_xboole_0(X33,X32)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.45/0.63  fof(c_0_17, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.45/0.63  fof(c_0_18, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.45/0.63  fof(c_0_19, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.45/0.63  fof(c_0_20, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.45/0.63  fof(c_0_21, plain, ![X24, X25]:((~r1_xboole_0(X24,X25)|k4_xboole_0(X24,X25)=X24)&(k4_xboole_0(X24,X25)!=X24|r1_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.45/0.63  fof(c_0_22, negated_conjecture, (((r1_xboole_0(esk1_0,esk4_0)&r1_xboole_0(esk2_0,esk4_0))&r1_xboole_0(esk3_0,esk4_0))&~r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.45/0.63  cnf(c_0_23, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.45/0.63  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.45/0.63  cnf(c_0_25, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.45/0.63  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.45/0.63  fof(c_0_27, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.45/0.63  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.45/0.63  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.45/0.63  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.45/0.63  cnf(c_0_31, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.45/0.63  cnf(c_0_32, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.45/0.63  cnf(c_0_33, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.45/0.63  fof(c_0_34, plain, ![X26, X27, X28]:(~r1_xboole_0(X26,X27)|k2_xboole_0(k4_xboole_0(X28,X26),X27)=k4_xboole_0(k2_xboole_0(X28,X27),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).
% 0.45/0.63  cnf(c_0_35, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.45/0.63  fof(c_0_36, plain, ![X22, X23]:r1_xboole_0(k4_xboole_0(X22,X23),k4_xboole_0(X23,X22)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 0.45/0.63  cnf(c_0_37, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 0.45/0.63  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.45/0.63  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29])).
% 0.45/0.63  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk2_0,esk4_0)=esk2_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.45/0.63  cnf(c_0_41, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.45/0.63  cnf(c_0_42, plain, (k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.45/0.63  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_30, c_0_35])).
% 0.45/0.63  fof(c_0_44, plain, ![X19, X20, X21]:((r1_xboole_0(X19,k2_xboole_0(X20,X21))|~r1_xboole_0(X19,X20)|~r1_xboole_0(X19,X21))&((r1_xboole_0(X19,X20)|~r1_xboole_0(X19,k2_xboole_0(X20,X21)))&(r1_xboole_0(X19,X21)|~r1_xboole_0(X19,k2_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.45/0.63  cnf(c_0_45, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.45/0.63  cnf(c_0_46, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.45/0.63  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.45/0.63  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_33, c_0_41])).
% 0.45/0.63  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk1_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.45/0.63  cnf(c_0_50, plain, (k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X2,X3)),X1)=k5_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1)))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_24]), c_0_24])).
% 0.45/0.63  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_43]), c_0_41])).
% 0.45/0.63  cnf(c_0_52, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.45/0.63  cnf(c_0_53, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.45/0.63  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk4_0,esk2_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.45/0.63  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk1_0,esk4_0)=esk1_0), inference(spm,[status(thm)],[c_0_30, c_0_49])).
% 0.45/0.63  cnf(c_0_56, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,esk1_0),k4_xboole_0(esk4_0,k4_xboole_0(X1,esk1_0)))=k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(esk4_0,X1)),esk1_0)), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.45/0.63  fof(c_0_57, plain, ![X16, X17, X18]:k2_xboole_0(k2_xboole_0(X16,X17),X18)=k2_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.45/0.63  cnf(c_0_58, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_43])).
% 0.45/0.63  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_51]), c_0_48])).
% 0.45/0.63  cnf(c_0_60, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_24])).
% 0.45/0.63  cnf(c_0_61, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.45/0.63  cnf(c_0_62, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,esk1_0),esk1_0)), inference(spm,[status(thm)],[c_0_45, c_0_55])).
% 0.45/0.63  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk4_0,esk1_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_56]), c_0_41]), c_0_48])).
% 0.45/0.63  cnf(c_0_64, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.45/0.63  fof(c_0_65, plain, ![X29, X30, X31]:k5_xboole_0(k5_xboole_0(X29,X30),X31)=k5_xboole_0(X29,k5_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.45/0.63  cnf(c_0_66, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.45/0.63  cnf(c_0_67, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(X1,k4_xboole_0(esk2_0,X1)))|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.45/0.63  cnf(c_0_68, negated_conjecture, (r1_xboole_0(esk4_0,esk1_0)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.45/0.63  cnf(c_0_69, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.45/0.63  cnf(c_0_70, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.45/0.63  cnf(c_0_71, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(X1,k4_xboole_0(esk3_0,X1)))|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_66])).
% 0.45/0.63  cnf(c_0_72, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.45/0.63  cnf(c_0_73, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.45/0.63  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_70]), c_0_73])).
% 0.45/0.63  cnf(c_0_75, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_45])).
% 0.45/0.63  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)))=esk4_0), inference(spm,[status(thm)],[c_0_30, c_0_74])).
% 0.45/0.63  cnf(c_0_77, negated_conjecture, (~r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.45/0.63  cnf(c_0_78, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)),esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.45/0.63  cnf(c_0_79, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_46, c_0_39])).
% 0.45/0.63  cnf(c_0_80, negated_conjecture, (~r1_xboole_0(k5_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk3_0,k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_24]), c_0_24])).
% 0.45/0.63  cnf(c_0_81, negated_conjecture, (r1_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)),esk4_0),esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_78])).
% 0.45/0.63  cnf(c_0_82, negated_conjecture, (k4_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)),esk4_0)=k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_76]), c_0_41]), c_0_48])).
% 0.45/0.63  cnf(c_0_83, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_70]), c_0_73])).
% 0.45/0.63  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_82]), c_0_83]), ['proof']).
% 0.45/0.63  # SZS output end CNFRefutation
% 0.45/0.63  # Proof object total steps             : 85
% 0.45/0.63  # Proof object clause steps            : 56
% 0.45/0.63  # Proof object formula steps           : 29
% 0.45/0.63  # Proof object conjectures             : 33
% 0.45/0.63  # Proof object clause conjectures      : 30
% 0.45/0.63  # Proof object formula conjectures     : 3
% 0.45/0.63  # Proof object initial clauses used    : 17
% 0.45/0.63  # Proof object initial formulas used   : 14
% 0.45/0.63  # Proof object generating inferences   : 24
% 0.45/0.63  # Proof object simplifying inferences  : 34
% 0.45/0.63  # Training examples: 0 positive, 0 negative
% 0.45/0.63  # Parsed axioms                        : 14
% 0.45/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.45/0.63  # Initial clauses                      : 20
% 0.45/0.63  # Removed in clause preprocessing      : 2
% 0.45/0.63  # Initial clauses in saturation        : 18
% 0.45/0.63  # Processed clauses                    : 2378
% 0.45/0.63  # ...of these trivial                  : 410
% 0.45/0.63  # ...subsumed                          : 1111
% 0.45/0.63  # ...remaining for further processing  : 857
% 0.45/0.63  # Other redundant clauses eliminated   : 0
% 0.45/0.63  # Clauses deleted for lack of memory   : 0
% 0.45/0.63  # Backward-subsumed                    : 7
% 0.45/0.63  # Backward-rewritten                   : 258
% 0.45/0.63  # Generated clauses                    : 28175
% 0.45/0.63  # ...of the previous two non-trivial   : 16440
% 0.45/0.63  # Contextual simplify-reflections      : 0
% 0.45/0.63  # Paramodulations                      : 28172
% 0.45/0.63  # Factorizations                       : 0
% 0.45/0.63  # Equation resolutions                 : 3
% 0.45/0.63  # Propositional unsat checks           : 0
% 0.45/0.63  #    Propositional check models        : 0
% 0.45/0.63  #    Propositional check unsatisfiable : 0
% 0.45/0.63  #    Propositional clauses             : 0
% 0.45/0.63  #    Propositional clauses after purity: 0
% 0.45/0.63  #    Propositional unsat core size     : 0
% 0.45/0.63  #    Propositional preprocessing time  : 0.000
% 0.45/0.63  #    Propositional encoding time       : 0.000
% 0.45/0.63  #    Propositional solver time         : 0.000
% 0.45/0.63  #    Success case prop preproc time    : 0.000
% 0.45/0.63  #    Success case prop encoding time   : 0.000
% 0.45/0.63  #    Success case prop solver time     : 0.000
% 0.45/0.63  # Current number of processed clauses  : 592
% 0.45/0.63  #    Positive orientable unit clauses  : 395
% 0.45/0.63  #    Positive unorientable unit clauses: 2
% 0.45/0.63  #    Negative unit clauses             : 1
% 0.45/0.63  #    Non-unit-clauses                  : 194
% 0.45/0.63  # Current number of unprocessed clauses: 13000
% 0.45/0.63  # ...number of literals in the above   : 17575
% 0.45/0.63  # Current number of archived formulas  : 0
% 0.45/0.63  # Current number of archived clauses   : 267
% 0.45/0.63  # Clause-clause subsumption calls (NU) : 11100
% 0.45/0.63  # Rec. Clause-clause subsumption calls : 11001
% 0.45/0.63  # Non-unit clause-clause subsumptions  : 1118
% 0.45/0.63  # Unit Clause-clause subsumption calls : 663
% 0.45/0.63  # Rewrite failures with RHS unbound    : 0
% 0.45/0.63  # BW rewrite match attempts            : 702
% 0.45/0.63  # BW rewrite match successes           : 115
% 0.45/0.63  # Condensation attempts                : 0
% 0.45/0.63  # Condensation successes               : 0
% 0.45/0.63  # Termbank termtop insertions          : 595468
% 0.48/0.63  
% 0.48/0.63  # -------------------------------------------------
% 0.48/0.63  # User time                : 0.274 s
% 0.48/0.63  # System time              : 0.014 s
% 0.48/0.63  # Total time               : 0.288 s
% 0.48/0.63  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
