%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:53 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 646 expanded)
%              Number of clauses        :   61 ( 285 expanded)
%              Number of leaves         :   13 ( 178 expanded)
%              Depth                    :   21
%              Number of atoms          :  158 ( 898 expanded)
%              Number of equality atoms :   68 ( 552 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t70_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_13,plain,(
    ! [X21,X22] : k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22)) = X21 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_14,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X12] : k2_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_16,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k4_xboole_0(X14,X13)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_20,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_22]),c_0_24]),c_0_22])).

fof(c_0_28,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_29,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_30,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_18]),c_0_18])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

fof(c_0_37,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_xboole_0(X24,X25)
      | r1_xboole_0(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_38,plain,(
    ! [X26,X27] : r1_tarski(X26,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_24])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_18])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_33])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X1,X2))
    | k2_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | k2_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | k2_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_22])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_27])).

fof(c_0_53,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_35])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_40]),c_0_21]),c_0_22]),c_0_27])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,X2) = X1
    | X2 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_52]),c_0_21])).

fof(c_0_57,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_58,negated_conjecture,
    ( ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) )
    & ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | r1_xboole_0(esk1_0,esk2_0) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_xboole_0(esk1_0,esk2_0) )
    & ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | r1_xboole_0(esk1_0,esk3_0) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_53])])])])])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_22]),c_0_27])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_31]),c_0_22]),c_0_27])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,X2) = X2
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_56])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk1_0)
    | r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk1_0)
    | r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_64])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,X2) = X1
    | k4_xboole_0(X2,X3) != k1_xboole_0
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_69]),c_0_62])).

cnf(c_0_73,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_35]),c_0_35])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk3_0,X1) = esk3_0
    | k4_xboole_0(X1,esk1_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0)
    | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_72])).

cnf(c_0_78,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_24]),c_0_41])])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k4_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_55])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk1_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_36])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_71])).

cnf(c_0_83,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X2))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_80]),c_0_36]),c_0_21])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(X1,esk3_0))
    | ~ r1_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 2.22/2.39  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 2.22/2.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 2.22/2.39  #
% 2.22/2.39  # Preprocessing time       : 0.026 s
% 2.22/2.39  # Presaturation interreduction done
% 2.22/2.39  
% 2.22/2.39  # Proof found!
% 2.22/2.39  # SZS status Theorem
% 2.22/2.39  # SZS output start CNFRefutation
% 2.22/2.39  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.22/2.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.22/2.39  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.22/2.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.22/2.39  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.22/2.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.22/2.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.22/2.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.22/2.39  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.22/2.39  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.22/2.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.22/2.39  fof(t70_xboole_1, conjecture, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.22/2.39  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.22/2.39  fof(c_0_13, plain, ![X21, X22]:k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))=X21, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 2.22/2.39  fof(c_0_14, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.22/2.39  fof(c_0_15, plain, ![X12]:k2_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t1_boole])).
% 2.22/2.39  fof(c_0_16, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.22/2.39  cnf(c_0_17, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.22/2.39  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.22/2.39  fof(c_0_19, plain, ![X13, X14]:k2_xboole_0(X13,k4_xboole_0(X14,X13))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 2.22/2.39  fof(c_0_20, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.22/2.39  cnf(c_0_21, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.22/2.39  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.22/2.39  cnf(c_0_23, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 2.22/2.39  cnf(c_0_24, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.22/2.39  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.22/2.39  cnf(c_0_26, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 2.22/2.39  cnf(c_0_27, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_22]), c_0_24]), c_0_22])).
% 2.22/2.39  fof(c_0_28, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.22/2.39  fof(c_0_29, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 2.22/2.39  fof(c_0_30, plain, ![X16, X17, X18]:k4_xboole_0(k4_xboole_0(X16,X17),X18)=k4_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 2.22/2.39  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_18]), c_0_18])).
% 2.22/2.39  cnf(c_0_32, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 2.22/2.39  cnf(c_0_33, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.22/2.39  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.22/2.39  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.22/2.39  cnf(c_0_36, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 2.22/2.39  fof(c_0_37, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_xboole_0(X24,X25)|r1_xboole_0(X23,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 2.22/2.39  fof(c_0_38, plain, ![X26, X27]:r1_tarski(X26,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 2.22/2.39  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.22/2.39  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_18])).
% 2.22/2.39  cnf(c_0_41, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_24])).
% 2.22/2.39  cnf(c_0_42, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.22/2.39  cnf(c_0_43, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.22/2.39  cnf(c_0_44, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_39, c_0_18])).
% 2.22/2.39  cnf(c_0_45, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_33])).
% 2.22/2.39  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 2.22/2.39  cnf(c_0_47, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_33])).
% 2.22/2.39  cnf(c_0_48, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_45, c_0_22])).
% 2.22/2.39  cnf(c_0_49, plain, (r1_xboole_0(X1,k2_xboole_0(X1,X2))|k2_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 2.22/2.39  cnf(c_0_50, plain, (X1=k1_xboole_0|k2_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 2.22/2.39  cnf(c_0_51, plain, (X1=k1_xboole_0|k2_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_22])).
% 2.22/2.39  cnf(c_0_52, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_27])).
% 2.22/2.39  fof(c_0_53, negated_conjecture, ~(![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t70_xboole_1])).
% 2.22/2.39  cnf(c_0_54, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_35])).
% 2.22/2.39  cnf(c_0_55, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_40]), c_0_21]), c_0_22]), c_0_27])).
% 2.22/2.39  cnf(c_0_56, plain, (k2_xboole_0(X1,X2)=X1|X2!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_52]), c_0_21])).
% 2.22/2.39  fof(c_0_57, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|r1_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 2.22/2.39  fof(c_0_58, negated_conjecture, ((((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))))&((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|r1_xboole_0(esk1_0,esk2_0))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk2_0))))&((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|r1_xboole_0(esk1_0,esk3_0))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk3_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_53])])])])])).
% 2.22/2.39  cnf(c_0_59, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_22]), c_0_27])).
% 2.22/2.39  cnf(c_0_60, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_31]), c_0_22]), c_0_27])).
% 2.22/2.39  cnf(c_0_61, plain, (k2_xboole_0(X1,X2)=X2|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_56])).
% 2.22/2.39  cnf(c_0_62, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 2.22/2.39  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.22/2.39  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.22/2.39  cnf(c_0_65, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 2.22/2.39  cnf(c_0_66, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 2.22/2.39  cnf(c_0_67, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_46, c_0_22])).
% 2.22/2.39  cnf(c_0_68, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk1_0)|r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 2.22/2.39  cnf(c_0_69, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk1_0)|r1_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_64])).
% 2.22/2.39  cnf(c_0_70, plain, (k4_xboole_0(X1,X2)=X1|k4_xboole_0(X2,X3)!=k1_xboole_0|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 2.22/2.39  cnf(c_0_71, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_62])).
% 2.22/2.39  cnf(c_0_72, negated_conjecture, (r1_xboole_0(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_69]), c_0_62])).
% 2.22/2.39  cnf(c_0_73, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_35]), c_0_35])).
% 2.22/2.39  cnf(c_0_74, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_24, c_0_27])).
% 2.22/2.39  cnf(c_0_75, negated_conjecture, (k4_xboole_0(esk3_0,X1)=esk3_0|k4_xboole_0(X1,esk1_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 2.22/2.39  cnf(c_0_76, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.22/2.39  cnf(c_0_77, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_72])).
% 2.22/2.39  cnf(c_0_78, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_24]), c_0_41])])).
% 2.22/2.39  cnf(c_0_79, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k4_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_55])).
% 2.22/2.39  cnf(c_0_80, negated_conjecture, (k4_xboole_0(esk3_0,esk1_0)=esk3_0), inference(spm,[status(thm)],[c_0_75, c_0_36])).
% 2.22/2.39  cnf(c_0_81, negated_conjecture, (~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 2.22/2.39  cnf(c_0_82, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_62, c_0_71])).
% 2.22/2.39  cnf(c_0_83, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X2))|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 2.22/2.39  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_80]), c_0_36]), c_0_21])).
% 2.22/2.39  cnf(c_0_85, negated_conjecture, (~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 2.22/2.39  cnf(c_0_86, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(X1,esk3_0))|~r1_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 2.22/2.39  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_77])]), ['proof']).
% 2.22/2.39  # SZS output end CNFRefutation
% 2.22/2.39  # Proof object total steps             : 88
% 2.22/2.39  # Proof object clause steps            : 61
% 2.22/2.39  # Proof object formula steps           : 27
% 2.22/2.39  # Proof object conjectures             : 19
% 2.22/2.39  # Proof object clause conjectures      : 16
% 2.22/2.39  # Proof object formula conjectures     : 3
% 2.22/2.39  # Proof object initial clauses used    : 16
% 2.22/2.39  # Proof object initial formulas used   : 13
% 2.22/2.39  # Proof object generating inferences   : 38
% 2.22/2.39  # Proof object simplifying inferences  : 34
% 2.22/2.39  # Training examples: 0 positive, 0 negative
% 2.22/2.39  # Parsed axioms                        : 13
% 2.22/2.39  # Removed by relevancy pruning/SinE    : 0
% 2.22/2.39  # Initial clauses                      : 19
% 2.22/2.39  # Removed in clause preprocessing      : 4
% 2.22/2.39  # Initial clauses in saturation        : 15
% 2.22/2.39  # Processed clauses                    : 16117
% 2.22/2.39  # ...of these trivial                  : 331
% 2.22/2.39  # ...subsumed                          : 14532
% 2.22/2.39  # ...remaining for further processing  : 1254
% 2.22/2.39  # Other redundant clauses eliminated   : 0
% 2.22/2.39  # Clauses deleted for lack of memory   : 0
% 2.22/2.39  # Backward-subsumed                    : 59
% 2.22/2.39  # Backward-rewritten                   : 151
% 2.22/2.39  # Generated clauses                    : 272559
% 2.22/2.39  # ...of the previous two non-trivial   : 243137
% 2.22/2.39  # Contextual simplify-reflections      : 30
% 2.22/2.39  # Paramodulations                      : 272556
% 2.22/2.39  # Factorizations                       : 0
% 2.22/2.39  # Equation resolutions                 : 3
% 2.22/2.39  # Propositional unsat checks           : 0
% 2.22/2.39  #    Propositional check models        : 0
% 2.22/2.39  #    Propositional check unsatisfiable : 0
% 2.22/2.39  #    Propositional clauses             : 0
% 2.22/2.39  #    Propositional clauses after purity: 0
% 2.22/2.39  #    Propositional unsat core size     : 0
% 2.22/2.39  #    Propositional preprocessing time  : 0.000
% 2.22/2.39  #    Propositional encoding time       : 0.000
% 2.22/2.39  #    Propositional solver time         : 0.000
% 2.22/2.39  #    Success case prop preproc time    : 0.000
% 2.22/2.39  #    Success case prop encoding time   : 0.000
% 2.22/2.39  #    Success case prop solver time     : 0.000
% 2.22/2.39  # Current number of processed clauses  : 1029
% 2.22/2.39  #    Positive orientable unit clauses  : 117
% 2.22/2.39  #    Positive unorientable unit clauses: 8
% 2.22/2.39  #    Negative unit clauses             : 58
% 2.22/2.39  #    Non-unit-clauses                  : 846
% 2.22/2.39  # Current number of unprocessed clauses: 225919
% 2.22/2.39  # ...number of literals in the above   : 617676
% 2.22/2.39  # Current number of archived formulas  : 0
% 2.22/2.39  # Current number of archived clauses   : 226
% 2.22/2.39  # Clause-clause subsumption calls (NU) : 446274
% 2.22/2.39  # Rec. Clause-clause subsumption calls : 391961
% 2.22/2.39  # Non-unit clause-clause subsumptions  : 12283
% 2.22/2.39  # Unit Clause-clause subsumption calls : 861
% 2.22/2.39  # Rewrite failures with RHS unbound    : 0
% 2.22/2.39  # BW rewrite match attempts            : 793
% 2.22/2.39  # BW rewrite match successes           : 175
% 2.22/2.39  # Condensation attempts                : 0
% 2.22/2.39  # Condensation successes               : 0
% 2.22/2.39  # Termbank termtop insertions          : 3323031
% 2.22/2.40  
% 2.22/2.40  # -------------------------------------------------
% 2.22/2.40  # User time                : 1.942 s
% 2.22/2.40  # System time              : 0.101 s
% 2.22/2.40  # Total time               : 2.043 s
% 2.22/2.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
