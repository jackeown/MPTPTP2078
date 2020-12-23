%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:08 EST 2020

% Result     : Theorem 4.29s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 604 expanded)
%              Number of clauses        :   69 ( 267 expanded)
%              Number of leaves         :   11 ( 162 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 986 expanded)
%              Number of equality atoms :   94 ( 708 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_12,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_14,plain,(
    ! [X20,X21,X22,X23] : k2_zfmisc_1(k3_xboole_0(X20,X21),k3_xboole_0(X22,X23)) = k3_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_19,plain,(
    ! [X12,X13,X14] : k3_xboole_0(k3_xboole_0(X12,X13),X14) = k3_xboole_0(X12,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_20,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_21,plain,(
    ! [X24,X25,X26] :
      ( k2_zfmisc_1(k4_xboole_0(X24,X25),X26) = k4_xboole_0(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X26))
      & k2_zfmisc_1(X26,k4_xboole_0(X24,X25)) = k4_xboole_0(k2_zfmisc_1(X26,X24),k2_zfmisc_1(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    & k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0
    & ( ~ r1_tarski(esk1_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X17] : k5_xboole_0(X17,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_17]),c_0_17])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_17]),c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_41,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_17])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_23]),c_0_28])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2)) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_23]),c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_23])).

cnf(c_0_54,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k3_xboole_0(X4,X5)))
    | k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X4,k3_xboole_0(X5,X2)))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,k3_xboole_0(esk4_0,X1)))) = k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k5_xboole_0(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk2_0,k3_xboole_0(esk4_0,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_27]),c_0_27])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_28]),c_0_36]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_22])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_62,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X4)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X3,X4),X5))
    | k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X3,k3_xboole_0(X4,X1)),k3_xboole_0(X2,X5))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(k3_xboole_0(esk1_0,k3_xboole_0(esk3_0,X1)),k3_xboole_0(esk2_0,esk4_0))) = k2_zfmisc_1(k5_xboole_0(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk1_0,k3_xboole_0(esk3_0,X1))),k3_xboole_0(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_40]),c_0_27]),c_0_27])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_28]),c_0_36]),c_0_36])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_22]),c_0_47])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k3_xboole_0(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_26]),c_0_35]),c_0_36]),c_0_56])])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) = k1_xboole_0
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_57]),c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_40])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3))
    | ~ r1_tarski(X1,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_22]),c_0_46])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_26]),c_0_35]),c_0_36]),c_0_65])])).

cnf(c_0_75,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0) = k1_xboole_0
    | ~ r1_tarski(esk2_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_68]),c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_70]),c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)),k2_zfmisc_1(esk1_0,esk2_0)) = k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),k3_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_40])).

cnf(c_0_79,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_72]),c_0_28])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_26])).

cnf(c_0_81,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) = k1_xboole_0
    | ~ r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0
    | ~ r1_tarski(esk2_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_75]),c_0_61])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_76]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_36])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_40]),c_0_49])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,X2) != k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0
    | ~ r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_81]),c_0_69])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_82]),c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_84]),c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_42])]),c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_89]),c_0_42])]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:59:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 4.29/4.44  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 4.29/4.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.29/4.44  #
% 4.29/4.44  # Preprocessing time       : 0.032 s
% 4.29/4.44  # Presaturation interreduction done
% 4.29/4.44  
% 4.29/4.44  # Proof found!
% 4.29/4.44  # SZS status Theorem
% 4.29/4.44  # SZS output start CNFRefutation
% 4.29/4.44  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.29/4.44  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.29/4.44  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.29/4.44  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 4.29/4.44  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 4.29/4.44  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.29/4.44  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.29/4.44  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.29/4.44  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 4.29/4.44  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.29/4.44  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.29/4.44  fof(c_0_11, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 4.29/4.44  fof(c_0_12, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 4.29/4.44  fof(c_0_13, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 4.29/4.44  fof(c_0_14, plain, ![X20, X21, X22, X23]:k2_zfmisc_1(k3_xboole_0(X20,X21),k3_xboole_0(X22,X23))=k3_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 4.29/4.44  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 4.29/4.44  cnf(c_0_16, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 4.29/4.44  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.29/4.44  fof(c_0_18, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 4.29/4.44  fof(c_0_19, plain, ![X12, X13, X14]:k3_xboole_0(k3_xboole_0(X12,X13),X14)=k3_xboole_0(X12,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 4.29/4.44  fof(c_0_20, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 4.29/4.44  fof(c_0_21, plain, ![X24, X25, X26]:(k2_zfmisc_1(k4_xboole_0(X24,X25),X26)=k4_xboole_0(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X26))&k2_zfmisc_1(X26,k4_xboole_0(X24,X25))=k4_xboole_0(k2_zfmisc_1(X26,X24),k2_zfmisc_1(X26,X25))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 4.29/4.44  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.29/4.44  cnf(c_0_23, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.29/4.44  fof(c_0_24, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))&(k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0&(~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 4.29/4.44  cnf(c_0_25, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 4.29/4.44  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.29/4.44  cnf(c_0_27, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.29/4.44  cnf(c_0_28, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.29/4.44  fof(c_0_29, plain, ![X17]:k5_xboole_0(X17,X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 4.29/4.44  cnf(c_0_30, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.29/4.44  cnf(c_0_31, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.29/4.44  cnf(c_0_32, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 4.29/4.44  cnf(c_0_33, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.29/4.44  cnf(c_0_34, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 4.29/4.44  cnf(c_0_35, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 4.29/4.44  cnf(c_0_36, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.29/4.44  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 4.29/4.44  cnf(c_0_38, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_17]), c_0_17])).
% 4.29/4.44  cnf(c_0_39, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_17]), c_0_17])).
% 4.29/4.44  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 4.29/4.44  fof(c_0_41, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 4.29/4.44  cnf(c_0_42, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 4.29/4.44  cnf(c_0_43, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_17])).
% 4.29/4.44  cnf(c_0_44, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 4.29/4.44  cnf(c_0_45, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 4.29/4.44  cnf(c_0_46, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_23]), c_0_28])).
% 4.29/4.44  cnf(c_0_47, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_23]), c_0_28])).
% 4.29/4.44  cnf(c_0_48, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_22])).
% 4.29/4.44  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.29/4.44  cnf(c_0_50, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.29/4.44  cnf(c_0_51, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 4.29/4.44  cnf(c_0_52, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_26])).
% 4.29/4.44  cnf(c_0_53, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(spm,[status(thm)],[c_0_43, c_0_23])).
% 4.29/4.44  cnf(c_0_54, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k3_xboole_0(X4,X5)))|k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X4,k3_xboole_0(X5,X2))))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 4.29/4.44  cnf(c_0_55, negated_conjecture, (k5_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,k3_xboole_0(esk4_0,X1))))=k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k5_xboole_0(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk2_0,k3_xboole_0(esk4_0,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_27]), c_0_27])).
% 4.29/4.44  cnf(c_0_56, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_28]), c_0_36]), c_0_36])).
% 4.29/4.44  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_22])).
% 4.29/4.44  cnf(c_0_58, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.29/4.44  cnf(c_0_59, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.29/4.44  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0)=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_36])).
% 4.29/4.44  cnf(c_0_61, negated_conjecture, (esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 4.29/4.44  cnf(c_0_62, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X4))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 4.29/4.44  cnf(c_0_63, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X3,X4),X5))|k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X3,k3_xboole_0(X4,X1)),k3_xboole_0(X2,X5)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 4.29/4.44  cnf(c_0_64, negated_conjecture, (k5_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(k3_xboole_0(esk1_0,k3_xboole_0(esk3_0,X1)),k3_xboole_0(esk2_0,esk4_0)))=k2_zfmisc_1(k5_xboole_0(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk1_0,k3_xboole_0(esk3_0,X1))),k3_xboole_0(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_40]), c_0_27]), c_0_27])).
% 4.29/4.44  cnf(c_0_65, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_28]), c_0_36]), c_0_36])).
% 4.29/4.44  cnf(c_0_66, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_tarski(X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_22]), c_0_47])).
% 4.29/4.44  cnf(c_0_67, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k3_xboole_0(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_26]), c_0_35]), c_0_36]), c_0_56])])).
% 4.29/4.44  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))=k1_xboole_0|~r1_tarski(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_57]), c_0_36])).
% 4.29/4.44  cnf(c_0_69, negated_conjecture, (esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_58])).
% 4.29/4.44  cnf(c_0_70, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 4.29/4.44  cnf(c_0_71, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.29/4.44  cnf(c_0_72, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_62, c_0_40])).
% 4.29/4.44  cnf(c_0_73, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3))|~r1_tarski(X1,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_22]), c_0_46])).
% 4.29/4.44  cnf(c_0_74, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_26]), c_0_35]), c_0_36]), c_0_65])])).
% 4.29/4.44  cnf(c_0_75, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0)=k1_xboole_0|~r1_tarski(esk2_0,k3_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 4.29/4.44  cnf(c_0_76, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0|~r1_tarski(esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_68]), c_0_69])).
% 4.29/4.44  cnf(c_0_77, negated_conjecture, (~r1_tarski(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_70]), c_0_71])).
% 4.29/4.44  cnf(c_0_78, negated_conjecture, (k5_xboole_0(k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)),k2_zfmisc_1(esk1_0,esk2_0))=k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),k3_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_40])).
% 4.29/4.44  cnf(c_0_79, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_72]), c_0_28])).
% 4.29/4.44  cnf(c_0_80, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_26])).
% 4.29/4.44  cnf(c_0_81, negated_conjecture, (k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))=k1_xboole_0|~r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 4.29/4.44  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0|~r1_tarski(esk2_0,k3_xboole_0(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_75]), c_0_61])).
% 4.29/4.44  cnf(c_0_83, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_76]), c_0_77])).
% 4.29/4.44  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79]), c_0_36])).
% 4.29/4.44  cnf(c_0_85, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_40]), c_0_49])).
% 4.29/4.44  cnf(c_0_86, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,X2)!=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_80])).
% 4.29/4.44  cnf(c_0_87, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0|~r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_81]), c_0_69])).
% 4.29/4.44  cnf(c_0_88, negated_conjecture, (~r1_tarski(esk2_0,k3_xboole_0(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_82]), c_0_83])).
% 4.29/4.44  cnf(c_0_89, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_84]), c_0_85])).
% 4.29/4.44  cnf(c_0_90, negated_conjecture, (~r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_42])]), c_0_88])).
% 4.29/4.44  cnf(c_0_91, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_89]), c_0_42])]), c_0_90]), ['proof']).
% 4.29/4.44  # SZS output end CNFRefutation
% 4.29/4.44  # Proof object total steps             : 92
% 4.29/4.44  # Proof object clause steps            : 69
% 4.29/4.44  # Proof object formula steps           : 23
% 4.29/4.44  # Proof object conjectures             : 34
% 4.29/4.44  # Proof object clause conjectures      : 31
% 4.29/4.44  # Proof object formula conjectures     : 3
% 4.29/4.44  # Proof object initial clauses used    : 17
% 4.29/4.44  # Proof object initial formulas used   : 11
% 4.29/4.44  # Proof object generating inferences   : 45
% 4.29/4.44  # Proof object simplifying inferences  : 52
% 4.29/4.44  # Training examples: 0 positive, 0 negative
% 4.29/4.44  # Parsed axioms                        : 11
% 4.29/4.44  # Removed by relevancy pruning/SinE    : 0
% 4.29/4.44  # Initial clauses                      : 17
% 4.29/4.44  # Removed in clause preprocessing      : 1
% 4.29/4.44  # Initial clauses in saturation        : 16
% 4.29/4.44  # Processed clauses                    : 22568
% 4.29/4.44  # ...of these trivial                  : 472
% 4.29/4.44  # ...subsumed                          : 19995
% 4.29/4.44  # ...remaining for further processing  : 2101
% 4.29/4.44  # Other redundant clauses eliminated   : 10
% 4.29/4.44  # Clauses deleted for lack of memory   : 0
% 4.29/4.44  # Backward-subsumed                    : 120
% 4.29/4.44  # Backward-rewritten                   : 323
% 4.29/4.44  # Generated clauses                    : 562667
% 4.29/4.44  # ...of the previous two non-trivial   : 531905
% 4.29/4.44  # Contextual simplify-reflections      : 48
% 4.29/4.44  # Paramodulations                      : 562614
% 4.29/4.44  # Factorizations                       : 3
% 4.29/4.44  # Equation resolutions                 : 50
% 4.29/4.44  # Propositional unsat checks           : 0
% 4.29/4.44  #    Propositional check models        : 0
% 4.29/4.44  #    Propositional check unsatisfiable : 0
% 4.29/4.44  #    Propositional clauses             : 0
% 4.29/4.44  #    Propositional clauses after purity: 0
% 4.29/4.44  #    Propositional unsat core size     : 0
% 4.29/4.44  #    Propositional preprocessing time  : 0.000
% 4.29/4.44  #    Propositional encoding time       : 0.000
% 4.29/4.44  #    Propositional solver time         : 0.000
% 4.29/4.44  #    Success case prop preproc time    : 0.000
% 4.29/4.44  #    Success case prop encoding time   : 0.000
% 4.29/4.44  #    Success case prop solver time     : 0.000
% 4.29/4.44  # Current number of processed clauses  : 1642
% 4.29/4.44  #    Positive orientable unit clauses  : 144
% 4.29/4.44  #    Positive unorientable unit clauses: 15
% 4.29/4.44  #    Negative unit clauses             : 33
% 4.29/4.44  #    Non-unit-clauses                  : 1450
% 4.29/4.44  # Current number of unprocessed clauses: 505876
% 4.29/4.44  # ...number of literals in the above   : 1515356
% 4.29/4.44  # Current number of archived formulas  : 0
% 4.29/4.44  # Current number of archived clauses   : 460
% 4.29/4.44  # Clause-clause subsumption calls (NU) : 435029
% 4.29/4.44  # Rec. Clause-clause subsumption calls : 296365
% 4.29/4.44  # Non-unit clause-clause subsumptions  : 9767
% 4.29/4.44  # Unit Clause-clause subsumption calls : 2156
% 4.29/4.44  # Rewrite failures with RHS unbound    : 0
% 4.29/4.44  # BW rewrite match attempts            : 1582
% 4.29/4.44  # BW rewrite match successes           : 321
% 4.29/4.44  # Condensation attempts                : 0
% 4.29/4.44  # Condensation successes               : 0
% 4.29/4.44  # Termbank termtop insertions          : 9704497
% 4.29/4.46  
% 4.29/4.46  # -------------------------------------------------
% 4.29/4.46  # User time                : 3.899 s
% 4.29/4.46  # System time              : 0.228 s
% 4.29/4.46  # Total time               : 4.126 s
% 4.29/4.46  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
