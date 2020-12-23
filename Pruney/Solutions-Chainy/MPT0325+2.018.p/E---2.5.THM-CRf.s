%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 234 expanded)
%              Number of clauses        :   44 ( 103 expanded)
%              Number of leaves         :   11 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 445 expanded)
%              Number of equality atoms :   69 ( 284 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

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

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

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
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | r1_tarski(k3_xboole_0(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

fof(c_0_12,plain,(
    ! [X20,X21,X22,X23] : k2_zfmisc_1(k3_xboole_0(X20,X21),k3_xboole_0(X22,X23)) = k3_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    & k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0
    & ( ~ r1_tarski(esk1_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_21,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X24,X25,X26] :
      ( k2_zfmisc_1(k4_xboole_0(X24,X25),X26) = k4_xboole_0(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X26))
      & k2_zfmisc_1(X26,k4_xboole_0(X24,X25)) = k4_xboole_0(k2_zfmisc_1(X26,X24),k2_zfmisc_1(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),X5)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),X5) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_30,plain,(
    ! [X17] : k5_xboole_0(X17,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),X5)
    | ~ r1_tarski(k2_zfmisc_1(X1,X4),X5) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_28]),c_0_28])).

fof(c_0_39,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_28]),c_0_28])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2)) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_16]),c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_16]),c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_18])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)),k2_zfmisc_1(esk1_0,esk2_0)) = k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),k3_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_47]),c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) = k1_xboole_0
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_33]),c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_56]),c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_58]),c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_60]),c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_62]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:34:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.19/0.51  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.027 s
% 0.19/0.51  # Presaturation interreduction done
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.19/0.51  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.19/0.51  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.51  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.19/0.51  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.51  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.51  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.51  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 0.19/0.51  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.51  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.51  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.51  fof(c_0_11, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|r1_tarski(k3_xboole_0(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.19/0.51  fof(c_0_12, plain, ![X20, X21, X22, X23]:k2_zfmisc_1(k3_xboole_0(X20,X21),k3_xboole_0(X22,X23))=k3_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.19/0.51  fof(c_0_13, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.51  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.19/0.51  cnf(c_0_15, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_16, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.51  fof(c_0_17, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.51  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.51  fof(c_0_19, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))&(k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0&(~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.51  fof(c_0_20, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.51  fof(c_0_21, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.51  fof(c_0_22, plain, ![X24, X25, X26]:(k2_zfmisc_1(k4_xboole_0(X24,X25),X26)=k4_xboole_0(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X26))&k2_zfmisc_1(X26,k4_xboole_0(X24,X25))=k4_xboole_0(k2_zfmisc_1(X26,X24),k2_zfmisc_1(X26,X25))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 0.19/0.51  cnf(c_0_23, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),X5)|~r1_tarski(k2_zfmisc_1(X1,X3),X5)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.51  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_25, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.19/0.51  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.51  cnf(c_0_27, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.51  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.51  fof(c_0_29, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.51  fof(c_0_30, plain, ![X17]:k5_xboole_0(X17,X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.51  cnf(c_0_31, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_32, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),X5)|~r1_tarski(k2_zfmisc_1(X1,X4),X5)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.51  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.51  cnf(c_0_34, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.51  cnf(c_0_35, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.51  cnf(c_0_36, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.51  cnf(c_0_37, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_38, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_28]), c_0_28])).
% 0.19/0.51  fof(c_0_39, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.51  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),X1)|~r1_tarski(k2_zfmisc_1(esk1_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.51  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.19/0.51  cnf(c_0_42, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_28]), c_0_28])).
% 0.19/0.51  cnf(c_0_43, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_16]), c_0_35])).
% 0.19/0.51  cnf(c_0_44, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_18])).
% 0.19/0.51  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.51  cnf(c_0_46, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.51  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.51  cnf(c_0_48, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_16]), c_0_35])).
% 0.19/0.51  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_18])).
% 0.19/0.51  cnf(c_0_50, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.51  cnf(c_0_51, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.51  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0)=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_36])).
% 0.19/0.51  cnf(c_0_53, negated_conjecture, (esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.51  cnf(c_0_54, negated_conjecture, (k5_xboole_0(k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)),k2_zfmisc_1(esk1_0,esk2_0))=k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),k3_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_33])).
% 0.19/0.51  cnf(c_0_55, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_47]), c_0_35])).
% 0.19/0.51  cnf(c_0_56, negated_conjecture, (k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))=k1_xboole_0|~r1_tarski(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_36])).
% 0.19/0.51  cnf(c_0_57, negated_conjecture, (esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_50])).
% 0.19/0.51  cnf(c_0_58, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.19/0.51  cnf(c_0_59, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.51  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_36])).
% 0.19/0.51  cnf(c_0_61, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_33]), c_0_45])).
% 0.19/0.51  cnf(c_0_62, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0|~r1_tarski(esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_56]), c_0_57])).
% 0.19/0.51  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_58]), c_0_59])).
% 0.19/0.51  cnf(c_0_64, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_60]), c_0_61])).
% 0.19/0.51  cnf(c_0_65, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_62]), c_0_63])).
% 0.19/0.51  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_64]), c_0_65]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 67
% 0.19/0.51  # Proof object clause steps            : 44
% 0.19/0.51  # Proof object formula steps           : 23
% 0.19/0.51  # Proof object conjectures             : 25
% 0.19/0.51  # Proof object clause conjectures      : 22
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 16
% 0.19/0.51  # Proof object initial formulas used   : 11
% 0.19/0.51  # Proof object generating inferences   : 22
% 0.19/0.51  # Proof object simplifying inferences  : 23
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 11
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 17
% 0.19/0.51  # Removed in clause preprocessing      : 1
% 0.19/0.51  # Initial clauses in saturation        : 16
% 0.19/0.51  # Processed clauses                    : 1800
% 0.19/0.51  # ...of these trivial                  : 24
% 0.19/0.51  # ...subsumed                          : 1406
% 0.19/0.51  # ...remaining for further processing  : 370
% 0.19/0.51  # Other redundant clauses eliminated   : 9
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 52
% 0.19/0.51  # Backward-rewritten                   : 82
% 0.19/0.51  # Generated clauses                    : 11677
% 0.19/0.51  # ...of the previous two non-trivial   : 9708
% 0.19/0.51  # Contextual simplify-reflections      : 4
% 0.19/0.51  # Paramodulations                      : 11656
% 0.19/0.51  # Factorizations                       : 3
% 0.19/0.51  # Equation resolutions                 : 18
% 0.19/0.51  # Propositional unsat checks           : 0
% 0.19/0.51  #    Propositional check models        : 0
% 0.19/0.51  #    Propositional check unsatisfiable : 0
% 0.19/0.51  #    Propositional clauses             : 0
% 0.19/0.51  #    Propositional clauses after purity: 0
% 0.19/0.51  #    Propositional unsat core size     : 0
% 0.19/0.51  #    Propositional preprocessing time  : 0.000
% 0.19/0.51  #    Propositional encoding time       : 0.000
% 0.19/0.51  #    Propositional solver time         : 0.000
% 0.19/0.51  #    Success case prop preproc time    : 0.000
% 0.19/0.51  #    Success case prop encoding time   : 0.000
% 0.19/0.51  #    Success case prop solver time     : 0.000
% 0.19/0.51  # Current number of processed clauses  : 220
% 0.19/0.51  #    Positive orientable unit clauses  : 25
% 0.19/0.51  #    Positive unorientable unit clauses: 1
% 0.19/0.51  #    Negative unit clauses             : 14
% 0.19/0.51  #    Non-unit-clauses                  : 180
% 0.19/0.51  # Current number of unprocessed clauses: 7693
% 0.19/0.51  # ...number of literals in the above   : 23143
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 151
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 7949
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 6703
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 540
% 0.19/0.51  # Unit Clause-clause subsumption calls : 246
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 65
% 0.19/0.51  # BW rewrite match successes           : 46
% 0.19/0.51  # Condensation attempts                : 0
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 151052
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.174 s
% 0.19/0.51  # System time              : 0.006 s
% 0.19/0.51  # Total time               : 0.180 s
% 0.19/0.51  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
