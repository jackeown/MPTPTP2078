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
% DateTime   : Thu Dec  3 10:44:06 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 202 expanded)
%              Number of clauses        :   46 (  89 expanded)
%              Number of leaves         :   14 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 309 expanded)
%              Number of equality atoms :   78 ( 225 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

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

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(c_0_14,plain,(
    ! [X18,X19] : r1_tarski(k3_xboole_0(X18,X19),X18) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_15,plain,(
    ! [X29,X30,X31,X32] : k2_zfmisc_1(k3_xboole_0(X29,X30),k3_xboole_0(X31,X32)) = k3_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(X30,X32)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X33,X34,X35] :
      ( k2_zfmisc_1(k4_xboole_0(X33,X34),X35) = k4_xboole_0(k2_zfmisc_1(X33,X35),k2_zfmisc_1(X34,X35))
      & k2_zfmisc_1(X35,k4_xboole_0(X33,X34)) = k4_xboole_0(k2_zfmisc_1(X35,X33),k2_zfmisc_1(X35,X34)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X12,X13,X14] : k5_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X14,X13)) = k3_xboole_0(k5_xboole_0(X12,X14),X13) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_21,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    & k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0
    & ( ~ r1_tarski(esk1_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X9] : k3_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X4)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_40,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k5_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_41,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k5_xboole_0(X23,X24),X25) = k5_xboole_0(X23,k5_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_27]),c_0_27])).

fof(c_0_43,plain,(
    ! [X26] : k5_xboole_0(X26,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_44,plain,(
    ! [X27,X28] :
      ( ( k2_zfmisc_1(X27,X28) != k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | k2_zfmisc_1(X27,X28) = k1_xboole_0 )
      & ( X28 != k1_xboole_0
        | k2_zfmisc_1(X27,X28) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_23]),c_0_36])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2)) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_23]),c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) = k2_zfmisc_1(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_47]),c_0_36])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_62,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_58])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_64]),c_0_65])).

cnf(c_0_69,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = esk1_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_68]),c_0_60]),c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_72]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.32  % Computer   : n025.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 20:43:21 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.33  # No SInE strategy applied
% 0.14/0.33  # Trying AutoSched0 for 299 seconds
% 1.82/2.04  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 1.82/2.04  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.82/2.04  #
% 1.82/2.04  # Preprocessing time       : 0.027 s
% 1.82/2.04  # Presaturation interreduction done
% 1.82/2.04  
% 1.82/2.04  # Proof found!
% 1.82/2.04  # SZS status Theorem
% 1.82/2.04  # SZS output start CNFRefutation
% 1.82/2.04  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.82/2.04  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 1.82/2.04  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.82/2.04  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 1.82/2.04  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 1.82/2.04  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.82/2.04  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 1.82/2.04  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.82/2.04  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.82/2.04  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.82/2.04  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 1.82/2.04  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.82/2.04  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.82/2.04  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.82/2.04  fof(c_0_14, plain, ![X18, X19]:r1_tarski(k3_xboole_0(X18,X19),X18), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.82/2.04  fof(c_0_15, plain, ![X29, X30, X31, X32]:k2_zfmisc_1(k3_xboole_0(X29,X30),k3_xboole_0(X31,X32))=k3_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(X30,X32)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 1.82/2.04  fof(c_0_16, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.82/2.04  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 1.82/2.04  fof(c_0_18, plain, ![X33, X34, X35]:(k2_zfmisc_1(k4_xboole_0(X33,X34),X35)=k4_xboole_0(k2_zfmisc_1(X33,X35),k2_zfmisc_1(X34,X35))&k2_zfmisc_1(X35,k4_xboole_0(X33,X34))=k4_xboole_0(k2_zfmisc_1(X35,X33),k2_zfmisc_1(X35,X34))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 1.82/2.04  fof(c_0_19, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.82/2.04  fof(c_0_20, plain, ![X12, X13, X14]:k5_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X14,X13))=k3_xboole_0(k5_xboole_0(X12,X14),X13), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 1.82/2.04  fof(c_0_21, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.82/2.04  cnf(c_0_22, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.82/2.04  cnf(c_0_23, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.82/2.04  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.82/2.04  fof(c_0_25, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))&(k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0&(~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 1.82/2.04  cnf(c_0_26, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.82/2.04  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.82/2.04  fof(c_0_28, plain, ![X9]:k3_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 1.82/2.04  cnf(c_0_29, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.82/2.04  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.82/2.04  cnf(c_0_31, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.82/2.04  cnf(c_0_32, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 1.82/2.04  cnf(c_0_33, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.82/2.04  cnf(c_0_34, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.82/2.04  cnf(c_0_35, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27])).
% 1.82/2.04  cnf(c_0_36, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.82/2.04  cnf(c_0_37, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.82/2.04  cnf(c_0_38, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X4))), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 1.82/2.04  cnf(c_0_39, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.82/2.04  fof(c_0_40, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k5_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 1.82/2.04  fof(c_0_41, plain, ![X23, X24, X25]:k5_xboole_0(k5_xboole_0(X23,X24),X25)=k5_xboole_0(X23,k5_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 1.82/2.04  cnf(c_0_42, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_27]), c_0_27])).
% 1.82/2.04  fof(c_0_43, plain, ![X26]:k5_xboole_0(X26,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 1.82/2.04  fof(c_0_44, plain, ![X27, X28]:((k2_zfmisc_1(X27,X28)!=k1_xboole_0|(X27=k1_xboole_0|X28=k1_xboole_0))&((X27!=k1_xboole_0|k2_zfmisc_1(X27,X28)=k1_xboole_0)&(X28!=k1_xboole_0|k2_zfmisc_1(X27,X28)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.82/2.04  cnf(c_0_45, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_23]), c_0_36])).
% 1.82/2.04  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_30])).
% 1.82/2.04  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.82/2.04  cnf(c_0_48, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.82/2.04  cnf(c_0_49, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.82/2.04  fof(c_0_50, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 1.82/2.04  cnf(c_0_51, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_23]), c_0_36])).
% 1.82/2.04  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_24])).
% 1.82/2.04  cnf(c_0_53, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.82/2.04  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.82/2.04  cnf(c_0_55, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.82/2.04  cnf(c_0_56, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))=k2_zfmisc_1(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 1.82/2.04  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_47]), c_0_36])).
% 1.82/2.04  cnf(c_0_58, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.82/2.04  cnf(c_0_59, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.82/2.04  cnf(c_0_60, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.82/2.04  cnf(c_0_61, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.82/2.04  cnf(c_0_62, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0)=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 1.82/2.04  cnf(c_0_63, negated_conjecture, (esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.82/2.04  cnf(c_0_64, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_53])).
% 1.82/2.04  cnf(c_0_65, negated_conjecture, (esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_58])).
% 1.82/2.04  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_53]), c_0_60])).
% 1.82/2.04  cnf(c_0_67, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 1.82/2.04  cnf(c_0_68, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_64]), c_0_65])).
% 1.82/2.04  cnf(c_0_69, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_22, c_0_30])).
% 1.82/2.04  cnf(c_0_70, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=esk1_0|~r1_tarski(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_60])).
% 1.82/2.04  cnf(c_0_71, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.82/2.04  cnf(c_0_72, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_68]), c_0_60]), c_0_66])).
% 1.82/2.04  cnf(c_0_73, negated_conjecture, (~r1_tarski(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 1.82/2.04  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_72]), c_0_73]), ['proof']).
% 1.82/2.04  # SZS output end CNFRefutation
% 1.82/2.04  # Proof object total steps             : 75
% 1.82/2.04  # Proof object clause steps            : 46
% 1.82/2.04  # Proof object formula steps           : 29
% 1.82/2.04  # Proof object conjectures             : 20
% 1.82/2.04  # Proof object clause conjectures      : 17
% 1.82/2.04  # Proof object formula conjectures     : 3
% 1.82/2.04  # Proof object initial clauses used    : 19
% 1.82/2.04  # Proof object initial formulas used   : 14
% 1.82/2.04  # Proof object generating inferences   : 22
% 1.82/2.04  # Proof object simplifying inferences  : 21
% 1.82/2.04  # Training examples: 0 positive, 0 negative
% 1.82/2.04  # Parsed axioms                        : 15
% 1.82/2.04  # Removed by relevancy pruning/SinE    : 0
% 1.82/2.04  # Initial clauses                      : 20
% 1.82/2.04  # Removed in clause preprocessing      : 1
% 1.82/2.04  # Initial clauses in saturation        : 19
% 1.82/2.04  # Processed clauses                    : 10633
% 1.82/2.04  # ...of these trivial                  : 263
% 1.82/2.04  # ...subsumed                          : 9236
% 1.82/2.04  # ...remaining for further processing  : 1134
% 1.82/2.04  # Other redundant clauses eliminated   : 0
% 1.82/2.04  # Clauses deleted for lack of memory   : 0
% 1.82/2.04  # Backward-subsumed                    : 133
% 1.82/2.04  # Backward-rewritten                   : 95
% 1.82/2.04  # Generated clauses                    : 274624
% 1.82/2.04  # ...of the previous two non-trivial   : 263186
% 1.82/2.04  # Contextual simplify-reflections      : 6
% 1.82/2.04  # Paramodulations                      : 274618
% 1.82/2.04  # Factorizations                       : 0
% 1.82/2.04  # Equation resolutions                 : 6
% 1.82/2.04  # Propositional unsat checks           : 0
% 1.82/2.04  #    Propositional check models        : 0
% 1.82/2.04  #    Propositional check unsatisfiable : 0
% 1.82/2.04  #    Propositional clauses             : 0
% 1.82/2.04  #    Propositional clauses after purity: 0
% 1.82/2.04  #    Propositional unsat core size     : 0
% 1.82/2.04  #    Propositional preprocessing time  : 0.000
% 1.82/2.04  #    Propositional encoding time       : 0.000
% 1.82/2.04  #    Propositional solver time         : 0.000
% 1.82/2.04  #    Success case prop preproc time    : 0.000
% 1.82/2.04  #    Success case prop encoding time   : 0.000
% 1.82/2.04  #    Success case prop solver time     : 0.000
% 1.82/2.04  # Current number of processed clauses  : 887
% 1.82/2.04  #    Positive orientable unit clauses  : 144
% 1.82/2.04  #    Positive unorientable unit clauses: 14
% 1.82/2.04  #    Negative unit clauses             : 23
% 1.82/2.04  #    Non-unit-clauses                  : 706
% 1.82/2.04  # Current number of unprocessed clauses: 252071
% 1.82/2.04  # ...number of literals in the above   : 662160
% 1.82/2.04  # Current number of archived formulas  : 0
% 1.82/2.04  # Current number of archived clauses   : 248
% 1.82/2.04  # Clause-clause subsumption calls (NU) : 144850
% 1.82/2.04  # Rec. Clause-clause subsumption calls : 60224
% 1.82/2.04  # Non-unit clause-clause subsumptions  : 5034
% 1.82/2.04  # Unit Clause-clause subsumption calls : 1472
% 1.82/2.04  # Rewrite failures with RHS unbound    : 0
% 1.82/2.04  # BW rewrite match attempts            : 978
% 1.82/2.04  # BW rewrite match successes           : 186
% 1.82/2.04  # Condensation attempts                : 0
% 1.82/2.04  # Condensation successes               : 0
% 1.82/2.04  # Termbank termtop insertions          : 3567684
% 1.82/2.05  
% 1.82/2.05  # -------------------------------------------------
% 1.82/2.05  # User time                : 1.619 s
% 1.82/2.05  # System time              : 0.102 s
% 1.82/2.05  # Total time               : 1.720 s
% 1.82/2.05  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
