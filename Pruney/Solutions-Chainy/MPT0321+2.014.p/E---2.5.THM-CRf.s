%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:00 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 (2919 expanded)
%              Number of clauses        :   73 (1296 expanded)
%              Number of leaves         :    8 ( 745 expanded)
%              Depth                    :   27
%              Number of atoms          :  182 (6064 expanded)
%              Number of equality atoms :   77 (4252 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X20] : k2_zfmisc_1(k3_xboole_0(X17,X18),k3_xboole_0(X19,X20)) = k3_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X20)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_10,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k2_zfmisc_1(esk3_0,esk4_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & ( esk1_0 != esk3_0
      | esk2_0 != esk4_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_11,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_14,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_15,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(X1,esk3_0),k3_xboole_0(X2,esk4_0)) = k2_zfmisc_1(k3_xboole_0(X1,esk1_0),k3_xboole_0(X2,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_11])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(X1,esk1_0),k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(k3_xboole_0(X1,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X14,X15,X16] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,X14))
        | X14 = k1_xboole_0
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X16))
        | X14 = k1_xboole_0
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_22,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk4_0) = k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

fof(c_0_24,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X10,X11] : r1_tarski(k3_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(esk2_0,esk4_0))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,X1),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk4_0)
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_34,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(esk2_0,esk4_0))
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(esk2_0,esk4_0))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,X1),k2_zfmisc_1(esk1_0,esk4_0))
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_33]),c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( k3_xboole_0(X1,esk4_0) = k1_xboole_0
    | r1_tarski(X2,k3_xboole_0(X3,esk3_0))
    | ~ r1_tarski(k2_zfmisc_1(X2,k3_xboole_0(X1,esk4_0)),k2_zfmisc_1(k3_xboole_0(X3,esk1_0),k3_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk2_0
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(esk2_0,esk4_0))
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(X2,esk3_0))
    | ~ r1_tarski(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(k3_xboole_0(X2,esk1_0),esk2_0))
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_16]),c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk4_0
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_43]),c_0_44])])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(X2,esk3_0))
    | ~ r1_tarski(X1,k3_xboole_0(X2,esk1_0))
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(X1,esk3_0),esk4_0) = k2_zfmisc_1(k3_xboole_0(X1,esk1_0),esk2_0)
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_47]),c_0_16])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(X1,esk3_0) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X1,esk1_0))
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)),k2_zfmisc_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_50]),c_0_16])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = esk1_0
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_16]),c_0_31])])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_12])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0))
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_20])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,esk3_0),esk4_0),k2_zfmisc_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0))
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk1_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_16]),c_0_12])).

cnf(c_0_63,negated_conjecture,
    ( esk4_0 = esk2_0
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_59]),c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_62]),c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 = esk1_0
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_55])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_69,negated_conjecture,
    ( esk4_0 = esk2_0
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = esk1_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_57]),c_0_16])).

cnf(c_0_73,negated_conjecture,
    ( esk1_0 != esk3_0
    | esk2_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk4_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( esk3_0 = esk1_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_66])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(esk2_0,esk4_0))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,X1),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_72]),c_0_27])).

cnf(c_0_77,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(esk2_0,esk4_0))
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_31])).

cnf(c_0_79,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k1_xboole_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_12,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(k1_xboole_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_66])]),c_0_77]),c_0_17])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_80]),c_0_44])])).

cnf(c_0_83,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(X1,esk1_0),esk2_0) = k2_zfmisc_1(X1,k1_xboole_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_81]),c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(X2,esk1_0))
    | ~ r1_tarski(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X2,k1_xboole_0))
    | ~ r1_tarski(X2,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_83]),c_0_41])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(esk1_0,esk3_0))
    | ~ r1_tarski(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_79]),c_0_17]),c_0_31])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_31])).

cnf(c_0_87,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_86]),c_0_32])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_77]),c_0_41])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_87]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.19/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.027 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.19/0.41  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.19/0.41  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.41  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.41  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.19/0.41  fof(c_0_9, plain, ![X17, X18, X19, X20]:k2_zfmisc_1(k3_xboole_0(X17,X18),k3_xboole_0(X19,X20))=k3_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X20)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.19/0.41  fof(c_0_10, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k2_zfmisc_1(esk3_0,esk4_0)&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&(esk1_0!=esk3_0|esk2_0!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.41  cnf(c_0_11, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_12, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k2_zfmisc_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  fof(c_0_13, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.41  fof(c_0_14, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.41  cnf(c_0_15, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(X1,esk3_0),k3_xboole_0(X2,esk4_0))=k2_zfmisc_1(k3_xboole_0(X1,esk1_0),k3_xboole_0(X2,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_11])).
% 0.19/0.41  cnf(c_0_16, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  fof(c_0_18, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.41  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(X1,esk1_0),k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(k3_xboole_0(X1,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.19/0.41  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  fof(c_0_21, plain, ![X14, X15, X16]:((~r1_tarski(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,X14))|X14=k1_xboole_0|r1_tarski(X15,X16))&(~r1_tarski(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X16))|X14=k1_xboole_0|r1_tarski(X15,X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.19/0.41  cnf(c_0_22, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk4_0)=k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_16])).
% 0.19/0.41  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.19/0.41  fof(c_0_24, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  cnf(c_0_25, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk3_0,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_12])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  fof(c_0_29, plain, ![X10, X11]:r1_tarski(k3_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (r1_tarski(X1,k3_xboole_0(esk2_0,esk4_0))|~r1_tarski(k2_zfmisc_1(esk1_0,X1),k2_zfmisc_1(esk1_0,esk2_0))|~r1_tarski(esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.19/0.41  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_32, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk4_0)|~r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.19/0.41  cnf(c_0_34, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_35, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (r1_tarski(esk2_0,k3_xboole_0(esk2_0,esk4_0))|~r1_tarski(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.41  cnf(c_0_37, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_32, c_0_11])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (r1_tarski(X1,k3_xboole_0(esk2_0,esk4_0))|~r1_tarski(k2_zfmisc_1(esk1_0,X1),k2_zfmisc_1(esk1_0,esk4_0))|~r1_tarski(esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_33]), c_0_27])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (k3_xboole_0(X1,esk4_0)=k1_xboole_0|r1_tarski(X2,k3_xboole_0(X3,esk3_0))|~r1_tarski(k2_zfmisc_1(X2,k3_xboole_0(X1,esk4_0)),k2_zfmisc_1(k3_xboole_0(X3,esk1_0),k3_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_34, c_0_15])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk2_0|~r1_tarski(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_32])])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_42, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_37, c_0_16])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (r1_tarski(esk4_0,k3_xboole_0(esk2_0,esk4_0))|~r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_31])).
% 0.19/0.41  cnf(c_0_44, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_32, c_0_17])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (r1_tarski(X1,k3_xboole_0(X2,esk3_0))|~r1_tarski(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(k3_xboole_0(X2,esk1_0),esk2_0))|~r1_tarski(esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_16]), c_0_41])).
% 0.19/0.41  cnf(c_0_46, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk4_0|~r1_tarski(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_43]), c_0_44])])).
% 0.19/0.41  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,k3_xboole_0(X2,esk3_0))|~r1_tarski(X1,k3_xboole_0(X2,esk1_0))|~r1_tarski(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(X1,esk3_0),esk4_0)=k2_zfmisc_1(k3_xboole_0(X1,esk1_0),esk2_0)|~r1_tarski(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_47]), c_0_16])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (k3_xboole_0(X1,esk3_0)=X1|~r1_tarski(X1,k3_xboole_0(X1,esk1_0))|~r1_tarski(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)),k2_zfmisc_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_22])).
% 0.19/0.41  cnf(c_0_53, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_44, c_0_11])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_50]), c_0_16])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=esk1_0|~r1_tarski(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_16]), c_0_31])])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk3_0,X1)|~r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_12])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0))|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_20])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,esk3_0),esk4_0),k2_zfmisc_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_19])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0))|~r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_54])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_44, c_0_55])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk3_0,esk1_0)|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_16]), c_0_12])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (esk4_0=esk2_0|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_59]), c_0_27])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (r1_tarski(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_62]), c_0_27])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (esk3_0=esk1_0|~r1_tarski(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_23, c_0_55])).
% 0.19/0.41  cnf(c_0_68, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_20, c_0_11])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (esk4_0=esk2_0|~r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=esk1_0|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_61])).
% 0.19/0.41  cnf(c_0_72, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_57]), c_0_16])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (esk1_0!=esk3_0|esk2_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_74, negated_conjecture, (esk4_0=k1_xboole_0|esk4_0=esk2_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.41  cnf(c_0_75, negated_conjecture, (esk3_0=esk1_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_66])])).
% 0.19/0.41  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,k3_xboole_0(esk2_0,esk4_0))|~r1_tarski(k2_zfmisc_1(esk1_0,X1),k2_zfmisc_1(esk1_0,esk2_0))|~r1_tarski(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_72]), c_0_27])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (r1_tarski(esk2_0,k3_xboole_0(esk2_0,esk4_0))|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_31])).
% 0.19/0.41  cnf(c_0_79, negated_conjecture, (k2_zfmisc_1(esk3_0,k1_xboole_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_12, c_0_77])).
% 0.19/0.41  cnf(c_0_80, negated_conjecture, (r1_tarski(esk2_0,k3_xboole_0(k1_xboole_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_66])]), c_0_77]), c_0_17])).
% 0.19/0.41  cnf(c_0_81, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(esk1_0,esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_79])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_80]), c_0_44])])).
% 0.19/0.41  cnf(c_0_83, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(X1,esk1_0),esk2_0)=k2_zfmisc_1(X1,k1_xboole_0)|~r1_tarski(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_81]), c_0_82])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, (r1_tarski(X1,k3_xboole_0(X2,esk1_0))|~r1_tarski(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X2,k1_xboole_0))|~r1_tarski(X2,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_83]), c_0_41])).
% 0.19/0.41  cnf(c_0_85, negated_conjecture, (r1_tarski(X1,k3_xboole_0(esk1_0,esk3_0))|~r1_tarski(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_79]), c_0_17]), c_0_31])])).
% 0.19/0.41  cnf(c_0_86, negated_conjecture, (r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_85, c_0_31])).
% 0.19/0.41  cnf(c_0_87, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_86]), c_0_32])])).
% 0.19/0.41  cnf(c_0_88, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_77]), c_0_41])).
% 0.19/0.41  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_87]), c_0_88]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 90
% 0.19/0.41  # Proof object clause steps            : 73
% 0.19/0.41  # Proof object formula steps           : 17
% 0.19/0.41  # Proof object conjectures             : 58
% 0.19/0.41  # Proof object clause conjectures      : 55
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 13
% 0.19/0.41  # Proof object initial formulas used   : 8
% 0.19/0.41  # Proof object generating inferences   : 54
% 0.19/0.41  # Proof object simplifying inferences  : 43
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 8
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 14
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 14
% 0.19/0.41  # Processed clauses                    : 430
% 0.19/0.41  # ...of these trivial                  : 14
% 0.19/0.41  # ...subsumed                          : 215
% 0.19/0.41  # ...remaining for further processing  : 201
% 0.19/0.41  # Other redundant clauses eliminated   : 2
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 28
% 0.19/0.41  # Backward-rewritten                   : 80
% 0.19/0.41  # Generated clauses                    : 1981
% 0.19/0.41  # ...of the previous two non-trivial   : 1747
% 0.19/0.41  # Contextual simplify-reflections      : 2
% 0.19/0.41  # Paramodulations                      : 1978
% 0.19/0.41  # Factorizations                       : 1
% 0.19/0.41  # Equation resolutions                 : 2
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 78
% 0.19/0.41  #    Positive orientable unit clauses  : 19
% 0.19/0.41  #    Positive unorientable unit clauses: 2
% 0.19/0.41  #    Negative unit clauses             : 5
% 0.19/0.41  #    Non-unit-clauses                  : 52
% 0.19/0.41  # Current number of unprocessed clauses: 1246
% 0.19/0.41  # ...number of literals in the above   : 2968
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 121
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 1695
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1586
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 181
% 0.19/0.41  # Unit Clause-clause subsumption calls : 68
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 25
% 0.19/0.41  # BW rewrite match successes           : 20
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 28189
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.059 s
% 0.19/0.41  # System time              : 0.006 s
% 0.19/0.41  # Total time               : 0.065 s
% 0.19/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
