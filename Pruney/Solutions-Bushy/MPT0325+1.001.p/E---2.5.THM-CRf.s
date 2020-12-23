%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0325+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:25 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 405 expanded)
%              Number of clauses        :   44 ( 176 expanded)
%              Number of leaves         :    7 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          :  108 ( 775 expanded)
%              Number of equality atoms :   81 ( 480 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_9,plain,(
    ! [X17,X18] : r1_tarski(k3_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    & k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0
    & ( ~ r1_tarski(esk1_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X9,X10,X11,X12] : k2_zfmisc_1(k3_xboole_0(X9,X10),k3_xboole_0(X11,X12)) = k3_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X12)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_16])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk4_0,esk2_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_16]),c_0_19]),c_0_16])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_22])).

fof(c_0_27,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_28,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X13 = X15
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | k2_zfmisc_1(X13,X14) != k2_zfmisc_1(X15,X16) )
      & ( X14 = X16
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | k2_zfmisc_1(X13,X14) != k2_zfmisc_1(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X1),k3_xboole_0(k3_xboole_0(esk4_0,esk2_0),X2)) = k2_zfmisc_1(k3_xboole_0(esk1_0,X1),k3_xboole_0(esk2_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_23]),c_0_19])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_24])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk1_0),k3_xboole_0(esk2_0,esk2_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X1),k3_xboole_0(esk4_0,esk2_0)) = k2_zfmisc_1(k3_xboole_0(esk1_0,X1),k3_xboole_0(esk4_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk1_0),k3_xboole_0(esk4_0,esk2_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_32]),c_0_19]),c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk1_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_36]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( X1 = k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X2)
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(k3_xboole_0(esk1_0,X2),k3_xboole_0(esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = X1
    | k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk1_0,esk3_0),X1) = k3_xboole_0(esk1_0,X1)
    | k3_xboole_0(esk1_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = esk2_0 ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk1_0,esk3_0)) = k3_xboole_0(esk1_0,X1)
    | k3_xboole_0(esk1_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk1_0),esk2_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = k3_xboole_0(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_47]),c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k3_xboole_0(esk1_0,esk1_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk1_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_57]),
    [proof]).

%------------------------------------------------------------------------------
