%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0895+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 143 expanded)
%              Number of clauses        :   29 (  66 expanded)
%              Number of leaves         :    4 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 551 expanded)
%              Number of equality atoms :  113 ( 550 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0 )
      <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t55_mcart_1])).

fof(c_0_5,negated_conjecture,
    ( ( esk1_0 = k1_xboole_0
      | esk2_0 = k1_xboole_0
      | esk3_0 = k1_xboole_0
      | esk4_0 = k1_xboole_0
      | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k1_xboole_0 )
    & ( esk1_0 != k1_xboole_0
      | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 )
    & ( esk2_0 != k1_xboole_0
      | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 )
    & ( esk3_0 != k1_xboole_0
      | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 )
    & ( esk4_0 != k1_xboole_0
      | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8] : k4_zfmisc_1(X5,X6,X7,X8) = k2_zfmisc_1(k3_zfmisc_1(X5,X6,X7),X8) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_8,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X11,X12,X13] :
      ( ( X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | k3_zfmisc_1(X11,X12,X13) != k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k3_zfmisc_1(X11,X12,X13) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k3_zfmisc_1(X11,X12,X13) = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k3_zfmisc_1(X11,X12,X13) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_26,plain,
    ( k3_zfmisc_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_30,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_32,plain,
    ( k3_zfmisc_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_27])])).

cnf(c_0_36,plain,
    ( k3_zfmisc_1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_27]),c_0_35])]),
    [proof]).

%------------------------------------------------------------------------------
