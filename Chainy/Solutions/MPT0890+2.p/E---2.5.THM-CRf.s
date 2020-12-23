%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0890+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:56 EST 2020

% Result     : Theorem 8.40s
% Output     : CNFRefutation 8.40s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 191 expanded)
%              Number of clauses        :   20 (  74 expanded)
%              Number of leaves         :    5 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 666 expanded)
%              Number of equality atoms :   60 ( 572 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                  & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                  & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_mcart_1])).

fof(c_0_6,plain,(
    ! [X102,X103,X104,X105] :
      ( X102 = k1_xboole_0
      | X103 = k1_xboole_0
      | X104 = k1_xboole_0
      | ~ m1_subset_1(X105,k3_zfmisc_1(X102,X103,X104))
      | X105 = k3_mcart_1(k5_mcart_1(X102,X103,X104,X105),k6_mcart_1(X102,X103,X104,X105),k7_mcart_1(X102,X103,X104,X105)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_7,plain,(
    ! [X863,X864,X865] : k3_mcart_1(X863,X864,X865) = k4_tarski(k4_tarski(X863,X864),X865) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_8,plain,(
    ! [X269,X270,X271] : k3_zfmisc_1(X269,X270,X271) = k2_zfmisc_1(k2_zfmisc_1(X269,X270),X271) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_9,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    & ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_mcart_1(k1_mcart_1(esk4_0))
      | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(k1_mcart_1(esk4_0))
      | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X75,X76] :
      ( k1_mcart_1(k4_tarski(X75,X76)) = X75
      & k2_mcart_1(k4_tarski(X75,X76)) = X76 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_15,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k2_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_mcart_1(k1_mcart_1(esk4_0))
    | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(k1_mcart_1(esk4_0))
    | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = k1_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk4_0)) != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)
    | k2_mcart_1(k1_mcart_1(esk4_0)) != k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22])])).

cnf(c_0_28,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk4_0)) = k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk4_0)) != k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
