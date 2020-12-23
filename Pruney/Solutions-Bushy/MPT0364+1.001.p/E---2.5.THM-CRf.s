%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0364+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  88 expanded)
%              Number of clauses        :   15 (  34 expanded)
%              Number of leaves         :    4 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 286 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
            <=> r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_subset_1])).

fof(c_0_5,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | m1_subset_1(k3_subset_1(X4,X5),k1_zfmisc_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_6,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ( ~ r1_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0))
      | ~ r1_tarski(esk2_0,esk3_0) )
    & ( r1_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0))
      | r1_tarski(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | k3_subset_1(X6,k3_subset_1(X6,X7)) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_8,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | r1_tarski(X9,k3_subset_1(X8,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( ~ r1_tarski(X9,k3_subset_1(X8,X10))
        | r1_xboole_0(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k3_subset_1(X3,X2))
    | ~ r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_xboole_0(X1,k3_subset_1(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0))
    | r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0))
    | ~ r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_13]),c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_16])]),c_0_22]),
    [proof]).

%------------------------------------------------------------------------------
