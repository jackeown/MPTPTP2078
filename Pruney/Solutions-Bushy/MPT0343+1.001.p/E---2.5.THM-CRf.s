%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0343+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:27 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 401 expanded)
%              Number of clauses        :   29 ( 150 expanded)
%              Number of leaves         :    3 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          :  126 (2164 expanded)
%              Number of equality atoms :   13 ( 246 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( r2_hidden(X4,X2)
                  <=> r2_hidden(X4,X3) ) )
             => X2 = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_subset_1])).

fof(c_0_4,plain,(
    ! [X7,X8,X9] :
      ( ( m1_subset_1(esk1_3(X7,X8,X9),X7)
        | r1_tarski(X8,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(X7)) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | r1_tarski(X8,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(X7)) )
      & ( ~ r2_hidden(esk1_3(X7,X8,X9),X9)
        | r1_tarski(X8,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X14] :
      ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
      & ( ~ r2_hidden(X14,esk3_0)
        | r2_hidden(X14,esk4_0)
        | ~ m1_subset_1(X14,esk2_0) )
      & ( ~ r2_hidden(X14,esk4_0)
        | r2_hidden(X14,esk3_0)
        | ~ m1_subset_1(X14,esk2_0) )
      & esk3_0 != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

cnf(c_0_6,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk4_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( X1 = X2
    | m1_subset_1(esk1_3(X3,X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk4_0,esk3_0),esk4_0)
    | ~ m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( esk4_0 = X1
    | m1_subset_1(esk1_3(esk2_0,X1,esk4_0),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_7]),c_0_10])])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_7])]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk1_3(esk2_0,X1,esk4_0),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk4_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0)
    | ~ m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0)
    | ~ r1_tarski(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_19]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( esk4_0 = X1
    | m1_subset_1(esk1_3(esk2_0,X1,esk4_0),esk2_0)
    | m1_subset_1(esk1_3(X2,esk4_0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk4_0)
    | ~ m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_10]),c_0_7])]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0)
    | m1_subset_1(esk1_3(X1,esk4_0,esk3_0),X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_7]),c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_10]),c_0_7])]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk4_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 = X1
    | m1_subset_1(esk1_3(esk2_0,X1,esk3_0),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_10]),c_0_7])]),c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_10])]),c_0_20]),c_0_30]),
    [proof]).

%------------------------------------------------------------------------------
