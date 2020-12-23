%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0427+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:37 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 152 expanded)
%              Number of clauses        :   30 (  68 expanded)
%              Number of leaves         :    5 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 ( 512 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t58_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( r2_hidden(X2,X1)
       => ( r2_hidden(X2,k8_setfam_1(X1,X3))
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
             => r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(X2,X3)
             => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_setfam_1])).

fof(c_0_6,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & r1_tarski(esk4_0,esk5_0)
    & ~ r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11)))
      | m1_subset_1(k8_setfam_1(X11,X12),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

cnf(c_0_11,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),k8_setfam_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_13,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),X1)
    | ~ r1_tarski(k8_setfam_1(esk3_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_17,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X16,k8_setfam_1(X15,X17))
        | ~ r2_hidden(X18,X17)
        | r2_hidden(X16,X18)
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X17)
        | r2_hidden(X16,k8_setfam_1(X15,X17))
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( ~ r2_hidden(X16,esk2_3(X15,X16,X17))
        | r2_hidden(X16,k8_setfam_1(X15,X17))
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_setfam_1])])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k8_setfam_1(esk3_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),X1),k8_setfam_1(esk3_0,esk5_0))
    | r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_9])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(X2,k8_setfam_1(X1,X3))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k8_setfam_1(esk3_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k8_setfam_1(X2,X3))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),X1)
    | r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),X1),X2)
    | ~ r1_tarski(k8_setfam_1(esk3_0,esk5_0),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,X1,esk4_0),esk4_0)
    | r2_hidden(X1,k8_setfam_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k8_setfam_1(X2,X3))
    | ~ r2_hidden(X1,esk2_3(X2,X1,X3))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k8_setfam_1(esk3_0,esk5_0))
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),X1)
    | r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),esk4_0),esk4_0)
    | r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k8_setfam_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk2_3(esk3_0,X1,esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),X1)
    | r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),X1),X2)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),esk4_0),X1)
    | r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),k8_setfam_1(esk3_0,esk4_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),X1)
    | r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),X1),k8_setfam_1(esk3_0,esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk1_2(k8_setfam_1(esk3_0,esk5_0),X1),esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),esk4_0),esk5_0)
    | r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_2(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_8]),
    [proof]).

%------------------------------------------------------------------------------
