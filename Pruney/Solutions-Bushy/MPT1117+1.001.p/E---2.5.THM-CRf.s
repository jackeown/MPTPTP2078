%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1117+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:45 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   28 (  97 expanded)
%              Number of clauses        :   19 (  40 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 333 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t45_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( r2_hidden(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v4_pre_topc(X4,X1)
                        & r1_tarski(X2,X4) )
                     => r2_hidden(X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_pre_topc)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t48_pre_topc])).

fof(c_0_5,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ~ r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k2_pre_topc(esk3_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_11,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X15,k2_pre_topc(X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v4_pre_topc(X16,X13)
        | ~ r1_tarski(X14,X16)
        | r2_hidden(X15,X16)
        | ~ r2_hidden(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X13)))
        | r2_hidden(X15,k2_pre_topc(X13,X14))
        | ~ r2_hidden(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( v4_pre_topc(esk2_3(X13,X14,X15),X13)
        | r2_hidden(X15,k2_pre_topc(X13,X14))
        | ~ r2_hidden(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( r1_tarski(X14,esk2_3(X13,X14,X15))
        | r2_hidden(X15,k2_pre_topc(X13,X14))
        | ~ r2_hidden(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(X15,esk2_3(X13,X14,X15))
        | r2_hidden(X15,k2_pre_topc(X13,X14))
        | ~ r2_hidden(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k2_pre_topc(esk3_0,esk4_0)),X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,esk2_3(X2,X1,X3))
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ r2_hidden(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k2_pre_topc(esk3_0,esk4_0)),X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | r1_tarski(esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k2_pre_topc(esk3_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_3(esk3_0,esk4_0,esk1_2(esk4_0,k2_pre_topc(esk3_0,esk4_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk2_3(esk3_0,esk4_0,X1))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_17])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k2_pre_topc(esk3_0,esk4_0)),esk2_3(esk3_0,esk4_0,esk1_2(esk4_0,k2_pre_topc(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21])]),c_0_22]),
    [proof]).

%------------------------------------------------------------------------------
