%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:12 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 217 expanded)
%              Number of clauses        :   34 (  89 expanded)
%              Number of leaves         :    5 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  179 ( 956 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t49_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

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

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_7,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | m1_subset_1(k2_pre_topc(X13,X14),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X2,X3)
                 => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_pre_topc])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & r1_tarski(esk4_0,esk5_0)
    & ~ r1_tarski(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_14,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v4_pre_topc(X18,X15)
        | ~ r1_tarski(X16,X18)
        | r2_hidden(X17,X18)
        | ~ r2_hidden(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk2_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))
        | r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ r2_hidden(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( v4_pre_topc(esk2_3(X15,X16,X17),X15)
        | r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ r2_hidden(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( r1_tarski(X16,esk2_3(X15,X16,X17))
        | r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ r2_hidden(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(X17,esk2_3(X15,X16,X17))
        | r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ r2_hidden(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,esk2_3(X2,X1,X3))
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ r2_hidden(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))
    | r1_tarski(k2_pre_topc(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v4_pre_topc(esk2_3(X1,X2,X3),X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk5_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(esk5_0,esk2_3(esk3_0,esk5_0,X1))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),u1_struct_0(esk3_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_20])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_20])])).

cnf(c_0_29,negated_conjecture,
    ( v4_pre_topc(esk2_3(esk3_0,esk5_0,X1),esk3_0)
    | r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_20])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),X2)
    | r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(esk5_0,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X4,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v4_pre_topc(esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)),esk3_0)
    | r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))
    | r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))
    | r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,X3))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X3,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_20])]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(esk4_0,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))
    | r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_22])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))
    | r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_10]),c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_20]),c_0_19])]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 16:34:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.92/1.08  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.92/1.08  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.92/1.08  #
% 0.92/1.08  # Preprocessing time       : 0.028 s
% 0.92/1.08  # Presaturation interreduction done
% 0.92/1.08  
% 0.92/1.08  # Proof found!
% 0.92/1.08  # SZS status Theorem
% 0.92/1.08  # SZS output start CNFRefutation
% 0.92/1.08  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.92/1.08  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.92/1.08  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.92/1.08  fof(t49_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 0.92/1.08  fof(t45_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(r2_hidden(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X4,X1)&r1_tarski(X2,X4))=>r2_hidden(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_pre_topc)).
% 0.92/1.08  fof(c_0_5, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.92/1.08  fof(c_0_6, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.92/1.08  fof(c_0_7, plain, ![X13, X14]:(~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|m1_subset_1(k2_pre_topc(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.92/1.08  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))))))), inference(assume_negation,[status(cth)],[t49_pre_topc])).
% 0.92/1.08  cnf(c_0_9, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.92/1.08  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.92/1.08  cnf(c_0_11, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.92/1.08  cnf(c_0_12, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.92/1.08  fof(c_0_13, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(r1_tarski(esk4_0,esk5_0)&~r1_tarski(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.92/1.08  fof(c_0_14, plain, ![X15, X16, X17, X18]:((~r2_hidden(X17,k2_pre_topc(X15,X16))|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))|(~v4_pre_topc(X18,X15)|~r1_tarski(X16,X18)|r2_hidden(X17,X18)))|~r2_hidden(X17,u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&((m1_subset_1(esk2_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))|r2_hidden(X17,k2_pre_topc(X15,X16))|~r2_hidden(X17,u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(((v4_pre_topc(esk2_3(X15,X16,X17),X15)|r2_hidden(X17,k2_pre_topc(X15,X16))|~r2_hidden(X17,u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(r1_tarski(X16,esk2_3(X15,X16,X17))|r2_hidden(X17,k2_pre_topc(X15,X16))|~r2_hidden(X17,u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15)))&(~r2_hidden(X17,esk2_3(X15,X16,X17))|r2_hidden(X17,k2_pre_topc(X15,X16))|~r2_hidden(X17,u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).
% 0.92/1.08  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.92/1.08  cnf(c_0_16, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.92/1.08  cnf(c_0_17, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.92/1.08  cnf(c_0_18, plain, (r1_tarski(X1,esk2_3(X2,X1,X3))|r2_hidden(X3,k2_pre_topc(X2,X1))|~r2_hidden(X3,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.08  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.92/1.08  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.92/1.08  cnf(c_0_21, plain, (r2_hidden(esk1_2(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))|r1_tarski(k2_pre_topc(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.92/1.08  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.92/1.08  cnf(c_0_23, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|r2_hidden(X3,k2_pre_topc(X1,X2))|~r2_hidden(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.08  cnf(c_0_24, plain, (v4_pre_topc(esk2_3(X1,X2,X3),X1)|r2_hidden(X3,k2_pre_topc(X1,X2))|~r2_hidden(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.08  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk5_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_17])).
% 0.92/1.08  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))|r1_tarski(esk5_0,esk2_3(esk3_0,esk5_0,X1))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.92/1.08  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),u1_struct_0(esk3_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_20])])).
% 0.92/1.08  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_20])])).
% 0.92/1.08  cnf(c_0_29, negated_conjecture, (v4_pre_topc(esk2_3(esk3_0,esk5_0,X1),esk3_0)|r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_20])])).
% 0.92/1.08  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),X2)|r1_tarski(esk4_0,X1)|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_9, c_0_25])).
% 0.92/1.08  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(esk5_0,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.92/1.08  cnf(c_0_32, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,k2_pre_topc(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X4,X2)|~r1_tarski(X3,X4)|~r2_hidden(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.08  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.92/1.08  cnf(c_0_34, negated_conjecture, (v4_pre_topc(esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)),esk3_0)|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.92/1.08  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.92/1.08  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.92/1.08  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,k2_pre_topc(esk3_0,X3))|~r2_hidden(X1,u1_struct_0(esk3_0))|~r1_tarski(X3,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_20])]), c_0_34])).
% 0.92/1.08  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(esk4_0,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.92/1.08  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)|~r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_22])])).
% 0.92/1.08  cnf(c_0_40, plain, (r2_hidden(X1,k2_pre_topc(X2,X3))|~r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.08  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_10]), c_0_27])).
% 0.92/1.08  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_20]), c_0_19])]), c_0_27])).
% 0.92/1.08  cnf(c_0_43, negated_conjecture, (~r1_tarski(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.92/1.08  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_42]), c_0_43]), ['proof']).
% 0.92/1.08  # SZS output end CNFRefutation
% 0.92/1.08  # Proof object total steps             : 45
% 0.92/1.08  # Proof object clause steps            : 34
% 0.92/1.08  # Proof object formula steps           : 11
% 0.92/1.08  # Proof object conjectures             : 24
% 0.92/1.08  # Proof object clause conjectures      : 21
% 0.92/1.08  # Proof object formula conjectures     : 3
% 0.92/1.08  # Proof object initial clauses used    : 15
% 0.92/1.08  # Proof object initial formulas used   : 5
% 0.92/1.08  # Proof object generating inferences   : 19
% 0.92/1.08  # Proof object simplifying inferences  : 19
% 0.92/1.08  # Training examples: 0 positive, 0 negative
% 0.92/1.08  # Parsed axioms                        : 5
% 0.92/1.08  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.08  # Initial clauses                      : 16
% 0.92/1.08  # Removed in clause preprocessing      : 0
% 0.92/1.08  # Initial clauses in saturation        : 16
% 0.92/1.08  # Processed clauses                    : 3333
% 0.92/1.08  # ...of these trivial                  : 0
% 0.92/1.08  # ...subsumed                          : 1732
% 0.92/1.08  # ...remaining for further processing  : 1601
% 0.92/1.08  # Other redundant clauses eliminated   : 0
% 0.92/1.08  # Clauses deleted for lack of memory   : 0
% 0.92/1.08  # Backward-subsumed                    : 243
% 0.92/1.08  # Backward-rewritten                   : 13
% 0.92/1.08  # Generated clauses                    : 30149
% 0.92/1.08  # ...of the previous two non-trivial   : 30157
% 0.92/1.08  # Contextual simplify-reflections      : 45
% 0.92/1.08  # Paramodulations                      : 30149
% 0.92/1.08  # Factorizations                       : 0
% 0.92/1.08  # Equation resolutions                 : 0
% 0.92/1.08  # Propositional unsat checks           : 0
% 0.92/1.08  #    Propositional check models        : 0
% 0.92/1.08  #    Propositional check unsatisfiable : 0
% 0.92/1.08  #    Propositional clauses             : 0
% 0.92/1.08  #    Propositional clauses after purity: 0
% 0.92/1.08  #    Propositional unsat core size     : 0
% 0.92/1.08  #    Propositional preprocessing time  : 0.000
% 0.92/1.08  #    Propositional encoding time       : 0.000
% 0.92/1.08  #    Propositional solver time         : 0.000
% 0.92/1.08  #    Success case prop preproc time    : 0.000
% 0.92/1.08  #    Success case prop encoding time   : 0.000
% 0.92/1.08  #    Success case prop solver time     : 0.000
% 0.92/1.08  # Current number of processed clauses  : 1329
% 0.92/1.08  #    Positive orientable unit clauses  : 119
% 0.92/1.08  #    Positive unorientable unit clauses: 0
% 0.92/1.08  #    Negative unit clauses             : 1
% 0.92/1.08  #    Non-unit-clauses                  : 1209
% 0.92/1.08  # Current number of unprocessed clauses: 26584
% 0.92/1.08  # ...number of literals in the above   : 121072
% 0.92/1.08  # Current number of archived formulas  : 0
% 0.92/1.08  # Current number of archived clauses   : 272
% 0.92/1.08  # Clause-clause subsumption calls (NU) : 299778
% 0.92/1.08  # Rec. Clause-clause subsumption calls : 88040
% 0.92/1.08  # Non-unit clause-clause subsumptions  : 2020
% 0.92/1.08  # Unit Clause-clause subsumption calls : 15229
% 0.92/1.08  # Rewrite failures with RHS unbound    : 0
% 0.92/1.08  # BW rewrite match attempts            : 1481
% 0.92/1.08  # BW rewrite match successes           : 13
% 0.92/1.08  # Condensation attempts                : 0
% 0.92/1.08  # Condensation successes               : 0
% 0.92/1.08  # Termbank termtop insertions          : 1781502
% 0.92/1.08  
% 0.92/1.08  # -------------------------------------------------
% 0.92/1.08  # User time                : 0.713 s
% 0.92/1.08  # System time              : 0.025 s
% 0.92/1.08  # Total time               : 0.738 s
% 0.92/1.08  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
