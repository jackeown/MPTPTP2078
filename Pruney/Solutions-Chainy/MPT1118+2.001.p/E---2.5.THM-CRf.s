%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:11 EST 2020

% Result     : Theorem 0.51s
% Output     : CNFRefutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 193 expanded)
%              Number of clauses        :   34 (  77 expanded)
%              Number of leaves         :    5 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  178 ( 861 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t49_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).

fof(c_0_5,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ r2_hidden(X13,X12)
      | r2_hidden(X13,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_6,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | m1_subset_1(k2_pre_topc(X14,X15),k1_zfmisc_1(u1_struct_0(X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X2,X3)
                 => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_pre_topc])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & r1_tarski(esk4_0,esk5_0)
    & ~ r1_tarski(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v4_pre_topc(X19,X16)
        | ~ r1_tarski(X17,X19)
        | r2_hidden(X18,X19)
        | ~ r2_hidden(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk2_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))
        | r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ r2_hidden(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( v4_pre_topc(esk2_3(X16,X17,X18),X16)
        | r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ r2_hidden(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( r1_tarski(X17,esk2_3(X16,X17,X18))
        | r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ r2_hidden(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(X18,esk2_3(X16,X17,X18))
        | r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ r2_hidden(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,esk2_3(X2,X1,X3))
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ r2_hidden(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

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
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(esk5_0,esk2_3(esk3_0,esk5_0,X1))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_17])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),u1_struct_0(esk3_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_21]),c_0_17])])).

cnf(c_0_29,negated_conjecture,
    ( v4_pre_topc(esk2_3(esk3_0,esk5_0,X1),esk3_0)
    | r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_17])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),X2)
    | r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_25])).

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
    inference(split_conjunct,[status(thm)],[c_0_8])).

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
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_17])]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(esk4_0,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))
    | r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_16])]),c_0_22])).

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
    inference(spm,[status(thm)],[c_0_39,c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_17]),c_0_21])]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:42:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.51/0.69  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.51/0.69  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.51/0.69  #
% 0.51/0.69  # Preprocessing time       : 0.027 s
% 0.51/0.69  # Presaturation interreduction done
% 0.51/0.69  
% 0.51/0.69  # Proof found!
% 0.51/0.69  # SZS status Theorem
% 0.51/0.69  # SZS output start CNFRefutation
% 0.51/0.69  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.51/0.69  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.51/0.69  fof(t49_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 0.51/0.69  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.51/0.69  fof(t45_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(r2_hidden(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X4,X1)&r1_tarski(X2,X4))=>r2_hidden(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_pre_topc)).
% 0.51/0.69  fof(c_0_5, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~r2_hidden(X13,X12)|r2_hidden(X13,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.51/0.69  fof(c_0_6, plain, ![X14, X15]:(~l1_pre_topc(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|m1_subset_1(k2_pre_topc(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.51/0.69  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))))))), inference(assume_negation,[status(cth)],[t49_pre_topc])).
% 0.51/0.69  fof(c_0_8, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.51/0.69  cnf(c_0_9, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.51/0.69  cnf(c_0_10, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.51/0.69  fof(c_0_11, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(r1_tarski(esk4_0,esk5_0)&~r1_tarski(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.51/0.69  cnf(c_0_12, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.51/0.69  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.51/0.69  fof(c_0_14, plain, ![X16, X17, X18, X19]:((~r2_hidden(X18,k2_pre_topc(X16,X17))|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|(~v4_pre_topc(X19,X16)|~r1_tarski(X17,X19)|r2_hidden(X18,X19)))|~r2_hidden(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&((m1_subset_1(esk2_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))|r2_hidden(X18,k2_pre_topc(X16,X17))|~r2_hidden(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(((v4_pre_topc(esk2_3(X16,X17,X18),X16)|r2_hidden(X18,k2_pre_topc(X16,X17))|~r2_hidden(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(r1_tarski(X17,esk2_3(X16,X17,X18))|r2_hidden(X18,k2_pre_topc(X16,X17))|~r2_hidden(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16)))&(~r2_hidden(X18,esk2_3(X16,X17,X18))|r2_hidden(X18,k2_pre_topc(X16,X17))|~r2_hidden(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).
% 0.51/0.69  cnf(c_0_15, plain, (r2_hidden(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,k2_pre_topc(X2,X3))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.51/0.69  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.51/0.69  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.51/0.69  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.51/0.69  cnf(c_0_19, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.51/0.69  cnf(c_0_20, plain, (r1_tarski(X1,esk2_3(X2,X1,X3))|r2_hidden(X3,k2_pre_topc(X2,X1))|~r2_hidden(X3,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.69  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.51/0.69  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.51/0.69  cnf(c_0_23, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|r2_hidden(X3,k2_pre_topc(X1,X2))|~r2_hidden(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.69  cnf(c_0_24, plain, (v4_pre_topc(esk2_3(X1,X2,X3),X1)|r2_hidden(X3,k2_pre_topc(X1,X2))|~r2_hidden(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.69  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk5_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.51/0.69  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))|r1_tarski(esk5_0,esk2_3(esk3_0,esk5_0,X1))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_17])])).
% 0.51/0.69  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),u1_struct_0(esk3_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_22, c_0_13])).
% 0.51/0.69  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_21]), c_0_17])])).
% 0.51/0.69  cnf(c_0_29, negated_conjecture, (v4_pre_topc(esk2_3(esk3_0,esk5_0,X1),esk3_0)|r2_hidden(X1,k2_pre_topc(esk3_0,esk5_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_17])])).
% 0.51/0.69  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),X2)|r1_tarski(esk4_0,X1)|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_12, c_0_25])).
% 0.51/0.69  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(esk5_0,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.51/0.69  cnf(c_0_32, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,k2_pre_topc(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X4,X2)|~r1_tarski(X3,X4)|~r2_hidden(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.69  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.51/0.69  cnf(c_0_34, negated_conjecture, (v4_pre_topc(esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)),esk3_0)|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.51/0.69  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.51/0.69  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.51/0.69  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,k2_pre_topc(esk3_0,X3))|~r2_hidden(X1,u1_struct_0(esk3_0))|~r1_tarski(X3,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_17])]), c_0_34])).
% 0.51/0.69  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(esk4_0,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X1)))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.51/0.69  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)|~r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_16])]), c_0_22])).
% 0.51/0.69  cnf(c_0_40, plain, (r2_hidden(X1,k2_pre_topc(X2,X3))|~r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.69  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),esk2_3(esk3_0,esk5_0,esk1_2(k2_pre_topc(esk3_0,esk4_0),X2)))|r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X2),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X2)), inference(spm,[status(thm)],[c_0_39, c_0_13])).
% 0.51/0.69  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk4_0),X1),k2_pre_topc(esk3_0,esk5_0))|r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_17]), c_0_21])]), c_0_27])).
% 0.51/0.69  cnf(c_0_43, negated_conjecture, (~r1_tarski(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.51/0.69  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_42]), c_0_43]), ['proof']).
% 0.51/0.69  # SZS output end CNFRefutation
% 0.51/0.69  # Proof object total steps             : 45
% 0.51/0.69  # Proof object clause steps            : 34
% 0.51/0.69  # Proof object formula steps           : 11
% 0.51/0.69  # Proof object conjectures             : 25
% 0.51/0.69  # Proof object clause conjectures      : 22
% 0.51/0.69  # Proof object formula conjectures     : 3
% 0.51/0.69  # Proof object initial clauses used    : 15
% 0.51/0.69  # Proof object initial formulas used   : 5
% 0.51/0.69  # Proof object generating inferences   : 19
% 0.51/0.69  # Proof object simplifying inferences  : 19
% 0.51/0.69  # Training examples: 0 positive, 0 negative
% 0.51/0.69  # Parsed axioms                        : 5
% 0.51/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.51/0.69  # Initial clauses                      : 15
% 0.51/0.69  # Removed in clause preprocessing      : 0
% 0.51/0.69  # Initial clauses in saturation        : 15
% 0.51/0.69  # Processed clauses                    : 1597
% 0.51/0.69  # ...of these trivial                  : 0
% 0.51/0.69  # ...subsumed                          : 458
% 0.51/0.69  # ...remaining for further processing  : 1139
% 0.51/0.69  # Other redundant clauses eliminated   : 0
% 0.51/0.69  # Clauses deleted for lack of memory   : 0
% 0.51/0.69  # Backward-subsumed                    : 155
% 0.51/0.69  # Backward-rewritten                   : 0
% 0.51/0.69  # Generated clauses                    : 9595
% 0.51/0.69  # ...of the previous two non-trivial   : 9590
% 0.51/0.69  # Contextual simplify-reflections      : 37
% 0.51/0.69  # Paramodulations                      : 9595
% 0.51/0.69  # Factorizations                       : 0
% 0.51/0.69  # Equation resolutions                 : 0
% 0.51/0.69  # Propositional unsat checks           : 0
% 0.51/0.69  #    Propositional check models        : 0
% 0.51/0.69  #    Propositional check unsatisfiable : 0
% 0.51/0.69  #    Propositional clauses             : 0
% 0.51/0.69  #    Propositional clauses after purity: 0
% 0.51/0.69  #    Propositional unsat core size     : 0
% 0.51/0.69  #    Propositional preprocessing time  : 0.000
% 0.51/0.69  #    Propositional encoding time       : 0.000
% 0.51/0.69  #    Propositional solver time         : 0.000
% 0.51/0.69  #    Success case prop preproc time    : 0.000
% 0.51/0.69  #    Success case prop encoding time   : 0.000
% 0.51/0.69  #    Success case prop solver time     : 0.000
% 0.51/0.69  # Current number of processed clauses  : 969
% 0.51/0.69  #    Positive orientable unit clauses  : 37
% 0.51/0.69  #    Positive unorientable unit clauses: 0
% 0.51/0.69  #    Negative unit clauses             : 1
% 0.51/0.69  #    Non-unit-clauses                  : 931
% 0.51/0.69  # Current number of unprocessed clauses: 7906
% 0.51/0.69  # ...number of literals in the above   : 39406
% 0.51/0.69  # Current number of archived formulas  : 0
% 0.51/0.69  # Current number of archived clauses   : 170
% 0.51/0.69  # Clause-clause subsumption calls (NU) : 175323
% 0.51/0.69  # Rec. Clause-clause subsumption calls : 32857
% 0.51/0.69  # Non-unit clause-clause subsumptions  : 650
% 0.51/0.69  # Unit Clause-clause subsumption calls : 5082
% 0.51/0.69  # Rewrite failures with RHS unbound    : 0
% 0.51/0.69  # BW rewrite match attempts            : 131
% 0.51/0.69  # BW rewrite match successes           : 0
% 0.51/0.69  # Condensation attempts                : 0
% 0.51/0.69  # Condensation successes               : 0
% 0.51/0.69  # Termbank termtop insertions          : 598996
% 0.51/0.69  
% 0.51/0.69  # -------------------------------------------------
% 0.51/0.69  # User time                : 0.336 s
% 0.51/0.69  # System time              : 0.015 s
% 0.51/0.69  # Total time               : 0.351 s
% 0.51/0.69  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
