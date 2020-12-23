%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2062+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 160 expanded)
%              Number of clauses        :   29 (  60 expanded)
%              Number of leaves         :    6 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 856 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3,X4] :
          ( ( r1_tarski(X2,X3)
            & r2_waybel_7(X1,X2,X4) )
         => r2_waybel_7(X1,X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow19)).

fof(d5_waybel_7,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( r2_waybel_7(X1,X2,X3)
        <=> ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X4,X1)
                  & r2_hidden(X3,X4) )
               => r2_hidden(X4,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_7)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2,X3,X4] :
            ( ( r1_tarski(X2,X3)
              & r2_waybel_7(X1,X2,X4) )
           => r2_waybel_7(X1,X3,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t22_yellow19])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_waybel_7(X5,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v3_pre_topc(X8,X5)
        | ~ r2_hidden(X7,X8)
        | r2_hidden(X8,X6)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_3(X5,X9,X10),k1_zfmisc_1(u1_struct_0(X5)))
        | r2_waybel_7(X5,X9,X10)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v3_pre_topc(esk1_3(X5,X9,X10),X5)
        | r2_waybel_7(X5,X9,X10)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(X10,esk1_3(X5,X9,X10))
        | r2_waybel_7(X5,X9,X10)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X9,X10),X9)
        | r2_waybel_7(X5,X9,X10)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & r2_waybel_7(esk2_0,esk3_0,esk5_0)
    & ~ r2_waybel_7(esk2_0,esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( r2_hidden(X4,X2)
    | ~ r2_waybel_7(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | r2_waybel_7(esk2_0,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk2_0,X1,X2),esk2_0)
    | r2_waybel_7(esk2_0,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_11])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | r2_waybel_7(X2,X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_18,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,X1,X2),X3)
    | r2_waybel_7(esk2_0,X1,X2)
    | ~ r2_hidden(X4,esk1_3(esk2_0,X1,X2))
    | ~ r2_waybel_7(esk2_0,X3,X4) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_10]),c_0_11])]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X2,X1))
    | r2_waybel_7(esk2_0,X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_11])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,X1,X2),X3)
    | r2_waybel_7(esk2_0,X1,X2)
    | ~ r2_waybel_7(esk2_0,X3,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_waybel_7(esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_27,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,X13)
      | v1_xboole_0(X13)
      | r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,X1,esk5_0),esk3_0)
    | r2_waybel_7(esk2_0,X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk5_0),esk4_0)
    | r2_waybel_7(esk2_0,X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( r2_waybel_7(X1,X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | r2_hidden(esk1_3(esk2_0,X1,esk5_0),esk4_0)
    | r2_waybel_7(esk2_0,X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_waybel_7(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_10]),c_0_11])]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_40,negated_conjecture,
    ( r2_waybel_7(esk2_0,X1,esk5_0) ),
    inference(sr,[status(thm)],[c_0_29,c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_40])]),
    [proof]).

%------------------------------------------------------------------------------
