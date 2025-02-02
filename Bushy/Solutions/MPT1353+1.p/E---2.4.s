%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t78_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:44 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 156 expanded)
%              Number of clauses        :   29 (  59 expanded)
%              Number of leaves         :    5 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 688 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t78_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> r1_tarski(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t78_tops_2.p',t78_tops_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t78_tops_2.p',d3_tarski)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t78_tops_2.p',d1_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t78_tops_2.p',t4_subset)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t78_tops_2.p',d5_pre_topc)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_tops_2(X2,X1)
            <=> r1_tarski(X2,u1_pre_topc(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t78_tops_2])).

fof(c_0_6,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk4_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk4_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & ( ~ v1_tops_2(esk2_0,esk1_0)
      | ~ r1_tarski(esk2_0,u1_pre_topc(esk1_0)) )
    & ( v1_tops_2(esk2_0,esk1_0)
      | r1_tarski(esk2_0,u1_pre_topc(esk1_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_tops_2(X9,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ r2_hidden(X10,X9)
        | v3_pre_topc(X10,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk3_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))
        | v1_tops_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(esk3_2(X8,X9),X9)
        | v1_tops_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ l1_pre_topc(X8) )
      & ( ~ v3_pre_topc(esk3_2(X8,X9),X8)
        | v1_tops_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_9,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | m1_subset_1(X32,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_tops_2(esk2_0,esk1_0)
    | r1_tarski(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X18,X19] :
      ( ( ~ v3_pre_topc(X19,X18)
        | r2_hidden(X19,u1_pre_topc(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( ~ r2_hidden(X19,u1_pre_topc(X18))
        | v3_pre_topc(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk1_0))
    | v1_tops_2(esk2_0,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk3_2(esk1_0,esk2_0),esk2_0)
    | v1_tops_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_21,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_tops_2(esk2_0,esk1_0)
    | m1_subset_1(esk3_2(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_13]),c_0_14])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_2(esk1_0,esk2_0),u1_pre_topc(esk1_0))
    | v1_tops_2(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_tops_2(esk2_0,esk1_0)
    | ~ v3_pre_topc(esk3_2(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_13]),c_0_14])])).

cnf(c_0_27,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ v1_tops_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_13]),c_0_14])])).

cnf(c_0_28,negated_conjecture,
    ( v1_tops_2(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_14])]),c_0_25]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_30,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | m1_subset_1(esk4_2(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( v3_pre_topc(esk4_2(esk2_0,X1),esk1_0)
    | r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_tops_2(esk2_0,esk1_0)
    | ~ r1_tarski(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_2(esk2_0,X1),u1_pre_topc(esk1_0))
    | r1_tarski(esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_14])]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_28])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
