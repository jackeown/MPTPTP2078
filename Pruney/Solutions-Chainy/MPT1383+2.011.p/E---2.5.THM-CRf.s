%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:28 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   66 (1055 expanded)
%              Number of clauses        :   47 ( 358 expanded)
%              Number of leaves         :    9 ( 251 expanded)
%              Depth                    :   15
%              Number of atoms          :  244 (8767 expanded)
%              Number of equality atoms :   11 (  38 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & r1_tarski(X4,X3)
                    & r2_hidden(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( m1_connsp_2(X3,X1,X2)
                <=> ? [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                      & v3_pre_topc(X4,X1)
                      & r1_tarski(X4,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_connsp_2])).

fof(c_0_10,plain,(
    ! [X23,X24,X25] :
      ( ( ~ m1_connsp_2(X25,X23,X24)
        | r2_hidden(X24,k1_tops_1(X23,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ r2_hidden(X24,k1_tops_1(X23,X25))
        | m1_connsp_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X29] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( ~ m1_connsp_2(esk3_0,esk1_0,esk2_0)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ v3_pre_topc(X29,esk1_0)
        | ~ r1_tarski(X29,esk3_0)
        | ~ r2_hidden(esk2_0,X29) )
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | m1_connsp_2(esk3_0,esk1_0,esk2_0) )
      & ( v3_pre_topc(esk4_0,esk1_0)
        | m1_connsp_2(esk3_0,esk1_0,esk2_0) )
      & ( r1_tarski(esk4_0,esk3_0)
        | m1_connsp_2(esk3_0,esk1_0,esk2_0) )
      & ( r2_hidden(esk2_0,esk4_0)
        | m1_connsp_2(esk3_0,esk1_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | v3_pre_topc(k1_tops_1(X12,X13),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | r1_tarski(k1_tops_1(X14,X15),X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | m1_subset_1(k1_tops_1(X10,X11),k1_zfmisc_1(u1_struct_0(X10))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_20,negated_conjecture,
    ( ~ m1_connsp_2(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ m1_connsp_2(X1,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

fof(c_0_26,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ v3_pre_topc(X22,X20)
        | k1_tops_1(X20,X22) = X22
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( k1_tops_1(X19,X21) != X21
        | v3_pre_topc(X21,X19)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X16,X17,X18] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ r1_tarski(X17,X18)
      | r1_tarski(k1_tops_1(X16,X17),k1_tops_1(X16,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_16]),c_0_17])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_17])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_23])])).

cnf(c_0_34,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_17])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_27]),c_0_23])])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23]),c_0_16]),c_0_17])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_32])]),c_0_36])]),c_0_37])).

fof(c_0_42,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_23]),c_0_17])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_36])])).

cnf(c_0_45,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0
    | ~ v3_pre_topc(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_17])])).

cnf(c_0_46,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_47,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk4_0),k1_tops_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_41])])).

cnf(c_0_50,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0
    | m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk4_0),k1_zfmisc_1(k1_tops_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_50]),c_0_23])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_31]),c_0_32]),c_0_36])]),c_0_54])).

cnf(c_0_57,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( m1_connsp_2(X1,esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( m1_connsp_2(esk3_0,esk1_0,esk2_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_23])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_62]),c_0_23])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_31]),c_0_32]),c_0_64]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n003.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 09:48:42 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.17/0.31  # No SInE strategy applied
% 0.17/0.31  # Trying AutoSched0 for 299 seconds
% 0.17/0.35  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.17/0.35  # and selection function SelectNewComplexAHP.
% 0.17/0.35  #
% 0.17/0.35  # Preprocessing time       : 0.027 s
% 0.17/0.35  # Presaturation interreduction done
% 0.17/0.35  
% 0.17/0.35  # Proof found!
% 0.17/0.35  # SZS status Theorem
% 0.17/0.35  # SZS output start CNFRefutation
% 0.17/0.35  fof(t8_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 0.17/0.35  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.17/0.35  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.17/0.35  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.17/0.35  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.17/0.35  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 0.17/0.35  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.17/0.35  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.17/0.35  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.17/0.35  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))))), inference(assume_negation,[status(cth)],[t8_connsp_2])).
% 0.17/0.35  fof(c_0_10, plain, ![X23, X24, X25]:((~m1_connsp_2(X25,X23,X24)|r2_hidden(X24,k1_tops_1(X23,X25))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~r2_hidden(X24,k1_tops_1(X23,X25))|m1_connsp_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.17/0.35  fof(c_0_11, negated_conjecture, ![X29]:(((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~m1_connsp_2(esk3_0,esk1_0,esk2_0)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X29,esk1_0)|~r1_tarski(X29,esk3_0)|~r2_hidden(esk2_0,X29)))&((((m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|m1_connsp_2(esk3_0,esk1_0,esk2_0))&(v3_pre_topc(esk4_0,esk1_0)|m1_connsp_2(esk3_0,esk1_0,esk2_0)))&(r1_tarski(esk4_0,esk3_0)|m1_connsp_2(esk3_0,esk1_0,esk2_0)))&(r2_hidden(esk2_0,esk4_0)|m1_connsp_2(esk3_0,esk1_0,esk2_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).
% 0.17/0.35  fof(c_0_12, plain, ![X12, X13]:(~v2_pre_topc(X12)|~l1_pre_topc(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|v3_pre_topc(k1_tops_1(X12,X13),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.17/0.35  fof(c_0_13, plain, ![X14, X15]:(~l1_pre_topc(X14)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|r1_tarski(k1_tops_1(X14,X15),X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.17/0.35  cnf(c_0_14, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  fof(c_0_19, plain, ![X10, X11]:(~l1_pre_topc(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|m1_subset_1(k1_tops_1(X10,X11),k1_zfmisc_1(u1_struct_0(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.17/0.35  cnf(c_0_20, negated_conjecture, (~m1_connsp_2(esk3_0,esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk3_0)|~r2_hidden(esk2_0,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_21, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_22, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.35  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_24, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.35  cnf(c_0_25, negated_conjecture, (r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~m1_connsp_2(X1,esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.17/0.35  fof(c_0_26, plain, ![X19, X20, X21, X22]:((~v3_pre_topc(X22,X20)|k1_tops_1(X20,X22)=X22|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X20)|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(k1_tops_1(X19,X21)!=X21|v3_pre_topc(X21,X19)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X20)|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.17/0.35  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_28, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.35  fof(c_0_29, plain, ![X16, X17, X18]:(~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|(~r1_tarski(X17,X18)|r1_tarski(k1_tops_1(X16,X17),k1_tops_1(X16,X18)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.17/0.35  cnf(c_0_30, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk3_0)|~r2_hidden(esk2_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.17/0.35  cnf(c_0_31, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_16]), c_0_17])])).
% 0.17/0.35  cnf(c_0_32, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_23]), c_0_17])])).
% 0.17/0.35  cnf(c_0_33, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_23])])).
% 0.17/0.35  cnf(c_0_34, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.17/0.35  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk3_0)|~r2_hidden(esk2_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_20, c_0_27])).
% 0.17/0.35  cnf(c_0_36, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_17])])).
% 0.17/0.35  cnf(c_0_37, negated_conjecture, (r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))|m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_27]), c_0_23])])).
% 0.17/0.35  cnf(c_0_38, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.17/0.35  cnf(c_0_39, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_33])).
% 0.17/0.35  cnf(c_0_40, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_23]), c_0_16]), c_0_17])])).
% 0.17/0.35  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_31]), c_0_32])]), c_0_36])]), c_0_37])).
% 0.17/0.35  fof(c_0_42, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.17/0.35  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk3_0))|~r1_tarski(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_23]), c_0_17])])).
% 0.17/0.35  cnf(c_0_44, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_36])])).
% 0.17/0.35  cnf(c_0_45, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0|~v3_pre_topc(esk4_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_17])])).
% 0.17/0.35  cnf(c_0_46, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  fof(c_0_47, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.17/0.35  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.17/0.35  cnf(c_0_49, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk4_0),k1_tops_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_41])])).
% 0.17/0.35  cnf(c_0_50, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0|m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.17/0.35  cnf(c_0_51, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.17/0.35  cnf(c_0_52, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk4_0),k1_zfmisc_1(k1_tops_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.17/0.35  cnf(c_0_53, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0|~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk3_0)|~r2_hidden(esk2_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_20, c_0_50])).
% 0.17/0.35  cnf(c_0_54, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_50]), c_0_23])])).
% 0.17/0.35  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))|~r2_hidden(X1,k1_tops_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.17/0.35  cnf(c_0_56, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_31]), c_0_32]), c_0_36])]), c_0_54])).
% 0.17/0.35  cnf(c_0_57, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_58, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.17/0.35  cnf(c_0_59, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_60, negated_conjecture, (m1_connsp_2(X1,esk1_0,esk2_0)|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.17/0.35  cnf(c_0_61, negated_conjecture, (m1_connsp_2(esk3_0,esk1_0,esk2_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.17/0.35  cnf(c_0_62, negated_conjecture, (m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_23])])).
% 0.17/0.35  cnf(c_0_63, negated_conjecture, (~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk3_0)|~r2_hidden(esk2_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_62])])).
% 0.17/0.35  cnf(c_0_64, negated_conjecture, (r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_62]), c_0_23])])).
% 0.17/0.35  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_31]), c_0_32]), c_0_64]), c_0_36])]), ['proof']).
% 0.17/0.35  # SZS output end CNFRefutation
% 0.17/0.35  # Proof object total steps             : 66
% 0.17/0.35  # Proof object clause steps            : 47
% 0.17/0.35  # Proof object formula steps           : 19
% 0.17/0.35  # Proof object conjectures             : 41
% 0.17/0.35  # Proof object clause conjectures      : 38
% 0.17/0.35  # Proof object formula conjectures     : 3
% 0.17/0.35  # Proof object initial clauses used    : 19
% 0.17/0.35  # Proof object initial formulas used   : 9
% 0.17/0.35  # Proof object generating inferences   : 25
% 0.17/0.35  # Proof object simplifying inferences  : 55
% 0.17/0.35  # Training examples: 0 positive, 0 negative
% 0.17/0.35  # Parsed axioms                        : 9
% 0.17/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.35  # Initial clauses                      : 21
% 0.17/0.35  # Removed in clause preprocessing      : 0
% 0.17/0.35  # Initial clauses in saturation        : 21
% 0.17/0.35  # Processed clauses                    : 134
% 0.17/0.35  # ...of these trivial                  : 7
% 0.17/0.35  # ...subsumed                          : 10
% 0.17/0.35  # ...remaining for further processing  : 117
% 0.17/0.35  # Other redundant clauses eliminated   : 0
% 0.17/0.35  # Clauses deleted for lack of memory   : 0
% 0.17/0.35  # Backward-subsumed                    : 2
% 0.17/0.35  # Backward-rewritten                   : 40
% 0.17/0.35  # Generated clauses                    : 122
% 0.17/0.35  # ...of the previous two non-trivial   : 110
% 0.17/0.35  # Contextual simplify-reflections      : 3
% 0.17/0.35  # Paramodulations                      : 122
% 0.17/0.35  # Factorizations                       : 0
% 0.17/0.35  # Equation resolutions                 : 0
% 0.17/0.35  # Propositional unsat checks           : 0
% 0.17/0.35  #    Propositional check models        : 0
% 0.17/0.35  #    Propositional check unsatisfiable : 0
% 0.17/0.35  #    Propositional clauses             : 0
% 0.17/0.35  #    Propositional clauses after purity: 0
% 0.17/0.35  #    Propositional unsat core size     : 0
% 0.17/0.35  #    Propositional preprocessing time  : 0.000
% 0.17/0.35  #    Propositional encoding time       : 0.000
% 0.17/0.35  #    Propositional solver time         : 0.000
% 0.17/0.35  #    Success case prop preproc time    : 0.000
% 0.17/0.35  #    Success case prop encoding time   : 0.000
% 0.17/0.35  #    Success case prop solver time     : 0.000
% 0.17/0.35  # Current number of processed clauses  : 54
% 0.17/0.35  #    Positive orientable unit clauses  : 28
% 0.17/0.35  #    Positive unorientable unit clauses: 0
% 0.17/0.35  #    Negative unit clauses             : 1
% 0.17/0.35  #    Non-unit-clauses                  : 25
% 0.17/0.35  # Current number of unprocessed clauses: 11
% 0.17/0.35  # ...number of literals in the above   : 19
% 0.17/0.35  # Current number of archived formulas  : 0
% 0.17/0.35  # Current number of archived clauses   : 63
% 0.17/0.35  # Clause-clause subsumption calls (NU) : 573
% 0.17/0.35  # Rec. Clause-clause subsumption calls : 295
% 0.17/0.35  # Non-unit clause-clause subsumptions  : 14
% 0.17/0.35  # Unit Clause-clause subsumption calls : 82
% 0.17/0.35  # Rewrite failures with RHS unbound    : 0
% 0.17/0.35  # BW rewrite match attempts            : 10
% 0.17/0.35  # BW rewrite match successes           : 9
% 0.17/0.35  # Condensation attempts                : 0
% 0.17/0.35  # Condensation successes               : 0
% 0.17/0.35  # Termbank termtop insertions          : 4367
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.032 s
% 0.17/0.35  # System time              : 0.005 s
% 0.17/0.35  # Total time               : 0.038 s
% 0.17/0.35  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
