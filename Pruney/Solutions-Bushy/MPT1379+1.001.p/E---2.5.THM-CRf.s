%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1379+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 658 expanded)
%              Number of clauses        :   49 ( 241 expanded)
%              Number of leaves         :    7 ( 156 expanded)
%              Depth                    :   13
%              Number of atoms          :  201 (4208 expanded)
%              Number of equality atoms :   20 ( 145 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( m1_connsp_2(X3,X1,X2)
                      & m1_connsp_2(X4,X1,X2) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X1),X3,X4),X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t46_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => k9_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)) = k1_tops_1(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( m1_connsp_2(X3,X1,X2)
                        & m1_connsp_2(X4,X1,X2) )
                    <=> m1_connsp_2(k9_subset_1(u1_struct_0(X1),X3,X4),X1,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_connsp_2])).

fof(c_0_8,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | m1_subset_1(k1_tops_1(X22,X23),k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ m1_connsp_2(esk4_0,esk2_0,esk3_0)
      | ~ m1_connsp_2(esk5_0,esk2_0,esk3_0)
      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),esk2_0,esk3_0) )
    & ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
      | m1_connsp_2(k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),esk2_0,esk3_0) )
    & ( m1_connsp_2(esk5_0,esk2_0,esk3_0)
      | m1_connsp_2(k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

fof(c_0_10,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X27))
      | k9_subset_1(X27,X28,X29) = k3_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_11,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X24))
      | m1_subset_1(k9_subset_1(X24,X25,X26),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_12,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X30,X31,X32] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
      | k9_subset_1(u1_struct_0(X30),k1_tops_1(X30,X31),k1_tops_1(X30,X32)) = k1_tops_1(X30,k9_subset_1(u1_struct_0(X30),X31,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_tops_1])])])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

fof(c_0_19,plain,(
    ! [X10,X11,X12] :
      ( ( ~ m1_connsp_2(X12,X10,X11)
        | r2_hidden(X11,k1_tops_1(X10,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(X11,k1_tops_1(X10,X12))
        | m1_connsp_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_20,negated_conjecture,
    ( m1_connsp_2(esk5_0,esk2_0,esk3_0)
    | m1_connsp_2(k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),X1,esk5_0) = k3_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_23,plain,
    ( k9_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)) = k1_tops_1(X1,k9_subset_1(u1_struct_0(X1),X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),X1,k1_tops_1(esk2_0,esk5_0)) = k3_xboole_0(X1,k1_tops_1(esk2_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_18])).

fof(c_0_26,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk1_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk1_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk1_3(X18,X19,X20),X18)
        | r2_hidden(esk1_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk1_3(X18,X19,X20),X19)
        | r2_hidden(esk1_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_connsp_2(k3_xboole_0(esk4_0,esk5_0),esk2_0,esk3_0)
    | m1_connsp_2(esk5_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( k1_tops_1(esk2_0,k3_xboole_0(X1,esk5_0)) = k3_xboole_0(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_13]),c_0_21]),c_0_14]),c_0_24])]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | m1_connsp_2(k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,k3_xboole_0(esk4_0,esk5_0)))
    | m1_connsp_2(esk5_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_14]),c_0_24]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k1_tops_1(esk2_0,k3_xboole_0(esk4_0,esk5_0)) = k3_xboole_0(k1_tops_1(esk2_0,esk4_0),k1_tops_1(esk2_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_connsp_2(X1,esk2_0,esk3_0)
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_14]),c_0_24])]),c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( m1_connsp_2(k3_xboole_0(esk4_0,esk5_0),esk2_0,esk3_0)
    | m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_21])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(k1_tops_1(esk2_0,esk4_0),k1_tops_1(esk2_0,esk5_0)))
    | m1_connsp_2(esk5_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_connsp_2(esk5_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_13])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,k3_xboole_0(esk4_0,esk5_0)))
    | m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_40]),c_0_14]),c_0_24]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( m1_connsp_2(esk5_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(k1_tops_1(esk2_0,esk4_0),k1_tops_1(esk2_0,esk5_0)))
    | m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | ~ m1_connsp_2(esk5_0,esk2_0,esk3_0)
    | ~ m1_connsp_2(k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_47]),c_0_14]),c_0_24]),c_0_13]),c_0_30])]),c_0_31])).

cnf(c_0_54,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( ~ m1_connsp_2(k3_xboole_0(esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | ~ m1_connsp_2(esk5_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( m1_connsp_2(k3_xboole_0(X1,esk5_0),esk2_0,esk3_0)
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,k3_xboole_0(X1,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(X1,k1_tops_1(esk2_0,esk5_0)))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_54]),c_0_14]),c_0_24]),c_0_33]),c_0_30])]),c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_connsp_2(k3_xboole_0(esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_47])])).

cnf(c_0_60,negated_conjecture,
    ( m1_connsp_2(k3_xboole_0(esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ r2_hidden(esk3_0,k3_xboole_0(k1_tops_1(esk2_0,esk4_0),k1_tops_1(esk2_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(k1_tops_1(esk2_0,esk4_0),k1_tops_1(esk2_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_connsp_2(k3_xboole_0(esk4_0,esk5_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_54])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])]),c_0_62]),
    [proof]).

%------------------------------------------------------------------------------
