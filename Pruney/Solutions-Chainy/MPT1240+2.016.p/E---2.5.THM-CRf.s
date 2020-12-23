%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:00 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 744 expanded)
%              Number of clauses        :   56 ( 261 expanded)
%              Number of leaves         :   12 ( 180 expanded)
%              Depth                    :   17
%              Number of atoms          :  284 (4961 expanded)
%              Number of equality atoms :   16 (  38 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t54_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,k1_tops_1(X1,X3))
          <=> ? [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                & v3_pre_topc(X4,X1)
                & r1_tarski(X4,X3)
                & r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

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

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_hidden(X2,k1_tops_1(X1,X3))
            <=> ? [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                  & v3_pre_topc(X4,X1)
                  & r1_tarski(X4,X3)
                  & r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t54_tops_1])).

fof(c_0_13,negated_conjecture,(
    ! [X32] :
      ( v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ v3_pre_topc(X32,esk1_0)
        | ~ r1_tarski(X32,esk3_0)
        | ~ r2_hidden(esk2_0,X32) )
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( v3_pre_topc(esk4_0,esk1_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( r1_tarski(esk4_0,esk3_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( r2_hidden(esk2_0,esk4_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | v3_pre_topc(k1_tops_1(X20,X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_17])).

fof(c_0_23,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_24,plain,(
    ! [X26,X27,X28] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ r1_tarski(X27,X28)
      | r1_tarski(k1_tops_1(X26,X27),k1_tops_1(X26,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_27,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | r1_tarski(k1_tops_1(X24,X25),X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_26])])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(k1_tops_1(X18,X19),k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_26])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k1_tops_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_21]),c_0_26])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_21]),c_0_26])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_21])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_21]),c_0_26])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_21]),c_0_26])])).

fof(c_0_42,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | k1_tops_1(X16,X17) = k3_subset_1(u1_struct_0(X16),k2_pre_topc(X16,k3_subset_1(u1_struct_0(X16),X17))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

fof(c_0_43,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k3_subset_1(X12,k3_subset_1(X12,X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_44,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_45,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_47,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_50,plain,(
    ! [X14,X15] :
      ( ( ~ v4_pre_topc(X15,X14)
        | k2_pre_topc(X14,X15) = X15
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( ~ v2_pre_topc(X14)
        | k2_pre_topc(X14,X15) != X15
        | v4_pre_topc(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_51,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_tops_1(X1,k1_tops_1(esk1_0,esk4_0)),k1_tops_1(esk1_0,esk3_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk4_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

fof(c_0_53,plain,(
    ! [X8,X9] :
      ( ( ~ r1_tarski(k1_tarski(X8),X9)
        | r2_hidden(X8,X9) )
      & ( ~ r2_hidden(X8,X9)
        | r1_tarski(k1_tarski(X8),X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_54,plain,
    ( k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2)) = k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_55,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_37]),c_0_21])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk4_0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k1_tops_1(X2,k1_tops_1(esk1_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_52])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),X2)
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_61,plain,(
    ! [X22,X23] :
      ( ( ~ v3_pre_topc(X23,X22)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X22),X23),X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X22),X23),X22)
        | v3_pre_topc(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

cnf(c_0_62,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k1_tarski(X1),k1_tops_1(esk1_0,esk3_0))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk4_0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,k1_tops_1(X2,k1_tops_1(esk1_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_48]),c_0_49])).

cnf(c_0_66,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_45]),c_0_26])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k1_tarski(X1),k1_tops_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_37]),c_0_21]),c_0_40])])).

cnf(c_0_71,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_32]),c_0_21]),c_0_26])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_57]),c_0_26])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_21]),c_0_40])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_32]),c_0_21]),c_0_26])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_37]),c_0_21]),c_0_26])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_77]),c_0_78])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_72]),c_0_40]),c_0_78]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:18:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.027 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t54_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 0.19/0.45  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.19/0.45  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.45  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.19/0.45  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.19/0.45  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.19/0.45  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 0.19/0.45  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.45  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.45  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.19/0.45  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.45  fof(t30_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 0.19/0.45  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t54_tops_1])).
% 0.19/0.45  fof(c_0_13, negated_conjecture, ![X32]:((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X32,esk1_0)|~r1_tarski(X32,esk3_0)|~r2_hidden(esk2_0,X32)))&((((m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)))&(v3_pre_topc(esk4_0,esk1_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))&(r1_tarski(esk4_0,esk3_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))&(r2_hidden(esk2_0,esk4_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])])).
% 0.19/0.45  cnf(c_0_14, negated_conjecture, (~r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk3_0)|~r2_hidden(esk2_0,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  fof(c_0_16, plain, ![X20, X21]:(~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|v3_pre_topc(k1_tops_1(X20,X21),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.19/0.45  cnf(c_0_17, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.45  cnf(c_0_19, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_22, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_17])).
% 0.19/0.45  fof(c_0_23, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.45  fof(c_0_24, plain, ![X26, X27, X28]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~r1_tarski(X27,X28)|r1_tarski(k1_tops_1(X26,X27),k1_tops_1(X26,X28)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.19/0.45  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])])).
% 0.19/0.45  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  fof(c_0_27, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|r1_tarski(k1_tops_1(X24,X25),X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.19/0.45  cnf(c_0_28, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_20]), c_0_21])])).
% 0.19/0.45  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.45  cnf(c_0_30, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_15]), c_0_26])])).
% 0.19/0.45  cnf(c_0_32, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.45  fof(c_0_33, plain, ![X18, X19]:(~l1_pre_topc(X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|m1_subset_1(k1_tops_1(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.19/0.45  cnf(c_0_34, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_17]), c_0_26])])).
% 0.19/0.45  cnf(c_0_35, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k1_tops_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.45  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_21]), c_0_26])])).
% 0.19/0.45  cnf(c_0_37, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  cnf(c_0_38, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_32]), c_0_21]), c_0_26])])).
% 0.19/0.45  cnf(c_0_39, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k1_tops_1(esk1_0,X2))|~r1_tarski(X2,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_26]), c_0_21])])).
% 0.19/0.45  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_21]), c_0_26])])).
% 0.19/0.45  cnf(c_0_41, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_37]), c_0_21]), c_0_26])])).
% 0.19/0.45  fof(c_0_42, plain, ![X16, X17]:(~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|k1_tops_1(X16,X17)=k3_subset_1(u1_struct_0(X16),k2_pre_topc(X16,k3_subset_1(u1_struct_0(X16),X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.19/0.45  fof(c_0_43, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k3_subset_1(X12,k3_subset_1(X12,X13))=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.45  fof(c_0_44, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.45  cnf(c_0_45, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_46, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.19/0.45  cnf(c_0_47, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.45  cnf(c_0_48, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.45  cnf(c_0_49, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.45  fof(c_0_50, plain, ![X14, X15]:((~v4_pre_topc(X15,X14)|k2_pre_topc(X14,X15)=X15|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(~v2_pre_topc(X14)|k2_pre_topc(X14,X15)!=X15|v4_pre_topc(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.19/0.45  cnf(c_0_51, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_45])).
% 0.19/0.45  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_tops_1(X1,k1_tops_1(esk1_0,esk4_0)),k1_tops_1(esk1_0,esk3_0))|~l1_pre_topc(X1)|~m1_subset_1(k1_tops_1(esk1_0,esk4_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 0.19/0.45  fof(c_0_53, plain, ![X8, X9]:((~r1_tarski(k1_tarski(X8),X9)|r2_hidden(X8,X9))&(~r2_hidden(X8,X9)|r1_tarski(k1_tarski(X8),X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.45  cnf(c_0_54, plain, (k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))=k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.19/0.45  cnf(c_0_55, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.45  cnf(c_0_56, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_37]), c_0_21])])).
% 0.19/0.46  cnf(c_0_57, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.46  cnf(c_0_58, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))|~l1_pre_topc(X2)|~m1_subset_1(k1_tops_1(esk1_0,esk4_0),k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k1_tops_1(X2,k1_tops_1(esk1_0,esk4_0)))), inference(spm,[status(thm)],[c_0_29, c_0_52])).
% 0.19/0.46  cnf(c_0_59, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.46  cnf(c_0_60, plain, (k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))=k3_subset_1(u1_struct_0(X1),X2)|~v4_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.46  fof(c_0_61, plain, ![X22, X23]:((~v3_pre_topc(X23,X22)|v4_pre_topc(k3_subset_1(u1_struct_0(X22),X23),X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(~v4_pre_topc(k3_subset_1(u1_struct_0(X22),X23),X22)|v3_pre_topc(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).
% 0.19/0.46  cnf(c_0_62, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_19]), c_0_20]), c_0_21])])).
% 0.19/0.46  cnf(c_0_63, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_57])).
% 0.19/0.46  cnf(c_0_64, negated_conjecture, (r1_tarski(k1_tarski(X1),k1_tops_1(esk1_0,esk3_0))|~l1_pre_topc(X2)|~m1_subset_1(k1_tops_1(esk1_0,esk4_0),k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,k1_tops_1(X2,k1_tops_1(esk1_0,esk4_0)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.46  cnf(c_0_65, plain, (k1_tops_1(X1,X2)=X2|~v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_48]), c_0_49])).
% 0.19/0.46  cnf(c_0_66, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.46  cnf(c_0_67, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_45]), c_0_26])])).
% 0.19/0.46  cnf(c_0_68, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_19]), c_0_20]), c_0_21])])).
% 0.19/0.46  cnf(c_0_69, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.46  cnf(c_0_70, negated_conjecture, (r1_tarski(k1_tarski(X1),k1_tops_1(esk1_0,esk3_0))|~r2_hidden(X1,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_37]), c_0_21]), c_0_40])])).
% 0.19/0.46  cnf(c_0_71, plain, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.46  cnf(c_0_72, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_32]), c_0_21]), c_0_26])])).
% 0.19/0.46  cnf(c_0_73, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_57]), c_0_26])])).
% 0.19/0.46  cnf(c_0_74, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))|~r2_hidden(X1,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk4_0)))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.46  cnf(c_0_75, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_21]), c_0_40])])).
% 0.19/0.46  cnf(c_0_76, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_32]), c_0_21]), c_0_26])])).
% 0.19/0.46  cnf(c_0_77, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_75])).
% 0.19/0.46  cnf(c_0_78, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_37]), c_0_21]), c_0_26])])).
% 0.19/0.46  cnf(c_0_79, negated_conjecture, (~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_77]), c_0_78])])).
% 0.19/0.46  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_72]), c_0_40]), c_0_78]), c_0_41])]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 81
% 0.19/0.46  # Proof object clause steps            : 56
% 0.19/0.46  # Proof object formula steps           : 25
% 0.19/0.46  # Proof object conjectures             : 42
% 0.19/0.46  # Proof object clause conjectures      : 39
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 20
% 0.19/0.46  # Proof object initial formulas used   : 12
% 0.19/0.46  # Proof object generating inferences   : 35
% 0.19/0.46  # Proof object simplifying inferences  : 63
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 12
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 22
% 0.19/0.46  # Removed in clause preprocessing      : 0
% 0.19/0.46  # Initial clauses in saturation        : 22
% 0.19/0.46  # Processed clauses                    : 691
% 0.19/0.46  # ...of these trivial                  : 5
% 0.19/0.46  # ...subsumed                          : 286
% 0.19/0.46  # ...remaining for further processing  : 400
% 0.19/0.46  # Other redundant clauses eliminated   : 0
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 35
% 0.19/0.46  # Backward-rewritten                   : 151
% 0.19/0.46  # Generated clauses                    : 1809
% 0.19/0.46  # ...of the previous two non-trivial   : 1817
% 0.19/0.46  # Contextual simplify-reflections      : 20
% 0.19/0.46  # Paramodulations                      : 1809
% 0.19/0.46  # Factorizations                       : 0
% 0.19/0.46  # Equation resolutions                 : 0
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 192
% 0.19/0.46  #    Positive orientable unit clauses  : 11
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 0
% 0.19/0.46  #    Non-unit-clauses                  : 181
% 0.19/0.46  # Current number of unprocessed clauses: 1141
% 0.19/0.46  # ...number of literals in the above   : 6868
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 208
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 30506
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 5770
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 340
% 0.19/0.46  # Unit Clause-clause subsumption calls : 249
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 8
% 0.19/0.46  # BW rewrite match successes           : 6
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 56740
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.113 s
% 0.19/0.46  # System time              : 0.007 s
% 0.19/0.46  # Total time               : 0.120 s
% 0.19/0.46  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
