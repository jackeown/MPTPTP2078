%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:00 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  107 (1616 expanded)
%              Number of clauses        :   78 ( 614 expanded)
%              Number of leaves         :   14 ( 392 expanded)
%              Depth                    :   21
%              Number of atoms          :  334 (9552 expanded)
%              Number of equality atoms :   19 ( 104 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

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

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

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

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_14,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_16,negated_conjecture,(
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

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,(
    ! [X36] :
      ( v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ v3_pre_topc(X36,esk1_0)
        | ~ r1_tarski(X36,esk3_0)
        | ~ r2_hidden(esk2_0,X36) )
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( v3_pre_topc(esk4_0,esk1_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( r1_tarski(esk4_0,esk3_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( r2_hidden(esk2_0,esk4_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X24,X25] :
      ( ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | v3_pre_topc(k1_tops_1(X24,X25),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

fof(c_0_34,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | r1_tarski(k1_tops_1(X28,X29),X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_21])])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_38,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_39,plain,(
    ! [X30,X31,X32] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ r1_tarski(X31,X32)
      | r1_tarski(k1_tops_1(X30,X31),k1_tops_1(X30,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_30]),c_0_21])])).

cnf(c_0_43,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k3_subset_1(X12,X13) = k4_xboole_0(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_21])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_48,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | k1_tops_1(X20,X21) = k3_subset_1(u1_struct_0(X20),k2_pre_topc(X20,k3_subset_1(u1_struct_0(X20),X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

fof(c_0_49,plain,(
    ! [X18,X19] :
      ( ( ~ v4_pre_topc(X19,X18)
        | k2_pre_topc(X18,X19) = X19
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( ~ v2_pre_topc(X18)
        | k2_pre_topc(X18,X19) != X19
        | v4_pre_topc(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_50,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_43])).

cnf(c_0_51,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_53,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | m1_subset_1(k1_tops_1(X22,X23),k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k1_tops_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_37]),c_0_30]),c_0_21])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_47])).

cnf(c_0_57,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_60,plain,(
    ! [X26,X27] :
      ( ( ~ v3_pre_topc(X27,X26)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X26),X27),X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X26),X27),X26)
        | v3_pre_topc(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_52])).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_63,plain,(
    ! [X10,X11] :
      ( ( ~ r1_tarski(k1_tarski(X10),X11)
        | r2_hidden(X10,X11) )
      & ( ~ r2_hidden(X10,X11)
        | r1_tarski(k1_tarski(X10),X11) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk4_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X2,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_30])]),c_0_56])).

fof(c_0_65,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | k3_subset_1(X14,k3_subset_1(X14,X15)) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_66,plain,
    ( k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)) = k1_tops_1(X1,X2)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_67,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_30])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_43])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X1,k1_tops_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_37])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X2,esk4_0)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_45]),c_0_30])]),c_0_56])).

cnf(c_0_73,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)) = k1_tops_1(X1,X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_18])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X1,k1_tops_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk4_0),k1_tops_1(esk1_0,esk4_0))
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_55])).

cnf(c_0_79,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_52]),c_0_21])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_51])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k1_tarski(X1),esk4_0)
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_55]),c_0_30])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk4_0),k1_tops_1(esk1_0,esk4_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(esk4_0,k1_tops_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_37])).

cnf(c_0_84,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_30]),c_0_55])])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_73]),c_0_59])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X2,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_21]),c_0_30])]),c_0_31])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk4_0),k1_tops_1(esk1_0,esk4_0))
    | ~ r1_tarski(esk4_0,k1_tops_1(esk1_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_31]),c_0_30]),c_0_42])])).

cnf(c_0_89,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_37]),c_0_30]),c_0_21])])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk4_0),k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(esk4_0,k1_tops_1(esk1_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_42])])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_89]),c_0_30]),c_0_55])])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_89]),c_0_89]),c_0_94])])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_96,c_0_89])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_tops_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_90]),c_0_21])])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_37]),c_0_30]),c_0_21])])).

cnf(c_0_104,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_102]),c_0_103])]),c_0_31])).

cnf(c_0_105,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_89]),c_0_29]),c_0_30]),c_0_55])])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_103]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.29  % Computer   : n020.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % WCLimit    : 600
% 0.10/0.29  % DateTime   : Tue Dec  1 15:05:52 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.10/0.29  # Version: 2.5pre002
% 0.10/0.29  # No SInE strategy applied
% 0.10/0.29  # Trying AutoSched0 for 299 seconds
% 0.46/0.63  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.46/0.63  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.46/0.63  #
% 0.46/0.63  # Preprocessing time       : 0.031 s
% 0.46/0.63  # Presaturation interreduction done
% 0.46/0.63  
% 0.46/0.63  # Proof found!
% 0.46/0.63  # SZS status Theorem
% 0.46/0.63  # SZS output start CNFRefutation
% 0.46/0.63  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.46/0.63  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.46/0.63  fof(t54_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 0.46/0.63  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.46/0.63  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.46/0.63  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.46/0.63  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.46/0.63  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.46/0.63  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 0.46/0.63  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.46/0.63  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.46/0.63  fof(t30_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 0.46/0.63  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.46/0.63  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.46/0.63  fof(c_0_14, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.46/0.63  fof(c_0_15, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.46/0.63  fof(c_0_16, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t54_tops_1])).
% 0.46/0.63  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.46/0.63  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.63  fof(c_0_19, negated_conjecture, ![X36]:((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X36,esk1_0)|~r1_tarski(X36,esk3_0)|~r2_hidden(esk2_0,X36)))&((((m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)))&(v3_pre_topc(esk4_0,esk1_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))&(r1_tarski(esk4_0,esk3_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))&(r2_hidden(esk2_0,esk4_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])])).
% 0.46/0.63  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.46/0.63  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.63  cnf(c_0_22, negated_conjecture, (~r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk3_0)|~r2_hidden(esk2_0,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.63  cnf(c_0_23, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.63  fof(c_0_24, plain, ![X24, X25]:(~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v3_pre_topc(k1_tops_1(X24,X25),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.46/0.63  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.63  cnf(c_0_26, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.46/0.63  cnf(c_0_27, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.46/0.63  cnf(c_0_28, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.63  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.63  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.63  cnf(c_0_31, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.46/0.63  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.63  cnf(c_0_33, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.46/0.63  fof(c_0_34, plain, ![X28, X29]:(~l1_pre_topc(X28)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|r1_tarski(k1_tops_1(X28,X29),X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.46/0.63  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_32])).
% 0.46/0.63  cnf(c_0_36, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_21])])).
% 0.46/0.63  cnf(c_0_37, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.46/0.63  fof(c_0_38, plain, ![X8, X9]:r1_tarski(k4_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.46/0.63  fof(c_0_39, plain, ![X30, X31, X32]:(~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|(~r1_tarski(X31,X32)|r1_tarski(k1_tops_1(X30,X31),k1_tops_1(X30,X32)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.46/0.63  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.46/0.63  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk3_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_26])).
% 0.46/0.63  cnf(c_0_42, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_30]), c_0_21])])).
% 0.46/0.63  cnf(c_0_43, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.46/0.63  fof(c_0_44, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k3_subset_1(X12,X13)=k4_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.46/0.63  cnf(c_0_45, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.46/0.63  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_21])])).
% 0.46/0.63  cnf(c_0_47, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.46/0.63  fof(c_0_48, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|k1_tops_1(X20,X21)=k3_subset_1(u1_struct_0(X20),k2_pre_topc(X20,k3_subset_1(u1_struct_0(X20),X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.46/0.63  fof(c_0_49, plain, ![X18, X19]:((~v4_pre_topc(X19,X18)|k2_pre_topc(X18,X19)=X19|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(~v2_pre_topc(X18)|k2_pre_topc(X18,X19)!=X19|v4_pre_topc(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.46/0.63  cnf(c_0_50, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_43])).
% 0.46/0.63  cnf(c_0_51, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.46/0.63  cnf(c_0_52, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.63  fof(c_0_53, plain, ![X22, X23]:(~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|m1_subset_1(k1_tops_1(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.46/0.63  cnf(c_0_54, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k1_tops_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_17, c_0_45])).
% 0.46/0.63  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_37]), c_0_30]), c_0_21])])).
% 0.46/0.63  cnf(c_0_56, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_47])).
% 0.46/0.63  cnf(c_0_57, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.46/0.63  cnf(c_0_58, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.46/0.63  cnf(c_0_59, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.46/0.63  fof(c_0_60, plain, ![X26, X27]:((~v3_pre_topc(X27,X26)|v4_pre_topc(k3_subset_1(u1_struct_0(X26),X27),X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(~v4_pre_topc(k3_subset_1(u1_struct_0(X26),X27),X26)|v3_pre_topc(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).
% 0.46/0.63  cnf(c_0_61, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_52])).
% 0.46/0.63  cnf(c_0_62, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.46/0.63  fof(c_0_63, plain, ![X10, X11]:((~r1_tarski(k1_tarski(X10),X11)|r2_hidden(X10,X11))&(~r2_hidden(X10,X11)|r1_tarski(k1_tarski(X10),X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.46/0.63  cnf(c_0_64, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk4_0))|~r1_tarski(X1,k1_tops_1(esk1_0,X2))|~r1_tarski(X2,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_30])]), c_0_56])).
% 0.46/0.63  fof(c_0_65, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|k3_subset_1(X14,k3_subset_1(X14,X15))=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.46/0.63  cnf(c_0_66, plain, (k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))=k1_tops_1(X1,X2)|~v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.46/0.63  cnf(c_0_67, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.46/0.63  cnf(c_0_68, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_30])])).
% 0.46/0.63  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_17, c_0_43])).
% 0.46/0.63  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(X1,k1_tops_1(X3,X2))), inference(spm,[status(thm)],[c_0_17, c_0_37])).
% 0.46/0.63  cnf(c_0_71, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.46/0.63  cnf(c_0_72, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X2,esk4_0)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_45]), c_0_30])]), c_0_56])).
% 0.46/0.63  cnf(c_0_73, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.46/0.63  cnf(c_0_74, plain, (k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))=k1_tops_1(X1,X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.46/0.63  cnf(c_0_75, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_28]), c_0_29]), c_0_30])])).
% 0.46/0.63  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_69, c_0_18])).
% 0.46/0.63  cnf(c_0_77, plain, (r1_tarski(k1_tarski(X1),X2)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r2_hidden(X1,k1_tops_1(X3,X2))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.46/0.63  cnf(c_0_78, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk4_0),k1_tops_1(esk1_0,esk4_0))|~r1_tarski(X1,esk4_0)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_55])).
% 0.46/0.63  cnf(c_0_79, plain, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.46/0.63  cnf(c_0_80, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_52]), c_0_21])])).
% 0.46/0.63  cnf(c_0_81, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,X3)))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_76, c_0_51])).
% 0.46/0.63  cnf(c_0_82, negated_conjecture, (r1_tarski(k1_tarski(X1),esk4_0)|~r2_hidden(X1,k1_tops_1(esk1_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_55]), c_0_30])])).
% 0.46/0.63  cnf(c_0_83, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk4_0),k1_tops_1(esk1_0,esk4_0))|~l1_pre_topc(X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(esk4_0,k1_tops_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_78, c_0_37])).
% 0.46/0.63  cnf(c_0_84, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_30]), c_0_55])])).
% 0.46/0.63  cnf(c_0_85, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_73]), c_0_59])).
% 0.46/0.63  cnf(c_0_86, negated_conjecture, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(esk4_0))|~r2_hidden(X1,k1_tops_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_82])).
% 0.46/0.63  cnf(c_0_87, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))|~r1_tarski(X1,k1_tops_1(esk1_0,X2))|~r1_tarski(X2,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_21]), c_0_30])]), c_0_31])).
% 0.46/0.63  cnf(c_0_88, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk4_0),k1_tops_1(esk1_0,esk4_0))|~r1_tarski(esk4_0,k1_tops_1(esk1_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_31]), c_0_30]), c_0_42])])).
% 0.46/0.63  cnf(c_0_89, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_37]), c_0_30]), c_0_21])])).
% 0.46/0.63  cnf(c_0_90, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.63  cnf(c_0_91, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.46/0.63  cnf(c_0_92, negated_conjecture, (r1_tarski(k1_tarski(X1),X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_tops_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.46/0.63  cnf(c_0_93, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk4_0),k1_tops_1(esk1_0,esk3_0))|~r1_tarski(esk4_0,k1_tops_1(esk1_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_42])])).
% 0.46/0.63  cnf(c_0_94, negated_conjecture, (r1_tarski(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_89]), c_0_30]), c_0_55])])).
% 0.46/0.63  cnf(c_0_95, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_90])).
% 0.46/0.63  cnf(c_0_96, negated_conjecture, (r2_hidden(X1,X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_tops_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.46/0.63  cnf(c_0_97, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_89]), c_0_89]), c_0_94])])).
% 0.46/0.63  cnf(c_0_98, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.46/0.63  cnf(c_0_99, negated_conjecture, (r2_hidden(X1,X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(X2))|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[c_0_96, c_0_89])).
% 0.46/0.63  cnf(c_0_100, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_tops_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_25, c_0_97])).
% 0.46/0.63  cnf(c_0_101, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_90]), c_0_21])])).
% 0.46/0.63  cnf(c_0_102, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.46/0.63  cnf(c_0_103, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_37]), c_0_30]), c_0_21])])).
% 0.46/0.63  cnf(c_0_104, negated_conjecture, (~v3_pre_topc(X1,esk1_0)|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_102]), c_0_103])]), c_0_31])).
% 0.46/0.63  cnf(c_0_105, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_89]), c_0_29]), c_0_30]), c_0_55])])).
% 0.46/0.63  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_103]), c_0_42])]), ['proof']).
% 0.46/0.63  # SZS output end CNFRefutation
% 0.46/0.63  # Proof object total steps             : 107
% 0.46/0.63  # Proof object clause steps            : 78
% 0.46/0.63  # Proof object formula steps           : 29
% 0.46/0.63  # Proof object conjectures             : 53
% 0.46/0.63  # Proof object clause conjectures      : 50
% 0.46/0.63  # Proof object formula conjectures     : 3
% 0.46/0.63  # Proof object initial clauses used    : 23
% 0.46/0.63  # Proof object initial formulas used   : 14
% 0.46/0.63  # Proof object generating inferences   : 53
% 0.46/0.63  # Proof object simplifying inferences  : 76
% 0.46/0.63  # Training examples: 0 positive, 0 negative
% 0.46/0.63  # Parsed axioms                        : 14
% 0.46/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.63  # Initial clauses                      : 25
% 0.46/0.63  # Removed in clause preprocessing      : 0
% 0.46/0.63  # Initial clauses in saturation        : 25
% 0.46/0.63  # Processed clauses                    : 2340
% 0.46/0.63  # ...of these trivial                  : 46
% 0.46/0.63  # ...subsumed                          : 1440
% 0.46/0.63  # ...remaining for further processing  : 854
% 0.46/0.63  # Other redundant clauses eliminated   : 0
% 0.46/0.63  # Clauses deleted for lack of memory   : 0
% 0.46/0.63  # Backward-subsumed                    : 23
% 0.46/0.63  # Backward-rewritten                   : 241
% 0.46/0.63  # Generated clauses                    : 10428
% 0.46/0.63  # ...of the previous two non-trivial   : 10217
% 0.46/0.63  # Contextual simplify-reflections      : 31
% 0.46/0.63  # Paramodulations                      : 10428
% 0.46/0.63  # Factorizations                       : 0
% 0.46/0.63  # Equation resolutions                 : 0
% 0.46/0.63  # Propositional unsat checks           : 0
% 0.46/0.63  #    Propositional check models        : 0
% 0.46/0.63  #    Propositional check unsatisfiable : 0
% 0.46/0.63  #    Propositional clauses             : 0
% 0.46/0.63  #    Propositional clauses after purity: 0
% 0.46/0.63  #    Propositional unsat core size     : 0
% 0.46/0.63  #    Propositional preprocessing time  : 0.000
% 0.46/0.63  #    Propositional encoding time       : 0.000
% 0.46/0.63  #    Propositional solver time         : 0.000
% 0.46/0.63  #    Success case prop preproc time    : 0.000
% 0.46/0.63  #    Success case prop encoding time   : 0.000
% 0.46/0.63  #    Success case prop solver time     : 0.000
% 0.46/0.63  # Current number of processed clauses  : 565
% 0.46/0.63  #    Positive orientable unit clauses  : 36
% 0.46/0.63  #    Positive unorientable unit clauses: 0
% 0.46/0.63  #    Negative unit clauses             : 0
% 0.46/0.63  #    Non-unit-clauses                  : 529
% 0.46/0.63  # Current number of unprocessed clauses: 7899
% 0.46/0.63  # ...number of literals in the above   : 31418
% 0.46/0.63  # Current number of archived formulas  : 0
% 0.46/0.63  # Current number of archived clauses   : 289
% 0.46/0.63  # Clause-clause subsumption calls (NU) : 116828
% 0.46/0.63  # Rec. Clause-clause subsumption calls : 80608
% 0.46/0.63  # Non-unit clause-clause subsumptions  : 1480
% 0.46/0.63  # Unit Clause-clause subsumption calls : 383
% 0.46/0.63  # Rewrite failures with RHS unbound    : 0
% 0.46/0.63  # BW rewrite match attempts            : 63
% 0.46/0.63  # BW rewrite match successes           : 11
% 0.46/0.63  # Condensation attempts                : 0
% 0.46/0.63  # Condensation successes               : 0
% 0.46/0.63  # Termbank termtop insertions          : 189516
% 0.46/0.63  
% 0.46/0.63  # -------------------------------------------------
% 0.46/0.63  # User time                : 0.335 s
% 0.46/0.63  # System time              : 0.006 s
% 0.46/0.63  # Total time               : 0.341 s
% 0.46/0.63  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
