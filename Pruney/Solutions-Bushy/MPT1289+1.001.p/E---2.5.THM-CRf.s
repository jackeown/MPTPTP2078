%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1289+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:03 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 807 expanded)
%              Number of clauses        :   82 ( 306 expanded)
%              Number of leaves         :   11 ( 203 expanded)
%              Depth                    :   25
%              Number of atoms          :  392 (3098 expanded)
%              Number of equality atoms :    6 (  54 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(t111_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
           => ( v4_tops_1(k1_tops_1(X1,X2),X1)
              & v4_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(d6_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
          <=> ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
              & r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(projectivity_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(c_0_11,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | r1_tarski(k1_tops_1(X17,X18),X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X21,X22,X23] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ r1_tarski(X22,X23)
      | r1_tarski(k1_tops_1(X21,X22),k1_tops_1(X21,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_tops_1(X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_tops_1(X2,X1)
             => ( v4_tops_1(k1_tops_1(X1,X2),X1)
                & v4_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t111_tops_1])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_tops_1(esk2_0,esk1_0)
    & ( ~ v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)
      | ~ v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_tops_1(X3,X4))
    | ~ r1_tarski(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X2,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

fof(c_0_25,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | m1_subset_1(k1_tops_1(X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_23])])).

cnf(c_0_27,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_28,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(k1_tops_1(X4,k2_pre_topc(X4,X5)),X5)
        | ~ v4_tops_1(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( r1_tarski(X5,k2_pre_topc(X4,k1_tops_1(X4,X5)))
        | ~ v4_tops_1(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( ~ r1_tarski(k1_tops_1(X4,k2_pre_topc(X4,X5)),X5)
        | ~ r1_tarski(X5,k2_pre_topc(X4,k1_tops_1(X4,X5)))
        | v4_tops_1(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,X2),esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23])])).

fof(c_0_30,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | k1_tops_1(X10,k1_tops_1(X10,X11)) = k1_tops_1(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

fof(c_0_31,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | r1_tarski(X20,k2_pre_topc(X19,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

fof(c_0_32,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ r1_tarski(X25,X26)
      | r1_tarski(k2_pre_topc(X24,X25),k2_pre_topc(X24,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))
    | ~ v4_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_14]),c_0_22]),c_0_23])])).

cnf(c_0_35,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | k2_pre_topc(X12,k2_pre_topc(X12,X13)) = k2_pre_topc(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

fof(c_0_39,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
      | m1_subset_1(k2_pre_topc(X8,X9),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ v4_tops_1(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_23])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ r1_tarski(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ r1_tarski(X1,k2_pre_topc(X2,X4))
    | ~ r1_tarski(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_37])).

cnf(c_0_44,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X3)))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3)
    | ~ v4_tops_1(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( v4_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_14]),c_0_23])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,X2))
    | ~ r1_tarski(X2,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_22]),c_0_23])])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_44]),c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_22]),c_0_47]),c_0_23])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_27]),c_0_23])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ r1_tarski(X1,k1_tops_1(X2,X4))
    | ~ r1_tarski(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k2_pre_topc(X2,X3)))
    | ~ r1_tarski(X4,k2_pre_topc(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ r1_tarski(X1,k1_tops_1(X2,X4))
    | ~ r1_tarski(X4,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,X2)))
    | ~ r1_tarski(k1_tops_1(esk1_0,X2),esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_27]),c_0_23])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ r1_tarski(X1,k2_pre_topc(X2,X4))
    | ~ r1_tarski(X4,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_35]),c_0_27])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X2,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_23])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0)))
    | ~ r1_tarski(X2,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_23])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,X2))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_22]),c_0_23])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)
    | ~ v4_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_33]),c_0_23])])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X4)))
    | ~ r1_tarski(k1_tops_1(X2,X4),k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_27])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_23])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,k1_tops_1(esk1_0,X2)))
    | ~ r1_tarski(k1_tops_1(esk1_0,X2),esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_27]),c_0_23])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0)))
    | ~ r1_tarski(X2,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_51]),c_0_22]),c_0_23])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,X1))
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_60]),c_0_22]),c_0_23])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_14]),c_0_47]),c_0_22]),c_0_23])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ r1_tarski(k1_tops_1(X2,X1),k2_pre_topc(X2,X3))
    | ~ v4_tops_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_33])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_35]),c_0_22]),c_0_23])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(k1_tops_1(esk1_0,X2),esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_35]),c_0_23])])).

cnf(c_0_74,plain,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ v4_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_22])])).

cnf(c_0_76,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_44]),c_0_45])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_47]),c_0_22]),c_0_23])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_47]),c_0_22]),c_0_23])])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)),k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_23])])).

cnf(c_0_80,plain,
    ( v4_tops_1(X2,X1)
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,X2))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_22]),c_0_23])])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_22]),c_0_23])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_77]),c_0_22]),c_0_23])])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_17]),c_0_23])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)),k2_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_44]),c_0_22]),c_0_23])])).

cnf(c_0_86,plain,
    ( v4_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2))))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_44]),c_0_45])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,X1))
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_76]),c_0_22]),c_0_23])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(X2,k2_pre_topc(X2,esk2_0)))
    | ~ v4_tops_1(esk2_0,X2)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_74])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),X1)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_42]),c_0_23])])).

cnf(c_0_90,negated_conjecture,
    ( v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_84]),c_0_23])]),c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))))
    | ~ m1_subset_1(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_22]),c_0_23])])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,esk2_0)),k2_pre_topc(esk1_0,esk2_0))
    | ~ v4_tops_1(esk2_0,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_60]),c_0_45])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_27]),c_0_22]),c_0_23])])).

cnf(c_0_94,negated_conjecture,
    ( v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_35]),c_0_22]),c_0_23])]),c_0_72])).

cnf(c_0_95,negated_conjecture,
    ( v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))))
    | ~ m1_subset_1(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_47]),c_0_22]),c_0_23])])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,X1)))
    | ~ r1_tarski(esk2_0,X1)
    | ~ m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_17]),c_0_22]),c_0_23])])).

cnf(c_0_97,negated_conjecture,
    ( ~ v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)
    | ~ v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_98,negated_conjecture,
    ( v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_45]),c_0_23])])).

cnf(c_0_99,negated_conjecture,
    ( v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_70])])).

cnf(c_0_100,negated_conjecture,
    ( ~ v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_27]),c_0_23])])).

cnf(c_0_102,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_103,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_27]),c_0_22]),c_0_23])])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_45]),c_0_22]),c_0_23])]),
    [proof]).

%------------------------------------------------------------------------------
