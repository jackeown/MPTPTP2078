%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:44 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  125 (5208 expanded)
%              Number of clauses        :  100 (2230 expanded)
%              Number of leaves         :   12 (1276 expanded)
%              Depth                    :   28
%              Number of atoms          :  389 (18135 expanded)
%              Number of equality atoms :   24 ( 960 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t111_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
           => ( v4_tops_1(k1_tops_1(X1,X2),X1)
              & v4_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_tops_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

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

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_tops_1(X2,X1)
             => ( v4_tops_1(k1_tops_1(X1,X2),X1)
                & v4_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t111_tops_1])).

fof(c_0_13,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_14,plain,(
    ! [X15,X16,X17] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
      | ~ r1_tarski(X16,X17)
      | r1_tarski(k2_pre_topc(X15,X16),k2_pre_topc(X15,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

fof(c_0_15,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | r1_tarski(k1_tops_1(X24,X25),X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_tops_1(esk2_0,esk1_0)
    & ( ~ v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)
      | ~ v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_pre_topc(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_25,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ r1_tarski(X27,X28)
      | r1_tarski(k1_tops_1(X26,X27),k1_tops_1(X26,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_pre_topc(X2,X4))
    | ~ r1_tarski(X3,u1_struct_0(X2))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ r1_tarski(X1,k1_tops_1(X3,X2))
    | ~ r1_tarski(X2,u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,X2))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k2_pre_topc(X2,X4))
    | ~ r1_tarski(X3,u1_struct_0(X2))
    | ~ r1_tarski(X4,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_21]),c_0_18])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,X2))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_21]),c_0_35])).

cnf(c_0_40,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_28])]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),X1)
    | ~ r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_28])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_29]),c_0_37])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X2,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_37])).

fof(c_0_47,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | k2_pre_topc(X13,k2_pre_topc(X13,X14)) = k2_pre_topc(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

fof(c_0_48,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_37])).

cnf(c_0_51,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | ~ r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_51]),c_0_52])).

fof(c_0_55,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(k1_tops_1(X18,k2_pre_topc(X18,X19)),X19)
        | ~ v4_tops_1(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( r1_tarski(X19,k2_pre_topc(X18,k1_tops_1(X18,X19)))
        | ~ v4_tops_1(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( ~ r1_tarski(k1_tops_1(X18,k2_pre_topc(X18,X19)),X19)
        | ~ r1_tarski(X19,k2_pre_topc(X18,k1_tops_1(X18,X19)))
        | v4_tops_1(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_35])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_23]),c_0_28])])).

cnf(c_0_58,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_28]),c_0_23])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))
    | ~ v4_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( v4_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_pre_topc(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_65,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_28]),c_0_23])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_37])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_28]),c_0_23])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,X2))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X2,u1_struct_0(esk1_0))
    | ~ r1_tarski(esk2_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_23]),c_0_28])])).

cnf(c_0_69,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_21]),c_0_66])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,X2))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,X1))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_37])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ v4_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_73,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_69]),c_0_28])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_35])).

cnf(c_0_75,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_19])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ v4_tops_1(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X1,k1_tops_1(X3,k2_pre_topc(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_72])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_52])).

cnf(c_0_78,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_21]),c_0_66])])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_37]),c_0_37])])).

cnf(c_0_80,negated_conjecture,
    ( k2_pre_topc(esk1_0,X1) = k2_pre_topc(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_64]),c_0_28]),c_0_23])])).

cnf(c_0_81,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ v4_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_33]),c_0_52])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_28])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_79])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k1_tops_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_33])).

cnf(c_0_85,negated_conjecture,
    ( k2_pre_topc(esk1_0,X1) = k2_pre_topc(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_21]),c_0_35])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))),esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_61]),c_0_28]),c_0_23])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_77]),c_0_28]),c_0_23])])).

fof(c_0_88,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k1_tops_1(X22,k1_tops_1(X22,X23)) = k1_tops_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_23]),c_0_28])])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_85]),c_0_28]),c_0_23])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))),esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_21]),c_0_87])])).

cnf(c_0_92,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_93,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | m1_subset_1(k1_tops_1(X20,X21),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_21]),c_0_35])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_85])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_28])])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X3)))
    | ~ v4_tops_1(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_60])).

cnf(c_0_98,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_99,plain,
    ( v4_tops_1(X2,X1)
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,X2),esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_92]),c_0_28])])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_37]),c_0_37])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_21]),c_0_79])])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_97]),c_0_61]),c_0_28]),c_0_23])])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X2,u1_struct_0(esk1_0))
    | ~ r1_tarski(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_43])).

cnf(c_0_105,plain,
    ( r1_tarski(k1_tops_1(X1,k1_tops_1(X1,X2)),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_98])).

cnf(c_0_106,plain,
    ( v4_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_51]),c_0_20]),c_0_52])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),X1)
    | ~ r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_28]),c_0_23])])).

cnf(c_0_110,negated_conjecture,
    ( v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_78]),c_0_28])])).

cnf(c_0_111,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_37])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_60]),c_0_61]),c_0_28]),c_0_23])])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_29]),c_0_37])])).

cnf(c_0_115,negated_conjecture,
    ( v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_101])])).

cnf(c_0_116,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_28]),c_0_101]),c_0_23]),c_0_113])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_37])).

cnf(c_0_118,negated_conjecture,
    ( ~ v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)
    | ~ v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_119,negated_conjecture,
    ( v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116]),c_0_69]),c_0_37])])).

cnf(c_0_120,plain,
    ( v4_tops_1(k1_tops_1(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,k1_tops_1(X1,X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X2)),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_33]),c_0_98])).

cnf(c_0_121,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_116]),c_0_28]),c_0_101])])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_92]),c_0_28]),c_0_23])])).

cnf(c_0_123,negated_conjecture,
    ( ~ v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_119])])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_116]),c_0_28]),c_0_69]),c_0_101]),c_0_101]),c_0_69]),c_0_37])]),c_0_121]),c_0_69]),c_0_122])]),c_0_123]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:49:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.50/0.68  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.50/0.68  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.50/0.68  #
% 0.50/0.68  # Preprocessing time       : 0.029 s
% 0.50/0.68  # Presaturation interreduction done
% 0.50/0.68  
% 0.50/0.68  # Proof found!
% 0.50/0.68  # SZS status Theorem
% 0.50/0.68  # SZS output start CNFRefutation
% 0.50/0.68  fof(t111_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)=>(v4_tops_1(k1_tops_1(X1,X2),X1)&v4_tops_1(k2_pre_topc(X1,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_tops_1)).
% 0.50/0.68  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.50/0.68  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 0.50/0.68  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.50/0.68  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.50/0.68  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.50/0.68  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.50/0.68  fof(projectivity_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 0.50/0.68  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.50/0.68  fof(d6_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)<=>(r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)&r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 0.50/0.68  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 0.50/0.68  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.50/0.68  fof(c_0_12, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)=>(v4_tops_1(k1_tops_1(X1,X2),X1)&v4_tops_1(k2_pre_topc(X1,X2),X1)))))), inference(assume_negation,[status(cth)],[t111_tops_1])).
% 0.50/0.68  fof(c_0_13, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.50/0.68  fof(c_0_14, plain, ![X15, X16, X17]:(~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(~r1_tarski(X16,X17)|r1_tarski(k2_pre_topc(X15,X16),k2_pre_topc(X15,X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 0.50/0.68  fof(c_0_15, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|r1_tarski(k1_tops_1(X24,X25),X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.50/0.68  fof(c_0_16, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.50/0.68  fof(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v4_tops_1(esk2_0,esk1_0)&(~v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)|~v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.50/0.68  cnf(c_0_18, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.50/0.68  cnf(c_0_19, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.50/0.68  cnf(c_0_20, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.68  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.68  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.68  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.68  cnf(c_0_24, plain, (r1_tarski(X1,k2_pre_topc(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_pre_topc(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.50/0.68  fof(c_0_25, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.50/0.68  cnf(c_0_26, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.50/0.68  fof(c_0_27, plain, ![X26, X27, X28]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~r1_tarski(X27,X28)|r1_tarski(k1_tops_1(X26,X27),k1_tops_1(X26,X28)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.50/0.68  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.68  cnf(c_0_29, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.50/0.68  cnf(c_0_30, plain, (r1_tarski(X1,k2_pre_topc(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_pre_topc(X2,X4))|~r1_tarski(X3,u1_struct_0(X2))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.50/0.68  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.50/0.68  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~l1_pre_topc(X3)|~r1_tarski(X1,k1_tops_1(X3,X2))|~r1_tarski(X2,u1_struct_0(X3))), inference(spm,[status(thm)],[c_0_18, c_0_26])).
% 0.50/0.68  cnf(c_0_33, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.50/0.68  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k2_pre_topc(esk1_0,X2))|~r1_tarski(X2,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_23]), c_0_28])])).
% 0.50/0.68  cnf(c_0_35, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_29])).
% 0.50/0.68  cnf(c_0_36, plain, (r1_tarski(X1,k2_pre_topc(X2,X3))|~l1_pre_topc(X2)|~r1_tarski(X1,k2_pre_topc(X2,X4))|~r1_tarski(X3,u1_struct_0(X2))|~r1_tarski(X4,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_21]), c_0_18])).
% 0.50/0.68  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.50/0.68  cnf(c_0_38, plain, (r1_tarski(k1_tops_1(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_22])).
% 0.50/0.68  cnf(c_0_39, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X1,k2_pre_topc(esk1_0,X2))|~r1_tarski(X2,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_21]), c_0_35])).
% 0.50/0.68  cnf(c_0_40, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~r1_tarski(X3,u1_struct_0(X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.50/0.68  cnf(c_0_41, plain, (r1_tarski(k1_tops_1(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,u1_struct_0(X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_21])).
% 0.50/0.68  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_28])]), c_0_35])).
% 0.50/0.68  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),X1)|~r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_23]), c_0_28])])).
% 0.50/0.68  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_29]), c_0_37])])).
% 0.50/0.68  cnf(c_0_45, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X2,k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,k2_pre_topc(esk1_0,X2))), inference(spm,[status(thm)],[c_0_18, c_0_44])).
% 0.50/0.68  cnf(c_0_46, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X1,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_45, c_0_37])).
% 0.50/0.68  fof(c_0_47, plain, ![X13, X14]:(~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|k2_pre_topc(X13,k2_pre_topc(X13,X14))=k2_pre_topc(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).
% 0.50/0.68  fof(c_0_48, plain, ![X11, X12]:(~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.50/0.68  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.50/0.68  cnf(c_0_50, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)),k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_37])).
% 0.50/0.68  cnf(c_0_51, plain, (k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.50/0.68  cnf(c_0_52, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.50/0.68  cnf(c_0_53, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|~r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.50/0.68  cnf(c_0_54, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k2_pre_topc(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_51]), c_0_52])).
% 0.50/0.68  fof(c_0_55, plain, ![X18, X19]:(((r1_tarski(k1_tops_1(X18,k2_pre_topc(X18,X19)),X19)|~v4_tops_1(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(r1_tarski(X19,k2_pre_topc(X18,k1_tops_1(X18,X19)))|~v4_tops_1(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18)))&(~r1_tarski(k1_tops_1(X18,k2_pre_topc(X18,X19)),X19)|~r1_tarski(X19,k2_pre_topc(X18,k1_tops_1(X18,X19)))|v4_tops_1(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).
% 0.50/0.68  cnf(c_0_56, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_35])).
% 0.50/0.68  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_23]), c_0_28])])).
% 0.50/0.68  cnf(c_0_58, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_22, c_0_52])).
% 0.50/0.68  cnf(c_0_59, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_28]), c_0_23])])).
% 0.50/0.68  cnf(c_0_60, plain, (r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))|~v4_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.50/0.68  cnf(c_0_61, negated_conjecture, (v4_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.68  cnf(c_0_62, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.50/0.68  cnf(c_0_63, plain, (r1_tarski(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_pre_topc(X2,X3))), inference(spm,[status(thm)],[c_0_18, c_0_58])).
% 0.50/0.68  cnf(c_0_64, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.50/0.68  cnf(c_0_65, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_28]), c_0_23])])).
% 0.50/0.68  cnf(c_0_66, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_62, c_0_37])).
% 0.50/0.68  cnf(c_0_67, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,X1),u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_28]), c_0_23])])).
% 0.50/0.68  cnf(c_0_68, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,X2))|~r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X2,u1_struct_0(esk1_0))|~r1_tarski(esk2_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_23]), c_0_28])])).
% 0.50/0.68  cnf(c_0_69, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_21]), c_0_66])])).
% 0.50/0.68  cnf(c_0_70, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k2_pre_topc(esk1_0,X2))|~r1_tarski(X2,esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_67])).
% 0.50/0.68  cnf(c_0_71, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,X1))|~r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_68, c_0_37])).
% 0.50/0.68  cnf(c_0_72, plain, (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~v4_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.50/0.68  cnf(c_0_73, negated_conjecture, (k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_69]), c_0_28])])).
% 0.50/0.68  cnf(c_0_74, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_35])).
% 0.50/0.68  cnf(c_0_75, plain, (k2_pre_topc(X1,X2)=k2_pre_topc(X1,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_49, c_0_19])).
% 0.50/0.68  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~v4_tops_1(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(X1,k1_tops_1(X3,k2_pre_topc(X3,X2)))), inference(spm,[status(thm)],[c_0_18, c_0_72])).
% 0.50/0.68  cnf(c_0_77, plain, (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_20, c_0_52])).
% 0.50/0.68  cnf(c_0_78, negated_conjecture, (k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_21]), c_0_66])])).
% 0.50/0.68  cnf(c_0_79, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_37]), c_0_37])])).
% 0.50/0.68  cnf(c_0_80, negated_conjecture, (k2_pre_topc(esk1_0,X1)=k2_pre_topc(esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_64]), c_0_28]), c_0_23])])).
% 0.50/0.68  cnf(c_0_81, plain, (r1_tarski(k1_tops_1(X1,X2),X3)|~v4_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k2_pre_topc(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_33]), c_0_52])).
% 0.50/0.68  cnf(c_0_82, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_pre_topc(esk1_0,esk2_0))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_28])])).
% 0.50/0.68  cnf(c_0_83, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_18, c_0_79])).
% 0.50/0.68  cnf(c_0_84, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k1_tops_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_18, c_0_33])).
% 0.50/0.68  cnf(c_0_85, negated_conjecture, (k2_pre_topc(esk1_0,X1)=k2_pre_topc(esk1_0,esk2_0)|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_21]), c_0_35])).
% 0.50/0.68  cnf(c_0_86, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))),esk2_0)|~m1_subset_1(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_61]), c_0_28]), c_0_23])])).
% 0.50/0.68  cnf(c_0_87, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_77]), c_0_28]), c_0_23])])).
% 0.50/0.68  fof(c_0_88, plain, ![X22, X23]:(~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|k1_tops_1(X22,k1_tops_1(X22,X23))=k1_tops_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 0.50/0.68  cnf(c_0_89, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k1_tops_1(esk1_0,X2))|~r1_tarski(X2,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_23]), c_0_28])])).
% 0.50/0.68  cnf(c_0_90, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_85]), c_0_28]), c_0_23])])).
% 0.50/0.68  cnf(c_0_91, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))),esk2_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_21]), c_0_87])])).
% 0.50/0.68  cnf(c_0_92, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.50/0.68  fof(c_0_93, plain, ![X20, X21]:(~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|m1_subset_1(k1_tops_1(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.50/0.68  cnf(c_0_94, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,k1_tops_1(esk1_0,X2))|~r1_tarski(X2,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_21]), c_0_35])).
% 0.50/0.68  cnf(c_0_95, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_90, c_0_85])).
% 0.50/0.68  cnf(c_0_96, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),esk2_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_28])])).
% 0.50/0.68  cnf(c_0_97, plain, (r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X3)))|~v4_tops_1(X3,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_18, c_0_60])).
% 0.50/0.68  cnf(c_0_98, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.50/0.68  cnf(c_0_99, plain, (v4_tops_1(X2,X1)|~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.50/0.68  cnf(c_0_100, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,X2),esk2_0)|~r1_tarski(X1,k1_tops_1(esk1_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_92]), c_0_28])])).
% 0.50/0.68  cnf(c_0_101, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_37]), c_0_37])])).
% 0.50/0.68  cnf(c_0_102, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_21]), c_0_79])])).
% 0.50/0.68  cnf(c_0_103, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_97]), c_0_61]), c_0_28]), c_0_23])])).
% 0.50/0.68  cnf(c_0_104, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X2,u1_struct_0(esk1_0))|~r1_tarski(esk2_0,X2)), inference(spm,[status(thm)],[c_0_18, c_0_43])).
% 0.50/0.68  cnf(c_0_105, plain, (r1_tarski(k1_tops_1(X1,k1_tops_1(X1,X2)),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_20, c_0_98])).
% 0.50/0.68  cnf(c_0_106, plain, (v4_tops_1(k2_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_51]), c_0_20]), c_0_52])).
% 0.50/0.68  cnf(c_0_107, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102])])).
% 0.50/0.68  cnf(c_0_108, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_103])).
% 0.50/0.68  cnf(c_0_109, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),X1)|~r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_28]), c_0_23])])).
% 0.50/0.68  cnf(c_0_110, negated_conjecture, (v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_78]), c_0_28])])).
% 0.50/0.68  cnf(c_0_111, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_49, c_0_33])).
% 0.50/0.68  cnf(c_0_112, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_107, c_0_37])).
% 0.50/0.68  cnf(c_0_113, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_60]), c_0_61]), c_0_28]), c_0_23])])).
% 0.50/0.68  cnf(c_0_114, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X1,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_29]), c_0_37])])).
% 0.50/0.68  cnf(c_0_115, negated_conjecture, (v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)|~r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_101])])).
% 0.50/0.68  cnf(c_0_116, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_28]), c_0_101]), c_0_23]), c_0_113])])).
% 0.50/0.68  cnf(c_0_117, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_114, c_0_37])).
% 0.50/0.68  cnf(c_0_118, negated_conjecture, (~v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)|~v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.68  cnf(c_0_119, negated_conjecture, (v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116]), c_0_69]), c_0_37])])).
% 0.50/0.68  cnf(c_0_120, plain, (v4_tops_1(k1_tops_1(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,k1_tops_1(X1,X2))))|~r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X2)),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_33]), c_0_98])).
% 0.50/0.68  cnf(c_0_121, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_116]), c_0_28]), c_0_101])])).
% 0.50/0.68  cnf(c_0_122, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_92]), c_0_28]), c_0_23])])).
% 0.50/0.68  cnf(c_0_123, negated_conjecture, (~v4_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_119])])).
% 0.50/0.68  cnf(c_0_124, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_116]), c_0_28]), c_0_69]), c_0_101]), c_0_101]), c_0_69]), c_0_37])]), c_0_121]), c_0_69]), c_0_122])]), c_0_123]), ['proof']).
% 0.50/0.68  # SZS output end CNFRefutation
% 0.50/0.68  # Proof object total steps             : 125
% 0.50/0.68  # Proof object clause steps            : 100
% 0.50/0.68  # Proof object formula steps           : 25
% 0.50/0.68  # Proof object conjectures             : 66
% 0.50/0.68  # Proof object clause conjectures      : 63
% 0.50/0.68  # Proof object formula conjectures     : 3
% 0.50/0.68  # Proof object initial clauses used    : 19
% 0.50/0.68  # Proof object initial formulas used   : 12
% 0.50/0.68  # Proof object generating inferences   : 77
% 0.50/0.68  # Proof object simplifying inferences  : 120
% 0.50/0.68  # Training examples: 0 positive, 0 negative
% 0.50/0.68  # Parsed axioms                        : 12
% 0.50/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.68  # Initial clauses                      : 20
% 0.50/0.68  # Removed in clause preprocessing      : 0
% 0.50/0.68  # Initial clauses in saturation        : 20
% 0.50/0.68  # Processed clauses                    : 2973
% 0.50/0.68  # ...of these trivial                  : 27
% 0.50/0.68  # ...subsumed                          : 2135
% 0.50/0.68  # ...remaining for further processing  : 810
% 0.50/0.68  # Other redundant clauses eliminated   : 2
% 0.50/0.68  # Clauses deleted for lack of memory   : 0
% 0.50/0.68  # Backward-subsumed                    : 162
% 0.50/0.68  # Backward-rewritten                   : 188
% 0.50/0.68  # Generated clauses                    : 14879
% 0.50/0.68  # ...of the previous two non-trivial   : 12233
% 0.50/0.68  # Contextual simplify-reflections      : 70
% 0.50/0.68  # Paramodulations                      : 14877
% 0.50/0.68  # Factorizations                       : 0
% 0.50/0.68  # Equation resolutions                 : 2
% 0.50/0.68  # Propositional unsat checks           : 0
% 0.50/0.68  #    Propositional check models        : 0
% 0.50/0.68  #    Propositional check unsatisfiable : 0
% 0.50/0.68  #    Propositional clauses             : 0
% 0.50/0.68  #    Propositional clauses after purity: 0
% 0.50/0.68  #    Propositional unsat core size     : 0
% 0.50/0.68  #    Propositional preprocessing time  : 0.000
% 0.50/0.68  #    Propositional encoding time       : 0.000
% 0.50/0.68  #    Propositional solver time         : 0.000
% 0.50/0.68  #    Success case prop preproc time    : 0.000
% 0.50/0.68  #    Success case prop encoding time   : 0.000
% 0.50/0.68  #    Success case prop solver time     : 0.000
% 0.50/0.68  # Current number of processed clauses  : 439
% 0.50/0.68  #    Positive orientable unit clauses  : 19
% 0.50/0.68  #    Positive unorientable unit clauses: 0
% 0.50/0.68  #    Negative unit clauses             : 4
% 0.50/0.68  #    Non-unit-clauses                  : 416
% 0.50/0.68  # Current number of unprocessed clauses: 9066
% 0.50/0.68  # ...number of literals in the above   : 47961
% 0.50/0.68  # Current number of archived formulas  : 0
% 0.50/0.68  # Current number of archived clauses   : 369
% 0.50/0.68  # Clause-clause subsumption calls (NU) : 41998
% 0.50/0.68  # Rec. Clause-clause subsumption calls : 22033
% 0.50/0.68  # Non-unit clause-clause subsumptions  : 1831
% 0.50/0.68  # Unit Clause-clause subsumption calls : 1079
% 0.50/0.68  # Rewrite failures with RHS unbound    : 0
% 0.50/0.68  # BW rewrite match attempts            : 94
% 0.50/0.68  # BW rewrite match successes           : 23
% 0.50/0.68  # Condensation attempts                : 0
% 0.50/0.68  # Condensation successes               : 0
% 0.50/0.68  # Termbank termtop insertions          : 355016
% 0.50/0.68  
% 0.50/0.68  # -------------------------------------------------
% 0.50/0.68  # User time                : 0.334 s
% 0.50/0.68  # System time              : 0.008 s
% 0.50/0.68  # Total time               : 0.342 s
% 0.50/0.68  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
