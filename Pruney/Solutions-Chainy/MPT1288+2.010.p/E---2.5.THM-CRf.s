%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 227 expanded)
%              Number of clauses        :   40 (  85 expanded)
%              Number of leaves         :   15 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  261 ( 921 expanded)
%              Number of equality atoms :   35 ( 150 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t110_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
           => k1_tops_1(X1,k2_tops_1(X1,X2)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tops_1)).

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

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(t92_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
           => v2_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(t95_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
           => v3_tops_1(k2_tops_1(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

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

fof(d6_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
          <=> ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
              & r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(c_0_15,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X10,X11,X12] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ r1_tarski(X11,X12)
      | r1_tarski(k2_pre_topc(X10,X11),k2_pre_topc(X10,X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_tops_1(X2,X1)
             => k1_tops_1(X1,k2_tops_1(X1,X2)) = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t110_tops_1])).

cnf(c_0_20,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_tops_1(esk2_0,esk1_0)
    & k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_22,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
      | k2_pre_topc(X8,k2_pre_topc(X8,X9)) = k2_pre_topc(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

fof(c_0_26,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | m1_subset_1(k2_pre_topc(X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_27,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = k2_pre_topc(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | k2_tops_1(X21,X22) = k7_subset_1(u1_struct_0(X21),k2_pre_topc(X21,X22),k1_tops_1(X21,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_30,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(esk2_0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_27]),c_0_24])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ v3_tops_1(X30,X29)
      | v2_tops_1(X30,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_tops_1])])])).

fof(c_0_36,plain,(
    ! [X31,X32] :
      ( ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ v3_pre_topc(X32,X31)
      | v3_tops_1(k2_tops_1(X31,X32),X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_tops_1])])])).

fof(c_0_37,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | m1_subset_1(k2_tops_1(X17,X18),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_38,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | k1_tops_1(X23,k1_tops_1(X23,X24)) = k1_tops_1(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

fof(c_0_39,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | m1_subset_1(k1_tops_1(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_40,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,k2_pre_topc(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_30]),c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_23]),c_0_33])])).

fof(c_0_42,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(k1_tops_1(X13,k2_pre_topc(X13,X14)),X14)
        | ~ v4_tops_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( r1_tarski(X14,k2_pre_topc(X13,k1_tops_1(X13,X14)))
        | ~ v4_tops_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( ~ r1_tarski(k1_tops_1(X13,k2_pre_topc(X13,X14)),X14)
        | ~ r1_tarski(X14,k2_pre_topc(X13,k1_tops_1(X13,X14)))
        | v4_tops_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

cnf(c_0_43,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,X1),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_27]),c_0_23]),c_0_24])])).

fof(c_0_44,plain,(
    ! [X27,X28] :
      ( ( ~ v2_tops_1(X28,X27)
        | k1_tops_1(X27,X28) = k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( k1_tops_1(X27,X28) != k1_xboole_0
        | v2_tops_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_45,plain,
    ( v2_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tops_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( v3_tops_1(k2_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k2_pre_topc(esk1_0,X1) = k2_pre_topc(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,X1))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_23]),c_0_24])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))
    | ~ v4_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( v4_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_27])).

cnf(c_0_54,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( v2_tops_1(k2_tops_1(X1,X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_56,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_tops_1(X1,X2)) = k2_tops_1(X1,k1_tops_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_48]),c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_23]),c_0_24])])).

cnf(c_0_58,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_23]),c_0_33])])).

cnf(c_0_59,plain,
    ( k1_tops_1(X1,k2_tops_1(X1,X2)) = k1_xboole_0
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( k2_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_23]),c_0_24])]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_63,plain,(
    ! [X19,X20] :
      ( ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | v3_pre_topc(k1_tops_1(X19,X20),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v3_pre_topc(k1_tops_1(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_24])]),c_0_62])).

cnf(c_0_65,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_66,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | r1_tarski(k1_tops_1(X25,X26),X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_61]),c_0_23]),c_0_24])])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_23]),c_0_24])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_49]),c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:19:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.029 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 0.19/0.45  fof(t110_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)=>k1_tops_1(X1,k2_tops_1(X1,X2))=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_tops_1)).
% 0.19/0.45  fof(projectivity_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 0.19/0.45  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.19/0.45  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.19/0.45  fof(t92_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v2_tops_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 0.19/0.45  fof(t95_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)=>v3_tops_1(k2_tops_1(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tops_1)).
% 0.19/0.45  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.19/0.45  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 0.19/0.45  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.19/0.45  fof(d6_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)<=>(r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)&r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 0.19/0.45  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 0.19/0.45  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.19/0.45  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.19/0.45  fof(c_0_15, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  fof(c_0_16, plain, ![X10, X11, X12]:(~l1_pre_topc(X10)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))|(~r1_tarski(X11,X12)|r1_tarski(k2_pre_topc(X10,X11),k2_pre_topc(X10,X12)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 0.19/0.45  cnf(c_0_17, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.45  cnf(c_0_18, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  fof(c_0_19, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)=>k1_tops_1(X1,k2_tops_1(X1,X2))=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t110_tops_1])).
% 0.19/0.45  cnf(c_0_20, plain, (k2_pre_topc(X1,X2)=k2_pre_topc(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.45  fof(c_0_21, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v4_tops_1(esk2_0,esk1_0)&k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.19/0.45  cnf(c_0_22, plain, (k2_pre_topc(X1,X2)=k2_pre_topc(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X3,X2)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.19/0.45  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  fof(c_0_25, plain, ![X8, X9]:(~l1_pre_topc(X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|k2_pre_topc(X8,k2_pre_topc(X8,X9))=k2_pre_topc(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).
% 0.19/0.45  fof(c_0_26, plain, ![X6, X7]:(~l1_pre_topc(X6)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|m1_subset_1(k2_pre_topc(X6,X7),k1_zfmisc_1(u1_struct_0(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.19/0.45  cnf(c_0_27, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=k2_pre_topc(esk1_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.45  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.45  fof(c_0_29, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|k2_tops_1(X21,X22)=k7_subset_1(u1_struct_0(X21),k2_pre_topc(X21,X22),k1_tops_1(X21,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.19/0.45  cnf(c_0_30, plain, (k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_31, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X2,esk2_0)|~r1_tarski(esk2_0,X2)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_27]), c_0_24])])).
% 0.19/0.45  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_34, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.45  fof(c_0_35, plain, ![X29, X30]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~v3_tops_1(X30,X29)|v2_tops_1(X30,X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_tops_1])])])).
% 0.19/0.45  fof(c_0_36, plain, ![X31, X32]:(~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~v3_pre_topc(X32,X31)|v3_tops_1(k2_tops_1(X31,X32),X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_tops_1])])])).
% 0.19/0.45  fof(c_0_37, plain, ![X17, X18]:(~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|m1_subset_1(k2_tops_1(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.19/0.45  fof(c_0_38, plain, ![X23, X24]:(~l1_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|k1_tops_1(X23,k1_tops_1(X23,X24))=k1_tops_1(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 0.19/0.45  fof(c_0_39, plain, ![X15, X16]:(~l1_pre_topc(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|m1_subset_1(k1_tops_1(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.19/0.45  cnf(c_0_40, plain, (k2_pre_topc(X1,X2)=k2_pre_topc(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~r1_tarski(X3,k2_pre_topc(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_30]), c_0_31])).
% 0.19/0.45  cnf(c_0_41, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_23]), c_0_33])])).
% 0.19/0.45  fof(c_0_42, plain, ![X13, X14]:(((r1_tarski(k1_tops_1(X13,k2_pre_topc(X13,X14)),X14)|~v4_tops_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(r1_tarski(X14,k2_pre_topc(X13,k1_tops_1(X13,X14)))|~v4_tops_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13)))&(~r1_tarski(k1_tops_1(X13,k2_pre_topc(X13,X14)),X14)|~r1_tarski(X14,k2_pre_topc(X13,k1_tops_1(X13,X14)))|v4_tops_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).
% 0.19/0.45  cnf(c_0_43, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_27]), c_0_23]), c_0_24])])).
% 0.19/0.45  fof(c_0_44, plain, ![X27, X28]:((~v2_tops_1(X28,X27)|k1_tops_1(X27,X28)=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(k1_tops_1(X27,X28)!=k1_xboole_0|v2_tops_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.19/0.45  cnf(c_0_45, plain, (v2_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tops_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.45  cnf(c_0_46, plain, (v3_tops_1(k2_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.45  cnf(c_0_47, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.45  cnf(c_0_48, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.45  cnf(c_0_49, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.45  cnf(c_0_50, negated_conjecture, (k2_pre_topc(esk1_0,X1)=k2_pre_topc(esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,k2_pre_topc(esk1_0,X1))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_23]), c_0_24])])).
% 0.19/0.45  cnf(c_0_51, plain, (r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))|~v4_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.45  cnf(c_0_52, negated_conjecture, (v4_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  cnf(c_0_53, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_27])).
% 0.19/0.45  cnf(c_0_54, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.45  cnf(c_0_55, plain, (v2_tops_1(k2_tops_1(X1,X2),X1)|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.19/0.45  cnf(c_0_56, plain, (k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_tops_1(X1,X2))=k2_tops_1(X1,k1_tops_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_48]), c_0_49])).
% 0.19/0.45  cnf(c_0_57, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_23]), c_0_24])])).
% 0.19/0.45  cnf(c_0_58, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_23]), c_0_33])])).
% 0.19/0.45  cnf(c_0_59, plain, (k1_tops_1(X1,k2_tops_1(X1,X2))=k1_xboole_0|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_47])).
% 0.19/0.45  cnf(c_0_60, negated_conjecture, (k2_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_23]), c_0_24])]), c_0_58])).
% 0.19/0.45  cnf(c_0_61, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  cnf(c_0_62, negated_conjecture, (k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  fof(c_0_63, plain, ![X19, X20]:(~v2_pre_topc(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v3_pre_topc(k1_tops_1(X19,X20),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.19/0.45  cnf(c_0_64, negated_conjecture, (~v3_pre_topc(k1_tops_1(esk1_0,esk2_0),esk1_0)|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_24])]), c_0_62])).
% 0.19/0.45  cnf(c_0_65, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.45  fof(c_0_66, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|r1_tarski(k1_tops_1(X25,X26),X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.19/0.45  cnf(c_0_67, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_61]), c_0_23]), c_0_24])])).
% 0.19/0.45  cnf(c_0_68, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.45  cnf(c_0_69, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_23]), c_0_24])])).
% 0.19/0.45  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_49]), c_0_23]), c_0_24])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 71
% 0.19/0.45  # Proof object clause steps            : 40
% 0.19/0.45  # Proof object formula steps           : 31
% 0.19/0.45  # Proof object conjectures             : 21
% 0.19/0.45  # Proof object clause conjectures      : 18
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 20
% 0.19/0.45  # Proof object initial formulas used   : 15
% 0.19/0.45  # Proof object generating inferences   : 19
% 0.19/0.45  # Proof object simplifying inferences  : 41
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 15
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 24
% 0.19/0.45  # Removed in clause preprocessing      : 0
% 0.19/0.45  # Initial clauses in saturation        : 24
% 0.19/0.45  # Processed clauses                    : 680
% 0.19/0.45  # ...of these trivial                  : 4
% 0.19/0.45  # ...subsumed                          : 413
% 0.19/0.45  # ...remaining for further processing  : 263
% 0.19/0.45  # Other redundant clauses eliminated   : 2
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 30
% 0.19/0.45  # Backward-rewritten                   : 10
% 0.19/0.45  # Generated clauses                    : 2489
% 0.19/0.45  # ...of the previous two non-trivial   : 2224
% 0.19/0.45  # Contextual simplify-reflections      : 32
% 0.19/0.45  # Paramodulations                      : 2487
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 2
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 198
% 0.19/0.45  #    Positive orientable unit clauses  : 17
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 3
% 0.19/0.45  #    Non-unit-clauses                  : 178
% 0.19/0.45  # Current number of unprocessed clauses: 1547
% 0.19/0.45  # ...number of literals in the above   : 10182
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 63
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 9408
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 2628
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 472
% 0.19/0.45  # Unit Clause-clause subsumption calls : 93
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 15
% 0.19/0.45  # BW rewrite match successes           : 7
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 71301
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.098 s
% 0.19/0.45  # System time              : 0.006 s
% 0.19/0.45  # Total time               : 0.104 s
% 0.19/0.45  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
