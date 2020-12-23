%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:43 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 218 expanded)
%              Number of clauses        :   43 (  80 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   20
%              Number of atoms          :  270 ( 824 expanded)
%              Number of equality atoms :   42 ( 126 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t110_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
           => k1_tops_1(X1,k2_tops_1(X1,X2)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tops_1)).

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

fof(d5_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
          <=> v2_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(projectivity_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(t96_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => v3_tops_1(k2_tops_1(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tops_1)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_16,plain,(
    ! [X27,X28,X29] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ r1_tarski(X28,X29)
      | r1_tarski(k1_tops_1(X27,X28),k1_tops_1(X27,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

fof(c_0_17,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | k1_tops_1(X25,k1_tops_1(X25,X26)) = k1_tops_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | m1_subset_1(k1_tops_1(X17,X18),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_19,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,X2),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_tops_1(X2,X1)
             => k1_tops_1(X1,k2_tops_1(X1,X2)) = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t110_tops_1])).

cnf(c_0_26,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ r1_tarski(k1_tops_1(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_tops_1(esk2_0,esk1_0)
    & k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_28,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,X3),X2)
    | ~ r1_tarski(k1_tops_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k1_tops_1(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_32,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,X1)) = k1_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,X1)),esk2_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_22]),c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( k1_tops_1(esk1_0,X1) = k1_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_21]),c_0_30])])).

fof(c_0_34,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(k1_tops_1(X15,k2_pre_topc(X15,X16)),X16)
        | ~ v4_tops_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( r1_tarski(X16,k2_pre_topc(X15,k1_tops_1(X15,X16)))
        | ~ v4_tops_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ r1_tarski(k1_tops_1(X15,k2_pre_topc(X15,X16)),X16)
        | ~ r1_tarski(X16,k2_pre_topc(X15,k1_tops_1(X15,X16)))
        | v4_tops_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

fof(c_0_35,plain,(
    ! [X30,X31] :
      ( ( ~ v2_tops_1(X31,X30)
        | k1_tops_1(X30,X31) = k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( k1_tops_1(X30,X31) != k1_xboole_0
        | v2_tops_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

fof(c_0_36,plain,(
    ! [X13,X14] :
      ( ( ~ v3_tops_1(X14,X13)
        | v2_tops_1(k2_pre_topc(X13,X14),X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( ~ v2_tops_1(k2_pre_topc(X13,X14),X13)
        | v3_tops_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).

fof(c_0_37,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | m1_subset_1(k2_pre_topc(X7,X8),k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_38,negated_conjecture,
    ( k1_tops_1(esk1_0,X1) = k1_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_20]),c_0_29]),c_0_30])])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ v4_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( v4_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_41,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | r1_tarski(X12,k2_pre_topc(X11,X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_42,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( v2_tops_1(k2_pre_topc(X2,X1),X2)
    | ~ v3_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | m1_subset_1(k2_tops_1(X19,X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_46,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | k2_tops_1(X23,X24) = k7_subset_1(u1_struct_0(X23),k2_pre_topc(X23,X24),k1_tops_1(X23,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

fof(c_0_47,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | k2_pre_topc(X9,k2_pre_topc(X9,X10)) = k2_pre_topc(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

cnf(c_0_48,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_29]),c_0_30])])).

cnf(c_0_49,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( k1_tops_1(X1,k2_pre_topc(X1,X2)) = k1_xboole_0
    | ~ v3_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_51,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_29]),c_0_30])])).

cnf(c_0_55,plain,
    ( k1_tops_1(X1,k2_pre_topc(X1,k2_tops_1(X1,X2))) = k1_xboole_0
    | ~ v3_tops_1(k2_tops_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_56,plain,(
    ! [X32,X33] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ v4_pre_topc(X33,X32)
      | v3_tops_1(k2_tops_1(X32,X33),X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_tops_1])])])).

fof(c_0_57,plain,(
    ! [X21,X22] :
      ( ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | v4_pre_topc(k2_pre_topc(X21,X22),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_58,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,k2_pre_topc(X1,X2))) = k2_tops_1(X1,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_44]),c_0_29]),c_0_30])])).

cnf(c_0_60,plain,
    ( k1_tops_1(X1,k2_pre_topc(X1,k2_tops_1(X1,k2_pre_topc(X1,X2)))) = k1_xboole_0
    | ~ v3_tops_1(k2_tops_1(X1,k2_pre_topc(X1,X2)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_44])).

cnf(c_0_61,plain,
    ( v3_tops_1(k2_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_29]),c_0_30])])).

cnf(c_0_64,plain,
    ( k1_tops_1(X1,k2_pre_topc(X1,k2_tops_1(X1,k2_pre_topc(X1,X2)))) = k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_44]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_63]),c_0_29]),c_0_30])])).

cnf(c_0_66,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,k2_tops_1(esk1_0,esk2_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_29]),c_0_30])])).

fof(c_0_68,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,k1_xboole_0)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_xboole_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,k2_tops_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_67]),c_0_30])])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_xboole_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_49]),c_0_30])])).

cnf(c_0_72,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_44]),c_0_30])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_51]),c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.59  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.39/0.59  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.39/0.59  #
% 0.39/0.59  # Preprocessing time       : 0.028 s
% 0.39/0.59  # Presaturation interreduction done
% 0.39/0.59  
% 0.39/0.59  # Proof found!
% 0.39/0.59  # SZS status Theorem
% 0.39/0.59  # SZS output start CNFRefutation
% 0.39/0.59  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.39/0.59  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 0.39/0.59  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.39/0.59  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.39/0.59  fof(t110_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)=>k1_tops_1(X1,k2_tops_1(X1,X2))=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_tops_1)).
% 0.39/0.59  fof(d6_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)<=>(r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)&r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 0.39/0.59  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 0.39/0.59  fof(d5_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)<=>v2_tops_1(k2_pre_topc(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 0.39/0.59  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.39/0.59  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.39/0.59  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.39/0.59  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.39/0.59  fof(projectivity_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 0.39/0.59  fof(t96_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_tops_1(k2_tops_1(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tops_1)).
% 0.39/0.59  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.39/0.59  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.39/0.59  fof(c_0_16, plain, ![X27, X28, X29]:(~l1_pre_topc(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|(~r1_tarski(X28,X29)|r1_tarski(k1_tops_1(X27,X28),k1_tops_1(X27,X29)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.39/0.59  fof(c_0_17, plain, ![X25, X26]:(~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|k1_tops_1(X25,k1_tops_1(X25,X26))=k1_tops_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 0.39/0.59  fof(c_0_18, plain, ![X17, X18]:(~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|m1_subset_1(k1_tops_1(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.39/0.59  fof(c_0_19, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.39/0.59  cnf(c_0_20, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.39/0.59  cnf(c_0_21, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.59  cnf(c_0_22, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.59  cnf(c_0_23, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.59  cnf(c_0_24, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,X2),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.39/0.59  fof(c_0_25, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)=>k1_tops_1(X1,k2_tops_1(X1,X2))=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t110_tops_1])).
% 0.39/0.59  cnf(c_0_26, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~r1_tarski(k1_tops_1(X1,X3),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.39/0.59  fof(c_0_27, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v4_tops_1(esk2_0,esk1_0)&k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.39/0.59  cnf(c_0_28, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,X3),X2)|~r1_tarski(k1_tops_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.39/0.59  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.59  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.59  cnf(c_0_31, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k1_tops_1(esk1_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)|~r1_tarski(k1_tops_1(esk1_0,esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.39/0.59  cnf(c_0_32, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,X1))=k1_tops_1(esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,X1)),esk2_0)|~r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_22]), c_0_30])])).
% 0.39/0.59  cnf(c_0_33, negated_conjecture, (k1_tops_1(esk1_0,X1)=k1_tops_1(esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_21]), c_0_30])])).
% 0.39/0.59  fof(c_0_34, plain, ![X15, X16]:(((r1_tarski(k1_tops_1(X15,k2_pre_topc(X15,X16)),X16)|~v4_tops_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(r1_tarski(X16,k2_pre_topc(X15,k1_tops_1(X15,X16)))|~v4_tops_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15)))&(~r1_tarski(k1_tops_1(X15,k2_pre_topc(X15,X16)),X16)|~r1_tarski(X16,k2_pre_topc(X15,k1_tops_1(X15,X16)))|v4_tops_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).
% 0.39/0.59  fof(c_0_35, plain, ![X30, X31]:((~v2_tops_1(X31,X30)|k1_tops_1(X30,X31)=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(k1_tops_1(X30,X31)!=k1_xboole_0|v2_tops_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.39/0.59  fof(c_0_36, plain, ![X13, X14]:((~v3_tops_1(X14,X13)|v2_tops_1(k2_pre_topc(X13,X14),X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(~v2_tops_1(k2_pre_topc(X13,X14),X13)|v3_tops_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).
% 0.39/0.59  fof(c_0_37, plain, ![X7, X8]:(~l1_pre_topc(X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|m1_subset_1(k2_pre_topc(X7,X8),k1_zfmisc_1(u1_struct_0(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.39/0.59  cnf(c_0_38, negated_conjecture, (k1_tops_1(esk1_0,X1)=k1_tops_1(esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,X1),esk2_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_20]), c_0_29]), c_0_30])])).
% 0.39/0.59  cnf(c_0_39, plain, (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~v4_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.39/0.59  cnf(c_0_40, negated_conjecture, (v4_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.59  fof(c_0_41, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|r1_tarski(X12,k2_pre_topc(X11,X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.39/0.59  cnf(c_0_42, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.39/0.59  cnf(c_0_43, plain, (v2_tops_1(k2_pre_topc(X2,X1),X2)|~v3_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.39/0.59  cnf(c_0_44, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.39/0.59  fof(c_0_45, plain, ![X19, X20]:(~l1_pre_topc(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|m1_subset_1(k2_tops_1(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.39/0.59  fof(c_0_46, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|k2_tops_1(X23,X24)=k7_subset_1(u1_struct_0(X23),k2_pre_topc(X23,X24),k1_tops_1(X23,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.39/0.59  fof(c_0_47, plain, ![X9, X10]:(~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|k2_pre_topc(X9,k2_pre_topc(X9,X10))=k2_pre_topc(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).
% 0.39/0.59  cnf(c_0_48, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_29]), c_0_30])])).
% 0.39/0.59  cnf(c_0_49, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.39/0.59  cnf(c_0_50, plain, (k1_tops_1(X1,k2_pre_topc(X1,X2))=k1_xboole_0|~v3_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.39/0.59  cnf(c_0_51, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.39/0.59  cnf(c_0_52, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.39/0.59  cnf(c_0_53, plain, (k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.39/0.59  cnf(c_0_54, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_29]), c_0_30])])).
% 0.39/0.59  cnf(c_0_55, plain, (k1_tops_1(X1,k2_pre_topc(X1,k2_tops_1(X1,X2)))=k1_xboole_0|~v3_tops_1(k2_tops_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.39/0.59  fof(c_0_56, plain, ![X32, X33]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(~v4_pre_topc(X33,X32)|v3_tops_1(k2_tops_1(X32,X33),X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_tops_1])])])).
% 0.39/0.59  fof(c_0_57, plain, ![X21, X22]:(~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v4_pre_topc(k2_pre_topc(X21,X22),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.39/0.59  cnf(c_0_58, plain, (k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,k2_pre_topc(X1,X2)))=k2_tops_1(X1,k2_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_44])).
% 0.39/0.59  cnf(c_0_59, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_44]), c_0_29]), c_0_30])])).
% 0.39/0.59  cnf(c_0_60, plain, (k1_tops_1(X1,k2_pre_topc(X1,k2_tops_1(X1,k2_pre_topc(X1,X2))))=k1_xboole_0|~v3_tops_1(k2_tops_1(X1,k2_pre_topc(X1,X2)),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_55, c_0_44])).
% 0.39/0.59  cnf(c_0_61, plain, (v3_tops_1(k2_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.39/0.59  cnf(c_0_62, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.39/0.59  cnf(c_0_63, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_29]), c_0_30])])).
% 0.39/0.59  cnf(c_0_64, plain, (k1_tops_1(X1,k2_pre_topc(X1,k2_tops_1(X1,k2_pre_topc(X1,X2))))=k1_xboole_0|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_44]), c_0_62])).
% 0.39/0.59  cnf(c_0_65, negated_conjecture, (k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_63]), c_0_29]), c_0_30])])).
% 0.39/0.59  cnf(c_0_66, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.59  cnf(c_0_67, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,k2_tops_1(esk1_0,esk2_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_29]), c_0_30])])).
% 0.39/0.59  fof(c_0_68, plain, ![X6]:(~r1_tarski(X6,k1_xboole_0)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.39/0.59  cnf(c_0_69, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_xboole_0)|~m1_subset_1(k2_pre_topc(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k2_pre_topc(esk1_0,k2_tops_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_67]), c_0_30])])).
% 0.39/0.59  cnf(c_0_70, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.39/0.59  cnf(c_0_71, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_xboole_0)|~m1_subset_1(k2_pre_topc(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_49]), c_0_30])])).
% 0.39/0.59  cnf(c_0_72, negated_conjecture, (k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.59  cnf(c_0_73, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.39/0.59  cnf(c_0_74, negated_conjecture, (~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_44]), c_0_30])])).
% 0.39/0.59  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_51]), c_0_29]), c_0_30])]), ['proof']).
% 0.39/0.59  # SZS output end CNFRefutation
% 0.39/0.59  # Proof object total steps             : 76
% 0.39/0.59  # Proof object clause steps            : 43
% 0.39/0.59  # Proof object formula steps           : 33
% 0.39/0.59  # Proof object conjectures             : 23
% 0.39/0.59  # Proof object clause conjectures      : 20
% 0.39/0.59  # Proof object formula conjectures     : 3
% 0.39/0.59  # Proof object initial clauses used    : 20
% 0.39/0.59  # Proof object initial formulas used   : 16
% 0.39/0.59  # Proof object generating inferences   : 23
% 0.39/0.59  # Proof object simplifying inferences  : 44
% 0.39/0.59  # Training examples: 0 positive, 0 negative
% 0.39/0.59  # Parsed axioms                        : 16
% 0.39/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.59  # Initial clauses                      : 26
% 0.39/0.59  # Removed in clause preprocessing      : 0
% 0.39/0.59  # Initial clauses in saturation        : 26
% 0.39/0.59  # Processed clauses                    : 2027
% 0.39/0.59  # ...of these trivial                  : 26
% 0.39/0.59  # ...subsumed                          : 1190
% 0.39/0.59  # ...remaining for further processing  : 811
% 0.39/0.59  # Other redundant clauses eliminated   : 2
% 0.39/0.59  # Clauses deleted for lack of memory   : 0
% 0.39/0.59  # Backward-subsumed                    : 202
% 0.39/0.59  # Backward-rewritten                   : 174
% 0.39/0.59  # Generated clauses                    : 6679
% 0.39/0.59  # ...of the previous two non-trivial   : 5470
% 0.39/0.59  # Contextual simplify-reflections      : 113
% 0.39/0.59  # Paramodulations                      : 6677
% 0.39/0.59  # Factorizations                       : 0
% 0.39/0.59  # Equation resolutions                 : 2
% 0.39/0.59  # Propositional unsat checks           : 0
% 0.39/0.59  #    Propositional check models        : 0
% 0.39/0.59  #    Propositional check unsatisfiable : 0
% 0.39/0.59  #    Propositional clauses             : 0
% 0.39/0.59  #    Propositional clauses after purity: 0
% 0.39/0.59  #    Propositional unsat core size     : 0
% 0.39/0.59  #    Propositional preprocessing time  : 0.000
% 0.39/0.59  #    Propositional encoding time       : 0.000
% 0.39/0.59  #    Propositional solver time         : 0.000
% 0.39/0.59  #    Success case prop preproc time    : 0.000
% 0.39/0.59  #    Success case prop encoding time   : 0.000
% 0.39/0.59  #    Success case prop solver time     : 0.000
% 0.39/0.59  # Current number of processed clauses  : 408
% 0.39/0.59  #    Positive orientable unit clauses  : 17
% 0.39/0.59  #    Positive unorientable unit clauses: 0
% 0.39/0.59  #    Negative unit clauses             : 3
% 0.39/0.59  #    Non-unit-clauses                  : 388
% 0.39/0.59  # Current number of unprocessed clauses: 3399
% 0.39/0.59  # ...number of literals in the above   : 21244
% 0.39/0.59  # Current number of archived formulas  : 0
% 0.39/0.59  # Current number of archived clauses   : 401
% 0.39/0.59  # Clause-clause subsumption calls (NU) : 58297
% 0.39/0.59  # Rec. Clause-clause subsumption calls : 16606
% 0.39/0.59  # Non-unit clause-clause subsumptions  : 1463
% 0.39/0.59  # Unit Clause-clause subsumption calls : 883
% 0.39/0.59  # Rewrite failures with RHS unbound    : 0
% 0.39/0.59  # BW rewrite match attempts            : 14
% 0.39/0.59  # BW rewrite match successes           : 9
% 0.39/0.59  # Condensation attempts                : 0
% 0.39/0.59  # Condensation successes               : 0
% 0.39/0.59  # Termbank termtop insertions          : 206883
% 0.39/0.59  
% 0.39/0.59  # -------------------------------------------------
% 0.39/0.59  # User time                : 0.237 s
% 0.39/0.59  # System time              : 0.012 s
% 0.39/0.59  # Total time               : 0.249 s
% 0.39/0.59  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
