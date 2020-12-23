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
% DateTime   : Thu Dec  3 11:12:40 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 877 expanded)
%              Number of clauses        :   54 ( 333 expanded)
%              Number of leaves         :   15 ( 216 expanded)
%              Depth                    :   13
%              Number of atoms          :  318 (6556 expanded)
%              Number of equality atoms :   43 ( 319 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(t107_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( ( v3_pre_topc(X4,X2)
                        & v4_tops_1(X4,X2) )
                     => v6_tops_1(X4,X2) )
                    & ( v6_tops_1(X3,X1)
                     => ( v3_pre_topc(X3,X1)
                        & v4_tops_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d6_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
          <=> ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
              & r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(d8_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_tops_1(X2,X1)
          <=> X2 = k1_tops_1(X1,k2_pre_topc(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t58_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,k1_tops_1(X1,X2)) = k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_1)).

fof(c_0_15,plain,(
    ! [X27,X28] :
      ( ( ~ v4_pre_topc(X28,X27)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X27),X28),X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X27),X28),X27)
        | v4_pre_topc(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k3_subset_1(X9,k3_subset_1(X9,X10)) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | m1_subset_1(k3_subset_1(X7,X8),k1_zfmisc_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ( ~ v4_pre_topc(X16,X15)
        | k2_pre_topc(X15,X16) = X16
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ v2_pre_topc(X15)
        | k2_pre_topc(X15,X16) != X16
        | v4_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_19,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k1_tops_1(X17,X18) = k3_subset_1(u1_struct_0(X17),k2_pre_topc(X17,k3_subset_1(u1_struct_0(X17),X18))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_23,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( ( v3_pre_topc(X4,X2)
                          & v4_tops_1(X4,X2) )
                       => v6_tops_1(X4,X2) )
                      & ( v6_tops_1(X3,X1)
                       => ( v3_pre_topc(X3,X1)
                          & v4_tops_1(X3,X1) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t107_tops_1])).

cnf(c_0_26,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21])).

fof(c_0_28,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_29,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(k1_tops_1(X19,k2_pre_topc(X19,X20)),X20)
        | ~ v4_tops_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( r1_tarski(X20,k2_pre_topc(X19,k1_tops_1(X19,X20)))
        | ~ v4_tops_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ r1_tarski(k1_tops_1(X19,k2_pre_topc(X19,X20)),X20)
        | ~ r1_tarski(X20,k2_pre_topc(X19,k1_tops_1(X19,X20)))
        | v4_tops_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

fof(c_0_30,plain,(
    ! [X21,X22] :
      ( ( ~ v6_tops_1(X22,X21)
        | X22 = k1_tops_1(X21,k2_pre_topc(X21,X22))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( X22 != k1_tops_1(X21,k2_pre_topc(X21,X22))
        | v6_tops_1(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_tops_1])])])])).

fof(c_0_31,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( v6_tops_1(esk3_0,esk1_0)
      | v3_pre_topc(esk4_0,esk2_0) )
    & ( ~ v3_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | v3_pre_topc(esk4_0,esk2_0) )
    & ( v6_tops_1(esk3_0,esk1_0)
      | v4_tops_1(esk4_0,esk2_0) )
    & ( ~ v3_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | v4_tops_1(esk4_0,esk2_0) )
    & ( v6_tops_1(esk3_0,esk1_0)
      | ~ v6_tops_1(esk4_0,esk2_0) )
    & ( ~ v3_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | ~ v6_tops_1(esk4_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])])).

cnf(c_0_32,plain,
    ( k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)) = k1_tops_1(X1,X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,plain,(
    ! [X25,X26] :
      ( ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | v3_pre_topc(k1_tops_1(X25,X26),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_34,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | m1_subset_1(k1_tops_1(X23,X24),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ v4_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X29,X30,X31] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ v3_pre_topc(X30,X29)
      | ~ r1_tarski(X30,X31)
      | r1_tarski(X30,k1_tops_1(X29,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

fof(c_0_38,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | r1_tarski(X14,k2_pre_topc(X13,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_40,plain,
    ( v6_tops_1(X1,X2)
    | X1 != k1_tops_1(X2,k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_32])).

cnf(c_0_44,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k1_tops_1(X1,k2_pre_topc(X1,X2)) = X2
    | ~ v4_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,k2_pre_topc(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( X1 = k1_tops_1(X2,k2_pre_topc(X2,X1))
    | ~ v6_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0)
    | ~ v6_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_54,negated_conjecture,
    ( v6_tops_1(esk4_0,esk2_0)
    | k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_55,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_56,plain,
    ( k1_tops_1(X1,k2_pre_topc(X1,X2)) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ v4_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | ~ v6_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_58,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0)
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0)
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0)
    | k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)) != esk4_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0)
    | ~ v6_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_62,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,k2_pre_topc(X1,X2))) = k1_tops_1(X1,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)) = esk4_0
    | ~ v3_pre_topc(esk4_0,esk2_0)
    | ~ v4_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_41]),c_0_42])])).

cnf(c_0_64,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)) != esk4_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_60])).

fof(c_0_67,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | k2_pre_topc(X32,k1_tops_1(X32,X33)) = k2_pre_topc(X32,k1_tops_1(X32,k2_pre_topc(X32,k1_tops_1(X32,X33)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_tops_1])])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_69,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_70,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_71,negated_conjecture,
    ( k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)) != esk4_0
    | ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_54])).

cnf(c_0_72,plain,
    ( v3_pre_topc(k1_tops_1(X1,k2_pre_topc(X1,X2)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(X1,k2_pre_topc(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_75,plain,
    ( v4_tops_1(X2,X1)
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_76,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,X2)) = k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_52]),c_0_51])])).

cnf(c_0_80,plain,
    ( v4_tops_1(k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))),k2_pre_topc(X1,k1_tops_1(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])])).

cnf(c_0_81,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_73]),c_0_74]),c_0_52]),c_0_51])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_73]),c_0_52]),c_0_73]),c_0_51]),c_0_51]),c_0_73]),c_0_73]),c_0_81])]),c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_48]),c_0_52]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.030 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 0.19/0.41  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.41  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.41  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.19/0.41  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 0.19/0.41  fof(t107_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((v3_pre_topc(X4,X2)&v4_tops_1(X4,X2))=>v6_tops_1(X4,X2))&(v6_tops_1(X3,X1)=>(v3_pre_topc(X3,X1)&v4_tops_1(X3,X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(d6_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)<=>(r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)&r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 0.19/0.41  fof(d8_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_tops_1(X2,X1)<=>X2=k1_tops_1(X1,k2_pre_topc(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 0.19/0.41  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.19/0.41  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.19/0.41  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 0.19/0.41  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.19/0.41  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.19/0.41  fof(t58_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,k1_tops_1(X1,X2))=k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_tops_1)).
% 0.19/0.41  fof(c_0_15, plain, ![X27, X28]:((~v4_pre_topc(X28,X27)|v3_pre_topc(k3_subset_1(u1_struct_0(X27),X28),X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X27),X28),X27)|v4_pre_topc(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 0.19/0.41  fof(c_0_16, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|k3_subset_1(X9,k3_subset_1(X9,X10))=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.41  fof(c_0_17, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|m1_subset_1(k3_subset_1(X7,X8),k1_zfmisc_1(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.41  fof(c_0_18, plain, ![X15, X16]:((~v4_pre_topc(X16,X15)|k2_pre_topc(X15,X16)=X16|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(~v2_pre_topc(X15)|k2_pre_topc(X15,X16)!=X16|v4_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.19/0.41  cnf(c_0_19, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_20, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_21, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  fof(c_0_22, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|k1_tops_1(X17,X18)=k3_subset_1(u1_struct_0(X17),k2_pre_topc(X17,k3_subset_1(u1_struct_0(X17),X18))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.19/0.41  cnf(c_0_23, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_24, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.41  fof(c_0_25, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((v3_pre_topc(X4,X2)&v4_tops_1(X4,X2))=>v6_tops_1(X4,X2))&(v6_tops_1(X3,X1)=>(v3_pre_topc(X3,X1)&v4_tops_1(X3,X1))))))))), inference(assume_negation,[status(cth)],[t107_tops_1])).
% 0.19/0.41  cnf(c_0_26, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_27, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k3_subset_1(u1_struct_0(X1),X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21])).
% 0.19/0.41  fof(c_0_28, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  fof(c_0_29, plain, ![X19, X20]:(((r1_tarski(k1_tops_1(X19,k2_pre_topc(X19,X20)),X20)|~v4_tops_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(r1_tarski(X20,k2_pre_topc(X19,k1_tops_1(X19,X20)))|~v4_tops_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19)))&(~r1_tarski(k1_tops_1(X19,k2_pre_topc(X19,X20)),X20)|~r1_tarski(X20,k2_pre_topc(X19,k1_tops_1(X19,X20)))|v4_tops_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).
% 0.19/0.41  fof(c_0_30, plain, ![X21, X22]:((~v6_tops_1(X22,X21)|X22=k1_tops_1(X21,k2_pre_topc(X21,X22))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&(X22!=k1_tops_1(X21,k2_pre_topc(X21,X22))|v6_tops_1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_tops_1])])])])).
% 0.19/0.41  fof(c_0_31, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((((v6_tops_1(esk3_0,esk1_0)|v3_pre_topc(esk4_0,esk2_0))&(~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|v3_pre_topc(esk4_0,esk2_0)))&((v6_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0))&(~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0))))&((v6_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0))&(~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])])).
% 0.19/0.41  cnf(c_0_32, plain, (k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))=k1_tops_1(X1,X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.41  fof(c_0_33, plain, ![X25, X26]:(~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|v3_pre_topc(k1_tops_1(X25,X26),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.19/0.41  fof(c_0_34, plain, ![X23, X24]:(~l1_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|m1_subset_1(k1_tops_1(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.19/0.41  cnf(c_0_35, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_36, plain, (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~v4_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  fof(c_0_37, plain, ![X29, X30, X31]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(~v3_pre_topc(X30,X29)|~r1_tarski(X30,X31)|r1_tarski(X30,k1_tops_1(X29,X31)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.19/0.41  fof(c_0_38, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|r1_tarski(X14,k2_pre_topc(X13,X14)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.19/0.41  fof(c_0_39, plain, ![X11, X12]:(~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.19/0.41  cnf(c_0_40, plain, (v6_tops_1(X1,X2)|X1!=k1_tops_1(X2,k2_pre_topc(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_43, plain, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_20, c_0_32])).
% 0.19/0.41  cnf(c_0_44, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_45, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_46, plain, (k1_tops_1(X1,k2_pre_topc(X1,X2))=X2|~v4_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k1_tops_1(X1,k2_pre_topc(X1,X2)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.41  cnf(c_0_47, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.41  cnf(c_0_48, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  cnf(c_0_49, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.41  cnf(c_0_50, plain, (X1=k1_tops_1(X2,k2_pre_topc(X2,X1))|~v6_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (v6_tops_1(esk4_0,esk2_0)|k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.19/0.41  cnf(c_0_55, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.19/0.41  cnf(c_0_56, plain, (k1_tops_1(X1,k2_pre_topc(X1,X2))=X2|~v3_pre_topc(X2,X1)|~v4_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|~v6_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)|v3_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)|k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))!=esk4_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_62, plain, (k1_tops_1(X1,k1_tops_1(X1,k2_pre_topc(X1,X2)))=k1_tops_1(X1,k2_pre_topc(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_55, c_0_49])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))=esk4_0|~v3_pre_topc(esk4_0,esk2_0)|~v4_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_41]), c_0_42])])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|v4_tops_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|v3_pre_topc(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_57, c_0_59])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))!=esk4_0), inference(spm,[status(thm)],[c_0_57, c_0_60])).
% 0.19/0.41  fof(c_0_67, plain, ![X32, X33]:(~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|k2_pre_topc(X32,k1_tops_1(X32,X33))=k2_pre_topc(X32,k1_tops_1(X32,k2_pre_topc(X32,k1_tops_1(X32,X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_tops_1])])])).
% 0.19/0.41  cnf(c_0_68, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))!=esk4_0|~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_61, c_0_54])).
% 0.19/0.41  cnf(c_0_72, plain, (v3_pre_topc(k1_tops_1(X1,k2_pre_topc(X1,X2)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k1_tops_1(X1,k2_pre_topc(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_44, c_0_62])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_66])).
% 0.19/0.41  cnf(c_0_74, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_75, plain, (v4_tops_1(X2,X1)|~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_76, plain, (k2_pre_topc(X1,k1_tops_1(X1,X2))=k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.41  cnf(c_0_77, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_68])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_69]), c_0_70]), c_0_71])).
% 0.19/0.41  cnf(c_0_79, negated_conjecture, (v3_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_52]), c_0_51])])).
% 0.19/0.41  cnf(c_0_80, plain, (v4_tops_1(k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))),X1)|~l1_pre_topc(X1)|~m1_subset_1(k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))),k2_pre_topc(X1,k1_tops_1(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])])).
% 0.19/0.41  cnf(c_0_81, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_73]), c_0_74]), c_0_52]), c_0_51])])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79])])).
% 0.19/0.41  cnf(c_0_83, negated_conjecture, (~r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_73]), c_0_52]), c_0_73]), c_0_51]), c_0_51]), c_0_73]), c_0_73]), c_0_81])]), c_0_82])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_48]), c_0_52]), c_0_51])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 85
% 0.19/0.41  # Proof object clause steps            : 54
% 0.19/0.41  # Proof object formula steps           : 31
% 0.19/0.41  # Proof object conjectures             : 29
% 0.19/0.41  # Proof object clause conjectures      : 26
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 28
% 0.19/0.41  # Proof object initial formulas used   : 15
% 0.19/0.41  # Proof object generating inferences   : 24
% 0.19/0.41  # Proof object simplifying inferences  : 41
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 15
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 32
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 32
% 0.19/0.41  # Processed clauses                    : 338
% 0.19/0.41  # ...of these trivial                  : 7
% 0.19/0.41  # ...subsumed                          : 104
% 0.19/0.41  # ...remaining for further processing  : 227
% 0.19/0.41  # Other redundant clauses eliminated   : 2
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 25
% 0.19/0.41  # Backward-rewritten                   : 53
% 0.19/0.41  # Generated clauses                    : 978
% 0.19/0.41  # ...of the previous two non-trivial   : 868
% 0.19/0.41  # Contextual simplify-reflections      : 33
% 0.19/0.41  # Paramodulations                      : 975
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 2
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 115
% 0.19/0.41  #    Positive orientable unit clauses  : 10
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 2
% 0.19/0.41  #    Non-unit-clauses                  : 103
% 0.19/0.41  # Current number of unprocessed clauses: 591
% 0.19/0.41  # ...number of literals in the above   : 3190
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 110
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 7440
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 2848
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 156
% 0.19/0.41  # Unit Clause-clause subsumption calls : 309
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 4
% 0.19/0.41  # BW rewrite match successes           : 4
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 32272
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.064 s
% 0.19/0.41  # System time              : 0.009 s
% 0.19/0.41  # Total time               : 0.073 s
% 0.19/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
