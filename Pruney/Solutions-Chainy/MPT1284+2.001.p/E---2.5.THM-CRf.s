%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   87 (4262 expanded)
%              Number of clauses        :   66 (1561 expanded)
%              Number of leaves         :   10 (1053 expanded)
%              Depth                    :   26
%              Number of atoms          :  298 (33095 expanded)
%              Number of equality atoms :   34 (1201 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( ( v4_pre_topc(X4,X2)
                        & v4_tops_1(X4,X2) )
                     => v5_tops_1(X4,X2) )
                    & ( v5_tops_1(X3,X1)
                     => ( v4_pre_topc(X3,X1)
                        & v4_tops_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(d7_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v5_tops_1(X2,X1)
          <=> X2 = k2_pre_topc(X1,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t31_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & r1_tarski(X3,X2) )
               => r1_tarski(k2_pre_topc(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(projectivity_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(d6_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
          <=> ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
              & r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( ( v4_pre_topc(X4,X2)
                          & v4_tops_1(X4,X2) )
                       => v5_tops_1(X4,X2) )
                      & ( v5_tops_1(X3,X1)
                       => ( v4_pre_topc(X3,X1)
                          & v4_tops_1(X3,X1) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tops_1])).

fof(c_0_11,plain,(
    ! [X22,X23] :
      ( ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | v4_pre_topc(k2_pre_topc(X22,X23),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( ( ~ v5_tops_1(X19,X18)
        | X19 = k2_pre_topc(X18,k1_tops_1(X18,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( X19 != k2_pre_topc(X18,k1_tops_1(X18,X19))
        | v5_tops_1(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).

fof(c_0_13,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | m1_subset_1(k1_tops_1(X20,X21),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_14,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ v4_pre_topc(X25,X24)
      | ~ r1_tarski(X26,X25)
      | r1_tarski(k2_pre_topc(X24,X26),X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).

fof(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( v5_tops_1(esk3_0,esk1_0)
      | v4_pre_topc(esk4_0,esk2_0) )
    & ( ~ v4_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | v4_pre_topc(esk4_0,esk2_0) )
    & ( v5_tops_1(esk3_0,esk1_0)
      | v4_tops_1(esk4_0,esk2_0) )
    & ( ~ v4_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | v4_tops_1(esk4_0,esk2_0) )
    & ( v5_tops_1(esk3_0,esk1_0)
      | ~ v5_tops_1(esk4_0,esk2_0) )
    & ( ~ v4_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | ~ v5_tops_1(esk4_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

cnf(c_0_16,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X1 = k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ v5_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_pre_topc(X1,X3),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v5_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | r1_tarski(X12,k2_pre_topc(X11,X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk3_0),X1)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_30,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0)
    | ~ v5_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_21]),c_0_24]),c_0_22])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,esk4_0),X1)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0)
    | v4_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk3_0),esk3_0)
    | ~ v5_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_21]),c_0_31])])).

cnf(c_0_37,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0)
    | r1_tarski(k2_pre_topc(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_26]),c_0_31])])).

cnf(c_0_38,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_pre_topc(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,esk4_0),esk4_0)
    | r1_tarski(k2_pre_topc(esk1_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_40,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | k2_pre_topc(X9,k2_pre_topc(X9,X10)) = k2_pre_topc(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

fof(c_0_41,plain,(
    ! [X13,X14,X15] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
      | ~ r1_tarski(X14,X15)
      | r1_tarski(k2_pre_topc(X13,X14),k2_pre_topc(X13,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

cnf(c_0_42,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0
    | r1_tarski(k2_pre_topc(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_26]),c_0_27])])).

fof(c_0_43,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(k1_tops_1(X16,k2_pre_topc(X16,X17)),X17)
        | ~ v4_tops_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( r1_tarski(X17,k2_pre_topc(X16,k1_tops_1(X16,X17)))
        | ~ v4_tops_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( ~ r1_tarski(k1_tops_1(X16,k2_pre_topc(X16,X17)),X17)
        | ~ r1_tarski(X17,k2_pre_topc(X16,k1_tops_1(X16,X17)))
        | v4_tops_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

cnf(c_0_44,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0
    | k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_42]),c_0_21]),c_0_22])])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ v4_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ v5_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_17]),c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0)
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | r1_tarski(k2_pre_topc(esk2_0,X1),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_26]),c_0_27])])).

cnf(c_0_51,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)
    | ~ v4_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_46]),c_0_26]),c_0_27])])).

cnf(c_0_52,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_21]),c_0_22])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))
    | ~ v4_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,X1)),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_18]),c_0_27])])).

cnf(c_0_55,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,X2)) = X2
    | ~ v4_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_26]),c_0_55])).

cnf(c_0_58,plain,
    ( v5_tops_1(X1,X2)
    | X1 != k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_59,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)) = esk4_0
    | k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_26]),c_0_27])]),c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0)
    | ~ v5_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_61,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | v5_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_26]),c_0_27])])).

cnf(c_0_62,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | v5_tops_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_63,plain,
    ( v4_tops_1(X2,X1)
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_62]),c_0_21]),c_0_22])])).

cnf(c_0_65,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_21]),c_0_22])])).

cnf(c_0_66,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk2_0)
    | ~ v4_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ v5_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_17]),c_0_31]),c_0_21]),c_0_22])])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ v5_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_17]),c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,esk4_0),esk4_0)
    | ~ v4_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_66]),c_0_26]),c_0_31])])).

cnf(c_0_70,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ v5_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_21]),c_0_22])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,esk4_0),esk4_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_30]),c_0_37])).

cnf(c_0_72,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v4_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_37]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_30]),c_0_49])).

cnf(c_0_75,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_73]),c_0_26]),c_0_27])])).

cnf(c_0_76,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_49]),c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,X1),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_75]),c_0_26]),c_0_27])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_75]),c_0_76]),c_0_26]),c_0_27])])).

cnf(c_0_79,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)) = esk4_0
    | ~ m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_77]),c_0_76]),c_0_26]),c_0_27]),c_0_78])])).

cnf(c_0_80,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_18]),c_0_26]),c_0_27])])).

cnf(c_0_81,negated_conjecture,
    ( ~ v4_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0)
    | ~ v5_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_82,negated_conjecture,
    ( v5_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_80]),c_0_26]),c_0_27])])).

cnf(c_0_83,negated_conjecture,
    ( ~ v5_tops_1(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_30]),c_0_60])).

cnf(c_0_84,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_82])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_82])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_84])]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t106_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((v4_pre_topc(X4,X2)&v4_tops_1(X4,X2))=>v5_tops_1(X4,X2))&(v5_tops_1(X3,X1)=>(v4_pre_topc(X3,X1)&v4_tops_1(X3,X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tops_1)).
% 0.13/0.38  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.13/0.38  fof(d7_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v5_tops_1(X2,X1)<=>X2=k2_pre_topc(X1,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 0.13/0.38  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.13/0.38  fof(t31_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&r1_tarski(X3,X2))=>r1_tarski(k2_pre_topc(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.13/0.38  fof(projectivity_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 0.13/0.38  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 0.13/0.38  fof(d6_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)<=>(r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)&r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((v4_pre_topc(X4,X2)&v4_tops_1(X4,X2))=>v5_tops_1(X4,X2))&(v5_tops_1(X3,X1)=>(v4_pre_topc(X3,X1)&v4_tops_1(X3,X1))))))))), inference(assume_negation,[status(cth)],[t106_tops_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X22, X23]:(~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|v4_pre_topc(k2_pre_topc(X22,X23),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.13/0.38  fof(c_0_12, plain, ![X18, X19]:((~v5_tops_1(X19,X18)|X19=k2_pre_topc(X18,k1_tops_1(X18,X19))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(X19!=k2_pre_topc(X18,k1_tops_1(X18,X19))|v5_tops_1(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X20, X21]:(~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|m1_subset_1(k1_tops_1(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.13/0.38  fof(c_0_14, plain, ![X24, X25, X26]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~v4_pre_topc(X25,X24)|~r1_tarski(X26,X25)|r1_tarski(k2_pre_topc(X24,X26),X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((((v5_tops_1(esk3_0,esk1_0)|v4_pre_topc(esk4_0,esk2_0))&(~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|v4_pre_topc(esk4_0,esk2_0)))&((v5_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0))&(~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0))))&((v5_tops_1(esk3_0,esk1_0)|~v5_tops_1(esk4_0,esk2_0))&(~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|~v5_tops_1(esk4_0,esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_17, plain, (X1=k2_pre_topc(X2,k1_tops_1(X2,X1))|~v5_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_18, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_19, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  cnf(c_0_20, plain, (r1_tarski(k2_pre_topc(X1,X3),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_23, plain, (v4_pre_topc(X1,X2)|~v2_pre_topc(X2)|~v5_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_28, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|r1_tarski(X12,k2_pre_topc(X11,X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk3_0),X1)|~v4_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (v4_pre_topc(esk3_0,esk1_0)|~v5_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_21]), c_0_24]), c_0_22])])).
% 0.13/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,esk4_0),X1)|~v4_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (v5_tops_1(esk3_0,esk1_0)|v4_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_34, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_35, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk3_0),esk3_0)|~v5_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_21]), c_0_31])])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (v5_tops_1(esk3_0,esk1_0)|r1_tarski(k2_pre_topc(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_26]), c_0_31])])).
% 0.13/0.38  cnf(c_0_38, plain, (k2_pre_topc(X1,X2)=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_pre_topc(X1,X2),X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,esk4_0),esk4_0)|r1_tarski(k2_pre_topc(esk1_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  fof(c_0_40, plain, ![X9, X10]:(~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|k2_pre_topc(X9,k2_pre_topc(X9,X10))=k2_pre_topc(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).
% 0.13/0.38  fof(c_0_41, plain, ![X13, X14, X15]:(~l1_pre_topc(X13)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|(~r1_tarski(X14,X15)|r1_tarski(k2_pre_topc(X13,X14),k2_pre_topc(X13,X15)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k2_pre_topc(esk2_0,esk4_0)=esk4_0|r1_tarski(k2_pre_topc(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_26]), c_0_27])])).
% 0.13/0.38  fof(c_0_43, plain, ![X16, X17]:(((r1_tarski(k1_tops_1(X16,k2_pre_topc(X16,X17)),X17)|~v4_tops_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(r1_tarski(X17,k2_pre_topc(X16,k1_tops_1(X16,X17)))|~v4_tops_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16)))&(~r1_tarski(k1_tops_1(X16,k2_pre_topc(X16,X17)),X17)|~r1_tarski(X17,k2_pre_topc(X16,k1_tops_1(X16,X17)))|v4_tops_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).
% 0.13/0.38  cnf(c_0_44, plain, (k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_45, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k2_pre_topc(esk2_0,esk4_0)=esk4_0|k2_pre_topc(esk1_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_42]), c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_47, plain, (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~v4_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_48, plain, (k2_pre_topc(X1,X2)=X2|~v5_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (v5_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|r1_tarski(k2_pre_topc(esk2_0,X1),esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)|~v4_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_46]), c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|v4_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_53, plain, (r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))|~v4_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,X1)),esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_18]), c_0_27])])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.38  cnf(c_0_56, plain, (k2_pre_topc(X1,k1_tops_1(X1,X2))=X2|~v4_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_34, c_0_53])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_26]), c_0_55])).
% 0.13/0.38  cnf(c_0_58, plain, (v5_tops_1(X1,X2)|X1!=k2_pre_topc(X2,k1_tops_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))=esk4_0|k2_pre_topc(esk1_0,esk3_0)=esk3_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_26]), c_0_27])]), c_0_52])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (v5_tops_1(esk3_0,esk1_0)|~v5_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|v5_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|v5_tops_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.38  cnf(c_0_63, plain, (v4_tops_1(X2,X1)|~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_62]), c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (v4_tops_1(esk3_0,esk1_0)|~r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (v4_pre_topc(esk4_0,esk2_0)|~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (v4_tops_1(esk3_0,esk1_0)|~v5_tops_1(esk3_0,esk1_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_17]), c_0_31]), c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_68, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~v5_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,esk4_0),esk4_0)|~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_66]), c_0_26]), c_0_31])])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (v4_tops_1(esk3_0,esk1_0)|~v5_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,esk4_0),esk4_0)|~v4_tops_1(esk3_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_30]), c_0_37])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,esk4_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_37]), c_0_71])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_30]), c_0_49])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (k2_pre_topc(esk2_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_73]), c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_49]), c_0_74])).
% 0.13/0.38  cnf(c_0_77, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,X1),esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_75]), c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_75]), c_0_76]), c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))=esk4_0|~m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_77]), c_0_76]), c_0_26]), c_0_27]), c_0_78])])).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_18]), c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, (~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|~v5_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, (v5_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_80]), c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (~v5_tops_1(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_30]), c_0_60])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (v5_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_82])])).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_82])])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_84])]), c_0_85]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 87
% 0.13/0.38  # Proof object clause steps            : 66
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 50
% 0.13/0.38  # Proof object clause conjectures      : 47
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 24
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 38
% 0.13/0.38  # Proof object simplifying inferences  : 91
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 27
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 27
% 0.13/0.38  # Processed clauses                    : 159
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 25
% 0.13/0.38  # ...remaining for further processing  : 132
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 13
% 0.13/0.38  # Backward-rewritten                   : 36
% 0.13/0.38  # Generated clauses                    : 256
% 0.13/0.38  # ...of the previous two non-trivial   : 202
% 0.13/0.38  # Contextual simplify-reflections      : 15
% 0.13/0.38  # Paramodulations                      : 254
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 55
% 0.13/0.38  #    Positive orientable unit clauses  : 14
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 40
% 0.13/0.38  # Current number of unprocessed clauses: 89
% 0.13/0.38  # ...number of literals in the above   : 454
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 75
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1220
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 540
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 51
% 0.13/0.38  # Unit Clause-clause subsumption calls : 37
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 8
% 0.13/0.38  # BW rewrite match successes           : 8
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 8310
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.038 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.044 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
