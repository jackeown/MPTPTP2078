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
% DateTime   : Thu Dec  3 11:14:09 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 (11799 expanded)
%              Number of clauses        :   61 (4384 expanded)
%              Number of leaves         :   10 (2832 expanded)
%              Depth                    :   19
%              Number of atoms          :  315 (65919 expanded)
%              Number of equality atoms :   51 (3253 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_compts_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_compts_1(X2,X1)
                  & r1_tarski(X3,X2)
                  & v4_pre_topc(X3,X1) )
               => v2_compts_1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(t34_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v4_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v4_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t12_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( X2 = k1_xboole_0
             => ( v2_compts_1(X2,X1)
              <=> v1_compts_1(k1_pre_topc(X1,X2)) ) )
            & ( v2_pre_topc(X1)
             => ( X2 = k1_xboole_0
                | ( v2_compts_1(X2,X1)
                <=> v1_compts_1(k1_pre_topc(X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

fof(t17_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v1_compts_1(X1)
              & v4_pre_topc(X2,X1) )
           => v2_compts_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).

fof(t28_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))
                 => ( ( X2 = X4
                      & r1_tarski(X2,X3) )
                   => k1_pre_topc(X1,X2) = k1_pre_topc(k1_pre_topc(X1,X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v2_compts_1(X2,X1)
                    & r1_tarski(X3,X2)
                    & v4_pre_topc(X3,X1) )
                 => v2_compts_1(X3,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_compts_1])).

fof(c_0_11,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | u1_struct_0(k1_pre_topc(X17,X18)) = X18 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v2_compts_1(esk2_0,esk1_0)
    & r1_tarski(esk3_0,esk2_0)
    & v4_pre_topc(esk3_0,esk1_0)
    & ~ v2_compts_1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ m1_pre_topc(X21,X19)
      | ~ v4_pre_topc(X20,X19)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | X22 != X20
      | v4_pre_topc(X22,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_tops_2])])])).

cnf(c_0_14,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v4_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X9,X10] :
      ( ( v1_pre_topc(k1_pre_topc(X9,X10))
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))) )
      & ( m1_pre_topc(k1_pre_topc(X9,X10),X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X11)
      | l1_pre_topc(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_19,plain,(
    ! [X23,X24] :
      ( ( ~ v2_compts_1(X24,X23)
        | v1_compts_1(k1_pre_topc(X23,X24))
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( ~ v1_compts_1(k1_pre_topc(X23,X24))
        | v2_compts_1(X24,X23)
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( ~ v2_compts_1(X24,X23)
        | v1_compts_1(k1_pre_topc(X23,X24))
        | X24 = k1_xboole_0
        | ~ v2_pre_topc(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( ~ v1_compts_1(k1_pre_topc(X23,X24))
        | v2_compts_1(X24,X23)
        | X24 = k1_xboole_0
        | ~ v2_pre_topc(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_compts_1])])])])).

cnf(c_0_20,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk1_0,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ v1_compts_1(X25)
      | ~ v4_pre_topc(X26,X25)
      | v2_compts_1(X26,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_compts_1])])])).

cnf(c_0_23,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X13,X15))))
      | X14 != X16
      | ~ r1_tarski(X14,X15)
      | k1_pre_topc(X13,X14) = k1_pre_topc(k1_pre_topc(X13,X15),X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_pre_topc])])])).

cnf(c_0_27,plain,
    ( v1_compts_1(k1_pre_topc(X2,X1))
    | X1 = k1_xboole_0
    | ~ v2_compts_1(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_29,plain,(
    ! [X7,X8] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | v2_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_30,plain,
    ( v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v4_pre_topc(X1,k1_pre_topc(X2,X3))
    | ~ v4_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( l1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ( ~ m1_subset_1(X5,k1_zfmisc_1(X6))
        | r1_tarski(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | m1_subset_1(X5,k1_zfmisc_1(X6)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_34,plain,
    ( k1_pre_topc(X1,X2) = k1_pre_topc(k1_pre_topc(X1,X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))
    | X2 != X4
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1))
    | ~ v2_compts_1(X1,k1_pre_topc(esk1_0,esk2_0))
    | ~ l1_pre_topc(k1_pre_topc(esk1_0,esk2_0))
    | ~ v2_pre_topc(k1_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v2_compts_1(X1,k1_pre_topc(X2,X3))
    | ~ v1_compts_1(k1_pre_topc(X2,X3))
    | ~ v4_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,plain,
    ( k1_pre_topc(k1_pre_topc(X1,X2),X3) = k1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1))
    | ~ v2_compts_1(X1,k1_pre_topc(esk1_0,esk2_0))
    | ~ v2_pre_topc(k1_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_15]),c_0_21])])).

cnf(c_0_46,plain,
    ( v2_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk1_0,X1))
    | ~ v1_compts_1(k1_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_15]),c_0_39])])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_40]),c_0_15]),c_0_41])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k1_pre_topc(k1_pre_topc(X1,esk2_0),esk3_0) = k1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,esk2_0))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_51,plain,
    ( v2_compts_1(X2,X1)
    | X2 = k1_xboole_0
    | ~ v1_compts_1(k1_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1))
    | ~ v2_compts_1(X1,k1_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_15]),c_0_41]),c_0_21])])).

cnf(c_0_54,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk3_0,k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_28]),c_0_49]),c_0_21])])).

cnf(c_0_55,negated_conjecture,
    ( k1_pre_topc(k1_pre_topc(esk1_0,esk2_0),esk3_0) = k1_pre_topc(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_41]),c_0_15]),c_0_28]),c_0_49]),c_0_21]),c_0_39])])).

cnf(c_0_56,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_compts_1(k1_pre_topc(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_39]),c_0_15]),c_0_41])]),c_0_52])).

cnf(c_0_57,plain,
    ( v1_compts_1(k1_pre_topc(X2,X1))
    | ~ v2_compts_1(X1,X2)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_49])]),c_0_56])).

cnf(c_0_59,plain,
    ( v1_compts_1(k1_pre_topc(X1,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,k1_xboole_0),X1))
    | ~ v2_compts_1(X1,k1_pre_topc(esk1_0,k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk1_0,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_59]),c_0_15])])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v2_compts_1(k1_xboole_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,k1_xboole_0),esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,k1_xboole_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63]),c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk1_0,k1_xboole_0)) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,k1_xboole_0),esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( k1_pre_topc(k1_pre_topc(esk1_0,k1_xboole_0),esk3_0) = k1_pre_topc(esk1_0,esk3_0)
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_56])).

cnf(c_0_70,plain,
    ( v2_compts_1(X2,X1)
    | ~ v1_compts_1(k1_pre_topc(X1,X2))
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_71,negated_conjecture,
    ( k1_pre_topc(k1_pre_topc(esk1_0,esk2_0),k1_xboole_0) = k1_pre_topc(esk1_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_69]),c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_69])).

cnf(c_0_73,plain,
    ( v2_compts_1(k1_xboole_0,X1)
    | ~ v1_compts_1(k1_pre_topc(X1,k1_xboole_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,k1_pre_topc(esk1_0,esk2_0))
    | ~ l1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_71]),c_0_28]),c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,k1_pre_topc(esk1_0,esk2_0))
    | ~ l1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_15]),c_0_75])]),c_0_76])).

cnf(c_0_78,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(k1_xboole_0,k1_pre_topc(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ l1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_80,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_32]),c_0_15]),c_0_21])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_80]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:21:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04AI
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t18_compts_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v2_compts_1(X2,X1)&r1_tarski(X3,X2))&v4_pre_topc(X3,X1))=>v2_compts_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 0.21/0.39  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.21/0.39  fof(t34_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 0.21/0.39  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.21/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.39  fof(t12_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((X2=k1_xboole_0=>(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))&(v2_pre_topc(X1)=>(X2=k1_xboole_0|(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_compts_1)).
% 0.21/0.39  fof(t17_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_compts_1(X1)&v4_pre_topc(X2,X1))=>v2_compts_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_compts_1)).
% 0.21/0.39  fof(t28_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))=>((X2=X4&r1_tarski(X2,X3))=>k1_pre_topc(X1,X2)=k1_pre_topc(k1_pre_topc(X1,X3),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_pre_topc)).
% 0.21/0.39  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.21/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v2_compts_1(X2,X1)&r1_tarski(X3,X2))&v4_pre_topc(X3,X1))=>v2_compts_1(X3,X1)))))), inference(assume_negation,[status(cth)],[t18_compts_1])).
% 0.21/0.39  fof(c_0_11, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|u1_struct_0(k1_pre_topc(X17,X18))=X18)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.21/0.39  fof(c_0_12, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((v2_compts_1(esk2_0,esk1_0)&r1_tarski(esk3_0,esk2_0))&v4_pre_topc(esk3_0,esk1_0))&~v2_compts_1(esk3_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.21/0.39  fof(c_0_13, plain, ![X19, X20, X21, X22]:(~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(~m1_pre_topc(X21,X19)|(~v4_pre_topc(X20,X19)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(X22!=X20|v4_pre_topc(X22,X21))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_tops_2])])])).
% 0.21/0.39  cnf(c_0_14, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_16, plain, (v4_pre_topc(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~v4_pre_topc(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  fof(c_0_17, plain, ![X9, X10]:((v1_pre_topc(k1_pre_topc(X9,X10))|(~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))))&(m1_pre_topc(k1_pre_topc(X9,X10),X9)|(~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.21/0.39  fof(c_0_18, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_pre_topc(X12,X11)|l1_pre_topc(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.39  fof(c_0_19, plain, ![X23, X24]:(((~v2_compts_1(X24,X23)|v1_compts_1(k1_pre_topc(X23,X24))|X24!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(~v1_compts_1(k1_pre_topc(X23,X24))|v2_compts_1(X24,X23)|X24!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))&((~v2_compts_1(X24,X23)|v1_compts_1(k1_pre_topc(X23,X24))|X24=k1_xboole_0|~v2_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(~v1_compts_1(k1_pre_topc(X23,X24))|v2_compts_1(X24,X23)|X24=k1_xboole_0|~v2_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_compts_1])])])])).
% 0.21/0.39  cnf(c_0_20, negated_conjecture, (u1_struct_0(k1_pre_topc(esk1_0,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  fof(c_0_22, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(~v1_compts_1(X25)|~v4_pre_topc(X26,X25)|v2_compts_1(X26,X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_compts_1])])])).
% 0.21/0.39  cnf(c_0_23, plain, (v4_pre_topc(X1,X2)|~v4_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_24, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_25, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  fof(c_0_26, plain, ![X13, X14, X15, X16]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X13,X15))))|(X14!=X16|~r1_tarski(X14,X15)|k1_pre_topc(X13,X14)=k1_pre_topc(k1_pre_topc(X13,X15),X16)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_pre_topc])])])).
% 0.21/0.39  cnf(c_0_27, plain, (v1_compts_1(k1_pre_topc(X2,X1))|X1=k1_xboole_0|~v2_compts_1(X1,X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (u1_struct_0(k1_pre_topc(esk1_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.39  fof(c_0_29, plain, ![X7, X8]:(~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|v2_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.21/0.39  cnf(c_0_30, plain, (v2_compts_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_compts_1(X1)|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_31, plain, (v4_pre_topc(X1,k1_pre_topc(X2,X3))|~v4_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.39  cnf(c_0_32, plain, (l1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.21/0.39  fof(c_0_33, plain, ![X5, X6]:((~m1_subset_1(X5,k1_zfmisc_1(X6))|r1_tarski(X5,X6))&(~r1_tarski(X5,X6)|m1_subset_1(X5,k1_zfmisc_1(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.39  cnf(c_0_34, plain, (k1_pre_topc(X1,X2)=k1_pre_topc(k1_pre_topc(X1,X3),X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))|X2!=X4|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (X1=k1_xboole_0|v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1))|~v2_compts_1(X1,k1_pre_topc(esk1_0,esk2_0))|~l1_pre_topc(k1_pre_topc(esk1_0,esk2_0))|~v2_pre_topc(k1_pre_topc(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.39  cnf(c_0_36, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_37, plain, (v2_compts_1(X1,k1_pre_topc(X2,X3))|~v1_compts_1(k1_pre_topc(X2,X3))|~v4_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (v4_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.39  cnf(c_0_43, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_44, plain, (k1_pre_topc(k1_pre_topc(X1,X2),X3)=k1_pre_topc(X1,X3)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_34])).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (X1=k1_xboole_0|v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1))|~v2_compts_1(X1,k1_pre_topc(esk1_0,esk2_0))|~v2_pre_topc(k1_pre_topc(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_32]), c_0_15]), c_0_21])])).
% 0.21/0.39  cnf(c_0_46, plain, (v2_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_36, c_0_24])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk1_0,X1))|~v1_compts_1(k1_pre_topc(esk1_0,X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,X1))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_15]), c_0_39])])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_40]), c_0_15]), c_0_41])])).
% 0.21/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (k1_pre_topc(k1_pre_topc(X1,esk2_0),esk3_0)=k1_pre_topc(X1,esk3_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,esk2_0))))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 0.21/0.39  cnf(c_0_51, plain, (v2_compts_1(X2,X1)|X2=k1_xboole_0|~v1_compts_1(k1_pre_topc(X1,X2))|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (~v2_compts_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_53, negated_conjecture, (X1=k1_xboole_0|v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X1))|~v2_compts_1(X1,k1_pre_topc(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_15]), c_0_41]), c_0_21])])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk3_0,k1_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_28]), c_0_49]), c_0_21])])).
% 0.21/0.39  cnf(c_0_55, negated_conjecture, (k1_pre_topc(k1_pre_topc(esk1_0,esk2_0),esk3_0)=k1_pre_topc(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_41]), c_0_15]), c_0_28]), c_0_49]), c_0_21]), c_0_39])])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (esk3_0=k1_xboole_0|~v1_compts_1(k1_pre_topc(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_39]), c_0_15]), c_0_41])]), c_0_52])).
% 0.21/0.39  cnf(c_0_57, plain, (v1_compts_1(k1_pre_topc(X2,X1))|~v2_compts_1(X1,X2)|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_49])]), c_0_56])).
% 0.21/0.39  cnf(c_0_59, plain, (v1_compts_1(k1_pre_topc(X1,k1_xboole_0))|~v2_compts_1(k1_xboole_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_57])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, (esk3_0=k1_xboole_0|X1=k1_xboole_0|v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,k1_xboole_0),X1))|~v2_compts_1(X1,k1_pre_topc(esk1_0,k1_xboole_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_53, c_0_58])).
% 0.21/0.39  cnf(c_0_61, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk1_0,k1_xboole_0))|~v2_compts_1(k1_xboole_0,esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,k1_xboole_0))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_59]), c_0_15])])).
% 0.21/0.39  cnf(c_0_62, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_49, c_0_58])).
% 0.21/0.39  cnf(c_0_63, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_21, c_0_58])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (esk3_0=k1_xboole_0|v2_compts_1(k1_xboole_0,esk1_0)), inference(spm,[status(thm)],[c_0_40, c_0_58])).
% 0.21/0.39  cnf(c_0_65, negated_conjecture, (esk3_0=k1_xboole_0|v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,k1_xboole_0),esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,k1_xboole_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63]), c_0_64])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, (u1_struct_0(k1_pre_topc(esk1_0,k1_xboole_0))=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_58])).
% 0.21/0.39  cnf(c_0_67, negated_conjecture, (esk3_0=k1_xboole_0|v1_compts_1(k1_pre_topc(k1_pre_topc(esk1_0,k1_xboole_0),esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_62])).
% 0.21/0.39  cnf(c_0_68, negated_conjecture, (k1_pre_topc(k1_pre_topc(esk1_0,k1_xboole_0),esk3_0)=k1_pre_topc(esk1_0,esk3_0)|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_58])).
% 0.21/0.39  cnf(c_0_69, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_56])).
% 0.21/0.39  cnf(c_0_70, plain, (v2_compts_1(X2,X1)|~v1_compts_1(k1_pre_topc(X1,X2))|X2!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_71, negated_conjecture, (k1_pre_topc(k1_pre_topc(esk1_0,esk2_0),k1_xboole_0)=k1_pre_topc(esk1_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_69]), c_0_69])).
% 0.21/0.39  cnf(c_0_72, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_49, c_0_69])).
% 0.21/0.39  cnf(c_0_73, plain, (v2_compts_1(k1_xboole_0,X1)|~v1_compts_1(k1_pre_topc(X1,k1_xboole_0))|~l1_pre_topc(X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_70])).
% 0.21/0.39  cnf(c_0_74, negated_conjecture, (v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))|~v2_compts_1(k1_xboole_0,k1_pre_topc(esk1_0,esk2_0))|~l1_pre_topc(k1_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_71]), c_0_28]), c_0_72])])).
% 0.21/0.39  cnf(c_0_75, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_39, c_0_69])).
% 0.21/0.39  cnf(c_0_76, negated_conjecture, (~v2_compts_1(k1_xboole_0,esk1_0)), inference(rw,[status(thm)],[c_0_52, c_0_69])).
% 0.21/0.39  cnf(c_0_77, negated_conjecture, (~v2_compts_1(k1_xboole_0,k1_pre_topc(esk1_0,esk2_0))|~l1_pre_topc(k1_pre_topc(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_15]), c_0_75])]), c_0_76])).
% 0.21/0.39  cnf(c_0_78, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(k1_xboole_0,k1_pre_topc(esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_54, c_0_69])).
% 0.21/0.39  cnf(c_0_79, negated_conjecture, (esk2_0=k1_xboole_0|~l1_pre_topc(k1_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.21/0.39  cnf(c_0_80, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_32]), c_0_15]), c_0_21])])).
% 0.21/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_80]), c_0_76]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 82
% 0.21/0.39  # Proof object clause steps            : 61
% 0.21/0.39  # Proof object formula steps           : 21
% 0.21/0.39  # Proof object conjectures             : 44
% 0.21/0.39  # Proof object clause conjectures      : 41
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 20
% 0.21/0.39  # Proof object initial formulas used   : 10
% 0.21/0.39  # Proof object generating inferences   : 31
% 0.21/0.39  # Proof object simplifying inferences  : 62
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 10
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 22
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 22
% 0.21/0.39  # Processed clauses                    : 190
% 0.21/0.39  # ...of these trivial                  : 3
% 0.21/0.39  # ...subsumed                          : 28
% 0.21/0.39  # ...remaining for further processing  : 159
% 0.21/0.39  # Other redundant clauses eliminated   : 4
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 18
% 0.21/0.39  # Backward-rewritten                   : 76
% 0.21/0.39  # Generated clauses                    : 187
% 0.21/0.39  # ...of the previous two non-trivial   : 221
% 0.21/0.39  # Contextual simplify-reflections      : 18
% 0.21/0.39  # Paramodulations                      : 183
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 4
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 39
% 0.21/0.39  #    Positive orientable unit clauses  : 8
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 2
% 0.21/0.39  #    Non-unit-clauses                  : 29
% 0.21/0.39  # Current number of unprocessed clauses: 59
% 0.21/0.39  # ...number of literals in the above   : 332
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 116
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 2091
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 445
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 60
% 0.21/0.39  # Unit Clause-clause subsumption calls : 59
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 5
% 0.21/0.39  # BW rewrite match successes           : 4
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 8633
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.041 s
% 0.21/0.39  # System time              : 0.005 s
% 0.21/0.39  # Total time               : 0.046 s
% 0.21/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
