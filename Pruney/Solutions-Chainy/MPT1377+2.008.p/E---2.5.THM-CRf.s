%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:18 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 844 expanded)
%              Number of clauses        :   64 ( 378 expanded)
%              Number of leaves         :   12 ( 212 expanded)
%              Depth                    :   23
%              Number of atoms          :  346 (3451 expanded)
%              Number of equality atoms :   11 ( 162 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(t33_compts_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_compts_1(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t28_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( X3 = X4
                   => ( v2_compts_1(X3,X1)
                    <=> v2_compts_1(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(c_0_12,plain,(
    ! [X6] : m1_subset_1(k2_subset_1(X6),k1_zfmisc_1(X6)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_13,plain,(
    ! [X5] : k2_subset_1(X5) = X5 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_14,plain,(
    ! [X16,X17,X18] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_19,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | u1_struct_0(k1_pre_topc(X14,X15)) = X15 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_20,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)))
      | m1_pre_topc(X20,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_21,plain,(
    ! [X9,X10] :
      ( ( v1_pre_topc(k1_pre_topc(X9,X10))
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))) )
      & ( m1_pre_topc(k1_pre_topc(X9,X10),X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_compts_1(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          <=> ( v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_compts_1])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(k1_pre_topc(X3,X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2),X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ( ~ v2_compts_1(esk2_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      | ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) )
    & ( v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | v2_compts_1(esk2_0,esk1_0) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | v2_compts_1(esk2_0,esk1_0) )
    & ( v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X7,X8] :
      ( ( v1_pre_topc(g1_pre_topc(X7,X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))) )
      & ( l1_pre_topc(g1_pre_topc(X7,X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_35,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_36,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | m1_subset_1(u1_pre_topc(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_37,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X11)
      | l1_pre_topc(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_38,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ v2_compts_1(X25,X23)
        | v2_compts_1(X26,X24)
        | X25 != X26
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ v2_compts_1(X26,X24)
        | v2_compts_1(X25,X23)
        | X25 != X26
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_compts_1])])])])).

fof(c_0_39,plain,(
    ! [X21,X22] :
      ( ( ~ m1_pre_topc(X21,X22)
        | m1_pre_topc(X21,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( ~ m1_pre_topc(X21,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | m1_pre_topc(X21,X22)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(k1_pre_topc(X3,X4),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( v2_compts_1(X3,X4)
    | ~ v2_compts_1(X1,X2)
    | X1 != X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_32])])).

cnf(c_0_48,plain,
    ( l1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_25])).

cnf(c_0_49,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_17])).

cnf(c_0_50,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_32])])).

cnf(c_0_52,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(X2))
    | ~ m1_pre_topc(X1,k1_pre_topc(X3,X2))
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_48])).

cnf(c_0_53,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_51]),c_0_32])])).

cnf(c_0_56,plain,
    ( m1_subset_1(u1_struct_0(k1_pre_topc(k1_pre_topc(X1,X2),X3)),k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_25]),c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0)
    | v2_compts_1(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_32])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(k1_pre_topc(X2,esk2_0),X3))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,esk2_0))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,plain,
    ( v2_compts_1(X3,X4)
    | ~ v2_compts_1(X1,X2)
    | X3 != X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X2,X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0)
    | v2_compts_1(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,esk2_0))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_23]),c_0_48])).

cnf(c_0_62,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_59]),c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0)
    | v2_compts_1(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_42]),c_0_32])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ m1_pre_topc(k1_pre_topc(X3,X4),X2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,esk2_0))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_18])).

cnf(c_0_66,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,k1_pre_topc(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_25])).

cnf(c_0_67,negated_conjecture,
    ( v2_compts_1(esk2_0,k1_pre_topc(X1,X2))
    | v2_compts_1(esk2_0,esk1_0)
    | ~ m1_pre_topc(k1_pre_topc(X1,X2),esk1_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_23])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_25])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(u1_struct_0(k1_pre_topc(X1,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_18])).

cnf(c_0_70,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0)
    | v2_compts_1(esk2_0,X1)
    | ~ m1_pre_topc(k1_pre_topc(X1,X2),esk1_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,esk2_0))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_32])])).

cnf(c_0_72,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_25]),c_0_32])])).

cnf(c_0_73,plain,
    ( v2_compts_1(X1,k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3))
    | ~ v2_compts_1(X1,X2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(u1_struct_0(k1_pre_topc(X1,esk2_0)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_18])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_76,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_23]),c_0_32])])).

cnf(c_0_77,plain,
    ( v2_compts_1(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v2_compts_1(X1,X2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_23])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_47]),c_0_32])])).

cnf(c_0_80,negated_conjecture,
    ( ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_47])])).

cnf(c_0_81,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_47]),c_0_18])])).

cnf(c_0_82,plain,
    ( v2_compts_1(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v2_compts_1(X1,X2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_23])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_18])])).

cnf(c_0_84,negated_conjecture,
    ( ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_85,negated_conjecture,
    ( v2_compts_1(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v2_compts_1(X1,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_32])])).

cnf(c_0_86,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_81]),c_0_18])]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_35])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_42]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:22:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.49  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S5PRR_RG_S0Y
% 0.18/0.49  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.49  #
% 0.18/0.49  # Preprocessing time       : 0.029 s
% 0.18/0.49  
% 0.18/0.49  # Proof found!
% 0.18/0.49  # SZS status Theorem
% 0.18/0.49  # SZS output start CNFRefutation
% 0.18/0.49  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.18/0.49  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.18/0.49  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.18/0.49  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.18/0.49  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.18/0.49  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.18/0.49  fof(t33_compts_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_compts_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_compts_1)).
% 0.18/0.49  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.18/0.49  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.18/0.49  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.18/0.49  fof(t28_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X3=X4=>(v2_compts_1(X3,X1)<=>v2_compts_1(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_compts_1)).
% 0.18/0.49  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.18/0.49  fof(c_0_12, plain, ![X6]:m1_subset_1(k2_subset_1(X6),k1_zfmisc_1(X6)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.18/0.49  fof(c_0_13, plain, ![X5]:k2_subset_1(X5)=X5, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.18/0.49  fof(c_0_14, plain, ![X16, X17, X18]:(~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.18/0.49  cnf(c_0_15, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.49  cnf(c_0_16, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.49  cnf(c_0_17, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.49  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.49  fof(c_0_19, plain, ![X14, X15]:(~l1_pre_topc(X14)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|u1_struct_0(k1_pre_topc(X14,X15))=X15)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.18/0.49  fof(c_0_20, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)))|m1_pre_topc(X20,X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.18/0.49  fof(c_0_21, plain, ![X9, X10]:((v1_pre_topc(k1_pre_topc(X9,X10))|(~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))))&(m1_pre_topc(k1_pre_topc(X9,X10),X9)|(~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.18/0.49  cnf(c_0_22, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.49  cnf(c_0_23, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.49  cnf(c_0_24, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.49  cnf(c_0_25, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.49  fof(c_0_26, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_compts_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))))), inference(assume_negation,[status(cth)],[t33_compts_1])).
% 0.18/0.49  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(k1_pre_topc(X3,X1),X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.49  cnf(c_0_28, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2),X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.49  fof(c_0_29, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|(~v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))))&(((v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|v2_compts_1(esk2_0,esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|v2_compts_1(esk2_0,esk1_0)))&((v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])])).
% 0.18/0.49  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.49  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.49  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.49  fof(c_0_33, plain, ![X7, X8]:((v1_pre_topc(g1_pre_topc(X7,X8))|~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))))&(l1_pre_topc(g1_pre_topc(X7,X8))|~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.18/0.49  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.18/0.49  cnf(c_0_35, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.49  fof(c_0_36, plain, ![X13]:(~l1_pre_topc(X13)|m1_subset_1(u1_pre_topc(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.18/0.49  fof(c_0_37, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_pre_topc(X12,X11)|l1_pre_topc(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.18/0.49  fof(c_0_38, plain, ![X23, X24, X25, X26]:((~v2_compts_1(X25,X23)|v2_compts_1(X26,X24)|X25!=X26|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X24,X23)|~l1_pre_topc(X23))&(~v2_compts_1(X26,X24)|v2_compts_1(X25,X23)|X25!=X26|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X24,X23)|~l1_pre_topc(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_compts_1])])])])).
% 0.18/0.49  fof(c_0_39, plain, ![X21, X22]:((~m1_pre_topc(X21,X22)|m1_pre_topc(X21,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))|~l1_pre_topc(X22)|~l1_pre_topc(X21))&(~m1_pre_topc(X21,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))|m1_pre_topc(X21,X22)|~l1_pre_topc(X22)|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.18/0.49  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(k1_pre_topc(X3,X4),X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_17, c_0_23])).
% 0.18/0.49  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.49  cnf(c_0_42, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.49  cnf(c_0_43, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.49  cnf(c_0_44, plain, (v2_compts_1(X3,X4)|~v2_compts_1(X1,X2)|X1!=X3|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.49  cnf(c_0_45, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.49  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_40, c_0_25])).
% 0.18/0.49  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_32])])).
% 0.18/0.49  cnf(c_0_48, plain, (l1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_43, c_0_25])).
% 0.18/0.49  cnf(c_0_49, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_44]), c_0_17])).
% 0.18/0.49  cnf(c_0_50, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_45, c_0_43])).
% 0.18/0.49  cnf(c_0_51, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_32])])).
% 0.18/0.49  cnf(c_0_52, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(X2))|~m1_pre_topc(X1,k1_pre_topc(X3,X2))|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_48])).
% 0.18/0.49  cnf(c_0_53, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~m1_pre_topc(X2,X3)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.18/0.49  cnf(c_0_54, negated_conjecture, (v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|v2_compts_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.49  cnf(c_0_55, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X2,k1_zfmisc_1(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_51]), c_0_32])])).
% 0.18/0.49  cnf(c_0_56, plain, (m1_subset_1(u1_struct_0(k1_pre_topc(k1_pre_topc(X1,X2),X3)),k1_zfmisc_1(X2))|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_25]), c_0_48])).
% 0.18/0.49  cnf(c_0_57, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)|v2_compts_1(esk2_0,X1)|~m1_pre_topc(X1,esk1_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_32])])).
% 0.18/0.49  cnf(c_0_58, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(k1_pre_topc(X2,esk2_0),X3))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,esk2_0))))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.49  cnf(c_0_59, plain, (v2_compts_1(X3,X4)|~v2_compts_1(X1,X2)|X3!=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X2,X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.49  cnf(c_0_60, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)|v2_compts_1(esk2_0,X1)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_57, c_0_35])).
% 0.18/0.49  cnf(c_0_61, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,esk2_0))))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_23]), c_0_48])).
% 0.18/0.49  cnf(c_0_62, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,X3)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_59]), c_0_17])).
% 0.18/0.49  cnf(c_0_63, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)|v2_compts_1(esk2_0,X1)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_42]), c_0_32])])).
% 0.18/0.49  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~m1_pre_topc(k1_pre_topc(X3,X4),X2)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_40, c_0_50])).
% 0.18/0.49  cnf(c_0_65, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,esk2_0))))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_61, c_0_18])).
% 0.18/0.49  cnf(c_0_66, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,k1_pre_topc(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_62, c_0_25])).
% 0.18/0.49  cnf(c_0_67, negated_conjecture, (v2_compts_1(esk2_0,k1_pre_topc(X1,X2))|v2_compts_1(esk2_0,esk1_0)|~m1_pre_topc(k1_pre_topc(X1,X2),esk1_0)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_63, c_0_23])).
% 0.18/0.49  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_64, c_0_25])).
% 0.18/0.49  cnf(c_0_69, negated_conjecture, (m1_subset_1(u1_struct_0(k1_pre_topc(X1,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~l1_pre_topc(X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_65, c_0_18])).
% 0.18/0.49  cnf(c_0_70, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)|v2_compts_1(esk2_0,X1)|~m1_pre_topc(k1_pre_topc(X1,X2),esk1_0)|~l1_pre_topc(X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.18/0.49  cnf(c_0_71, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,esk2_0))))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_32])])).
% 0.18/0.49  cnf(c_0_72, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,X1))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_25]), c_0_32])])).
% 0.18/0.49  cnf(c_0_73, plain, (v2_compts_1(X1,k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3))|~v2_compts_1(X1,X2)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), inference(spm,[status(thm)],[c_0_49, c_0_28])).
% 0.18/0.49  cnf(c_0_74, negated_conjecture, (m1_subset_1(u1_struct_0(k1_pre_topc(X1,esk2_0)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_71, c_0_18])).
% 0.18/0.49  cnf(c_0_75, negated_conjecture, (~v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.49  cnf(c_0_76, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_23]), c_0_32])])).
% 0.18/0.49  cnf(c_0_77, plain, (v2_compts_1(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v2_compts_1(X1,X2)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), inference(spm,[status(thm)],[c_0_66, c_0_73])).
% 0.18/0.49  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_74, c_0_23])).
% 0.18/0.49  cnf(c_0_79, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_47]), c_0_32])])).
% 0.18/0.49  cnf(c_0_80, negated_conjecture, (~v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_47])])).
% 0.18/0.49  cnf(c_0_81, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_47]), c_0_18])])).
% 0.18/0.49  cnf(c_0_82, plain, (v2_compts_1(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v2_compts_1(X1,X2)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_77, c_0_23])).
% 0.18/0.49  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_18])])).
% 0.18/0.49  cnf(c_0_84, negated_conjecture, (~v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.18/0.49  cnf(c_0_85, negated_conjecture, (v2_compts_1(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v2_compts_1(X1,esk1_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_32])])).
% 0.18/0.49  cnf(c_0_86, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_81]), c_0_18])]), c_0_83])).
% 0.18/0.49  cnf(c_0_87, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_86, c_0_35])).
% 0.18/0.49  cnf(c_0_88, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_42]), c_0_32])]), ['proof']).
% 0.18/0.49  # SZS output end CNFRefutation
% 0.18/0.49  # Proof object total steps             : 89
% 0.18/0.49  # Proof object clause steps            : 64
% 0.18/0.49  # Proof object formula steps           : 25
% 0.18/0.49  # Proof object conjectures             : 35
% 0.18/0.49  # Proof object clause conjectures      : 32
% 0.18/0.49  # Proof object formula conjectures     : 3
% 0.18/0.49  # Proof object initial clauses used    : 16
% 0.18/0.49  # Proof object initial formulas used   : 12
% 0.18/0.49  # Proof object generating inferences   : 42
% 0.18/0.49  # Proof object simplifying inferences  : 45
% 0.18/0.49  # Training examples: 0 positive, 0 negative
% 0.18/0.49  # Parsed axioms                        : 12
% 0.18/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.49  # Initial clauses                      : 23
% 0.18/0.49  # Removed in clause preprocessing      : 1
% 0.18/0.49  # Initial clauses in saturation        : 22
% 0.18/0.49  # Processed clauses                    : 545
% 0.18/0.49  # ...of these trivial                  : 0
% 0.18/0.49  # ...subsumed                          : 242
% 0.18/0.49  # ...remaining for further processing  : 303
% 0.18/0.49  # Other redundant clauses eliminated   : 2
% 0.18/0.49  # Clauses deleted for lack of memory   : 0
% 0.18/0.49  # Backward-subsumed                    : 31
% 0.18/0.49  # Backward-rewritten                   : 23
% 0.18/0.49  # Generated clauses                    : 2408
% 0.18/0.49  # ...of the previous two non-trivial   : 2373
% 0.18/0.49  # Contextual simplify-reflections      : 69
% 0.18/0.49  # Paramodulations                      : 2406
% 0.18/0.49  # Factorizations                       : 0
% 0.18/0.49  # Equation resolutions                 : 2
% 0.18/0.49  # Propositional unsat checks           : 0
% 0.18/0.49  #    Propositional check models        : 0
% 0.18/0.49  #    Propositional check unsatisfiable : 0
% 0.18/0.49  #    Propositional clauses             : 0
% 0.18/0.49  #    Propositional clauses after purity: 0
% 0.18/0.49  #    Propositional unsat core size     : 0
% 0.18/0.49  #    Propositional preprocessing time  : 0.000
% 0.18/0.49  #    Propositional encoding time       : 0.000
% 0.18/0.49  #    Propositional solver time         : 0.000
% 0.18/0.49  #    Success case prop preproc time    : 0.000
% 0.18/0.49  #    Success case prop encoding time   : 0.000
% 0.18/0.49  #    Success case prop solver time     : 0.000
% 0.18/0.49  # Current number of processed clauses  : 247
% 0.18/0.49  #    Positive orientable unit clauses  : 5
% 0.18/0.49  #    Positive unorientable unit clauses: 0
% 0.18/0.49  #    Negative unit clauses             : 3
% 0.18/0.49  #    Non-unit-clauses                  : 239
% 0.18/0.49  # Current number of unprocessed clauses: 1781
% 0.18/0.49  # ...number of literals in the above   : 13760
% 0.18/0.49  # Current number of archived formulas  : 0
% 0.18/0.49  # Current number of archived clauses   : 55
% 0.18/0.49  # Clause-clause subsumption calls (NU) : 38681
% 0.18/0.49  # Rec. Clause-clause subsumption calls : 5237
% 0.18/0.49  # Non-unit clause-clause subsumptions  : 341
% 0.18/0.49  # Unit Clause-clause subsumption calls : 94
% 0.18/0.49  # Rewrite failures with RHS unbound    : 0
% 0.18/0.49  # BW rewrite match attempts            : 7
% 0.18/0.49  # BW rewrite match successes           : 2
% 0.18/0.50  # Condensation attempts                : 0
% 0.18/0.50  # Condensation successes               : 0
% 0.18/0.50  # Termbank termtop insertions          : 126150
% 0.18/0.50  
% 0.18/0.50  # -------------------------------------------------
% 0.18/0.50  # User time                : 0.157 s
% 0.18/0.50  # System time              : 0.005 s
% 0.18/0.50  # Total time               : 0.162 s
% 0.18/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
