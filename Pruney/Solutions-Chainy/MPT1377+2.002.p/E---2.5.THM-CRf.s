%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:17 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 (17228 expanded)
%              Number of clauses        :   77 (7176 expanded)
%              Number of leaves         :   11 (4402 expanded)
%              Depth                    :   28
%              Number of atoms          :  390 (82029 expanded)
%              Number of equality atoms :   63 (8873 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

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

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X17 = X19
        | g1_pre_topc(X17,X18) != g1_pre_topc(X19,X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( X18 = X20
        | g1_pre_topc(X17,X18) != g1_pre_topc(X19,X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_12,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | m1_subset_1(u1_pre_topc(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_13,negated_conjecture,(
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

cnf(c_0_14,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_17,plain,(
    ! [X6,X7,X8] :
      ( ( X8 != k1_pre_topc(X6,X7)
        | k2_struct_0(X8) = X7
        | ~ v1_pre_topc(X8)
        | ~ m1_pre_topc(X8,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( k2_struct_0(X8) != X7
        | X8 = k1_pre_topc(X6,X7)
        | ~ v1_pre_topc(X8)
        | ~ m1_pre_topc(X8,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ( v1_pre_topc(k1_pre_topc(X11,X12))
        | ~ l1_pre_topc(X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11))) )
      & ( m1_pre_topc(k1_pre_topc(X11,X12),X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

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

fof(c_0_20,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

cnf(c_0_21,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X9,X10] :
      ( ( v1_pre_topc(g1_pre_topc(X9,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) )
      & ( l1_pre_topc(g1_pre_topc(X9,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_24,plain,
    ( X1 = k1_pre_topc(X3,X2)
    | k2_struct_0(X1) != X2
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
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

fof(c_0_29,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | l1_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_30,plain,
    ( v1_compts_1(k1_pre_topc(X2,X1))
    | X1 = k1_xboole_0
    | ~ v2_compts_1(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_33,plain,(
    ! [X16] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_34,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22])])).

cnf(c_0_35,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k1_pre_topc(X1,k2_struct_0(X2)) = X2
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_39,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | v2_compts_1(esk2_0,esk1_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_42,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_46,plain,
    ( k1_pre_topc(X1,X2) = k1_pre_topc(X3,X2)
    | ~ m1_pre_topc(k1_pre_topc(X3,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_26])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | v2_compts_1(esk2_0,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])])).

cnf(c_0_49,plain,
    ( m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,plain,
    ( l1_pre_topc(k1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_52,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_15])).

cnf(c_0_53,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = k1_pre_topc(X3,X2)
    | ~ m1_pre_topc(k1_pre_topc(X3,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_36])).

cnf(c_0_55,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_44])])).

cnf(c_0_57,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = k1_pre_topc(X3,X2)
    | ~ m1_pre_topc(k1_pre_topc(X3,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_15]),c_0_44])])).

cnf(c_0_59,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = k1_pre_topc(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(esk1_0,esk2_0))
    | ~ v2_compts_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_56]),c_0_43]),c_0_44])])).

cnf(c_0_61,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = k1_pre_topc(X3,X2)
    | ~ m1_pre_topc(k1_pre_topc(X3,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_36]),c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(esk1_0,esk2_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_56]),c_0_44])]),c_0_31]),c_0_60])).

cnf(c_0_63,plain,
    ( v2_compts_1(X2,X1)
    | X2 = k1_xboole_0
    | ~ v1_compts_1(k1_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) = k1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(k1_pre_topc(X1,esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_56]),c_0_44])])).

cnf(c_0_65,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_36])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) = k1_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_56]),c_0_44])])).

cnf(c_0_68,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_15]),c_0_44])])).

cnf(c_0_69,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_56]),c_0_44])]),c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_42]),c_0_43]),c_0_44])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_36])).

cnf(c_0_73,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,esk1_0)
    | ~ v1_compts_1(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_56]),c_0_43]),c_0_44])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_56])])).

cnf(c_0_75,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_15]),c_0_44])])).

cnf(c_0_76,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_78,plain,
    ( v2_compts_1(X2,X1)
    | ~ v1_compts_1(k1_pre_topc(X1,X2))
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_79,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_52]),c_0_56]),c_0_44])])).

cnf(c_0_80,plain,
    ( v2_compts_1(k1_xboole_0,X1)
    | ~ v1_compts_1(k1_pre_topc(X1,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_79]),c_0_79]),c_0_79])).

cnf(c_0_82,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_compts_1(k1_pre_topc(X1,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_59])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_44])])).

cnf(c_0_85,plain,
    ( v1_compts_1(k1_pre_topc(X2,X1))
    | ~ v2_compts_1(X1,X2)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_52]),c_0_83]),c_0_44])])).

cnf(c_0_87,plain,
    ( v1_compts_1(k1_pre_topc(X1,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_83]),c_0_44])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_36])).

cnf(c_0_90,negated_conjecture,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v2_compts_1(k1_xboole_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_79]),c_0_79])).

cnf(c_0_91,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_15]),c_0_44])])).

cnf(c_0_92,negated_conjecture,
    ( v2_compts_1(k1_xboole_0,esk1_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_79]),c_0_79])).

cnf(c_0_93,plain,
    ( v1_compts_1(k1_pre_topc(X1,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_59])).

cnf(c_0_94,negated_conjecture,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(sr,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(sr,[status(thm)],[c_0_92,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_83]),c_0_44])]),c_0_95])])).

cnf(c_0_97,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_96]),c_0_83]),c_0_44])]),c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_36])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_15]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.58  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.58  #
% 0.19/0.58  # Preprocessing time       : 0.039 s
% 0.19/0.58  # Presaturation interreduction done
% 0.19/0.58  
% 0.19/0.58  # Proof found!
% 0.19/0.58  # SZS status Theorem
% 0.19/0.58  # SZS output start CNFRefutation
% 0.19/0.58  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.19/0.58  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.58  fof(t33_compts_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_compts_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_compts_1)).
% 0.19/0.58  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.19/0.58  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.19/0.58  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.19/0.58  fof(t12_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((X2=k1_xboole_0=>(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))&(v2_pre_topc(X1)=>(X2=k1_xboole_0|(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_compts_1)).
% 0.19/0.58  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.19/0.58  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.19/0.58  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.58  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.19/0.58  fof(c_0_11, plain, ![X17, X18, X19, X20]:((X17=X19|g1_pre_topc(X17,X18)!=g1_pre_topc(X19,X20)|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))&(X18=X20|g1_pre_topc(X17,X18)!=g1_pre_topc(X19,X20)|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.19/0.58  fof(c_0_12, plain, ![X15]:(~l1_pre_topc(X15)|m1_subset_1(u1_pre_topc(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.58  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_compts_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))))), inference(assume_negation,[status(cth)],[t33_compts_1])).
% 0.19/0.58  cnf(c_0_14, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.58  cnf(c_0_15, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.58  fof(c_0_16, plain, ![X5]:(~l1_pre_topc(X5)|(~v1_pre_topc(X5)|X5=g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.19/0.58  fof(c_0_17, plain, ![X6, X7, X8]:((X8!=k1_pre_topc(X6,X7)|k2_struct_0(X8)=X7|(~v1_pre_topc(X8)|~m1_pre_topc(X8,X6))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|~l1_pre_topc(X6))&(k2_struct_0(X8)!=X7|X8=k1_pre_topc(X6,X7)|(~v1_pre_topc(X8)|~m1_pre_topc(X8,X6))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|~l1_pre_topc(X6))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.19/0.58  fof(c_0_18, plain, ![X11, X12]:((v1_pre_topc(k1_pre_topc(X11,X12))|(~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))))&(m1_pre_topc(k1_pre_topc(X11,X12),X11)|(~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.19/0.58  fof(c_0_19, plain, ![X23, X24]:(((~v2_compts_1(X24,X23)|v1_compts_1(k1_pre_topc(X23,X24))|X24!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(~v1_compts_1(k1_pre_topc(X23,X24))|v2_compts_1(X24,X23)|X24!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))&((~v2_compts_1(X24,X23)|v1_compts_1(k1_pre_topc(X23,X24))|X24=k1_xboole_0|~v2_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(~v1_compts_1(k1_pre_topc(X23,X24))|v2_compts_1(X24,X23)|X24=k1_xboole_0|~v2_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_compts_1])])])])).
% 0.19/0.58  fof(c_0_20, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|(~v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))))&(((v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|v2_compts_1(esk2_0,esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|v2_compts_1(esk2_0,esk1_0)))&((v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).
% 0.19/0.58  cnf(c_0_21, plain, (u1_struct_0(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X2,X3)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.58  cnf(c_0_22, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.58  fof(c_0_23, plain, ![X9, X10]:((v1_pre_topc(g1_pre_topc(X9,X10))|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))))&(l1_pre_topc(g1_pre_topc(X9,X10))|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.19/0.58  cnf(c_0_24, plain, (X1=k1_pre_topc(X3,X2)|k2_struct_0(X1)!=X2|~v1_pre_topc(X1)|~m1_pre_topc(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.58  cnf(c_0_25, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.58  cnf(c_0_26, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.58  cnf(c_0_27, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.58  fof(c_0_28, plain, ![X21, X22]:((~m1_pre_topc(X21,X22)|m1_pre_topc(X21,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))|~l1_pre_topc(X22)|~l1_pre_topc(X21))&(~m1_pre_topc(X21,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))|m1_pre_topc(X21,X22)|~l1_pre_topc(X22)|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.19/0.58  fof(c_0_29, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|l1_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.58  cnf(c_0_30, plain, (v1_compts_1(k1_pre_topc(X2,X1))|X1=k1_xboole_0|~v2_compts_1(X1,X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.58  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|v2_compts_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.58  cnf(c_0_32, negated_conjecture, (v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|v2_compts_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.58  fof(c_0_33, plain, ![X16]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.19/0.58  cnf(c_0_34, plain, (u1_struct_0(g1_pre_topc(X1,X2))=X1|~v1_pre_topc(g1_pre_topc(X1,X2))|~l1_pre_topc(g1_pre_topc(X1,X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22])])).
% 0.19/0.58  cnf(c_0_35, plain, (v1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.58  cnf(c_0_36, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.58  cnf(c_0_37, plain, (k1_pre_topc(X1,k2_struct_0(X2))=X2|~m1_pre_topc(X2,X1)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~v1_pre_topc(X2)|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.58  cnf(c_0_38, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_26]), c_0_27])).
% 0.19/0.58  cnf(c_0_39, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.58  cnf(c_0_40, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.58  cnf(c_0_41, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))|v2_compts_1(esk2_0,esk1_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.19/0.58  cnf(c_0_42, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.58  cnf(c_0_43, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.58  cnf(c_0_44, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.58  cnf(c_0_45, plain, (u1_struct_0(g1_pre_topc(X1,X2))=X1|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.58  cnf(c_0_46, plain, (k1_pre_topc(X1,X2)=k1_pre_topc(X3,X2)|~m1_pre_topc(k1_pre_topc(X3,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~l1_pre_topc(X1)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_26])).
% 0.19/0.58  cnf(c_0_47, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.58  cnf(c_0_48, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))|v2_compts_1(esk2_0,esk1_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44])])).
% 0.19/0.58  cnf(c_0_49, plain, (m1_pre_topc(X1,X2)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.58  cnf(c_0_50, plain, (l1_pre_topc(k1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_27])).
% 0.19/0.58  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.58  cnf(c_0_52, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_15])).
% 0.19/0.58  cnf(c_0_53, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)=k1_pre_topc(X3,X2)|~m1_pre_topc(k1_pre_topc(X3,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X3)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.58  cnf(c_0_54, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))|v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_48, c_0_36])).
% 0.19/0.58  cnf(c_0_55, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_50])).
% 0.19/0.58  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_44])])).
% 0.19/0.58  cnf(c_0_57, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)=k1_pre_topc(X3,X2)|~m1_pre_topc(k1_pre_topc(X3,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X3)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_53, c_0_52])).
% 0.19/0.58  cnf(c_0_58, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))|v2_compts_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_15]), c_0_44])])).
% 0.19/0.58  cnf(c_0_59, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)=k1_pre_topc(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_55])).
% 0.19/0.58  cnf(c_0_60, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(esk1_0,esk2_0))|~v2_compts_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_56]), c_0_43]), c_0_44])])).
% 0.19/0.58  cnf(c_0_61, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)=k1_pre_topc(X3,X2)|~m1_pre_topc(k1_pre_topc(X3,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~l1_pre_topc(X3)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_36]), c_0_15])).
% 0.19/0.58  cnf(c_0_62, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(esk1_0,esk2_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_56]), c_0_44])]), c_0_31]), c_0_60])).
% 0.19/0.58  cnf(c_0_63, plain, (v2_compts_1(X2,X1)|X2=k1_xboole_0|~v1_compts_1(k1_pre_topc(X1,X2))|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.58  cnf(c_0_64, negated_conjecture, (k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)=k1_pre_topc(X1,esk2_0)|~m1_pre_topc(k1_pre_topc(X1,esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_56]), c_0_44])])).
% 0.19/0.58  cnf(c_0_65, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(esk1_0,esk2_0))|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_62, c_0_36])).
% 0.19/0.58  cnf(c_0_66, plain, (X1=k1_xboole_0|v2_compts_1(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1))|~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_63, c_0_52])).
% 0.19/0.58  cnf(c_0_67, negated_conjecture, (k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)=k1_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_27]), c_0_56]), c_0_44])])).
% 0.19/0.58  cnf(c_0_68, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_15]), c_0_44])])).
% 0.19/0.58  cnf(c_0_69, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_56]), c_0_44])]), c_0_68])).
% 0.19/0.58  cnf(c_0_70, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_42]), c_0_43]), c_0_44])])).
% 0.19/0.58  cnf(c_0_71, negated_conjecture, (~v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.58  cnf(c_0_72, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_70, c_0_36])).
% 0.19/0.58  cnf(c_0_73, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,esk1_0)|~v1_compts_1(k1_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_56]), c_0_43]), c_0_44])])).
% 0.19/0.58  cnf(c_0_74, negated_conjecture, (~v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_56])])).
% 0.19/0.58  cnf(c_0_75, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_15]), c_0_44])])).
% 0.19/0.58  cnf(c_0_76, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_73, c_0_68])).
% 0.19/0.58  cnf(c_0_77, negated_conjecture, (esk2_0=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.19/0.58  cnf(c_0_78, plain, (v2_compts_1(X2,X1)|~v1_compts_1(k1_pre_topc(X1,X2))|X2!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.58  cnf(c_0_79, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_52]), c_0_56]), c_0_44])])).
% 0.19/0.58  cnf(c_0_80, plain, (v2_compts_1(k1_xboole_0,X1)|~v1_compts_1(k1_pre_topc(X1,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_78])).
% 0.19/0.58  cnf(c_0_81, negated_conjecture, (~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v2_compts_1(k1_xboole_0,esk1_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_79]), c_0_79]), c_0_79])).
% 0.19/0.58  cnf(c_0_82, plain, (v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v1_compts_1(k1_pre_topc(X1,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_80, c_0_59])).
% 0.19/0.58  cnf(c_0_83, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_56, c_0_79])).
% 0.19/0.58  cnf(c_0_84, negated_conjecture, (~v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))|~v2_compts_1(k1_xboole_0,esk1_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83]), c_0_44])])).
% 0.19/0.58  cnf(c_0_85, plain, (v1_compts_1(k1_pre_topc(X2,X1))|~v2_compts_1(X1,X2)|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.58  cnf(c_0_86, negated_conjecture, (~v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))|~v2_compts_1(k1_xboole_0,esk1_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_52]), c_0_83]), c_0_44])])).
% 0.19/0.58  cnf(c_0_87, plain, (v1_compts_1(k1_pre_topc(X1,k1_xboole_0))|~v2_compts_1(k1_xboole_0,X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_85])).
% 0.19/0.58  cnf(c_0_88, negated_conjecture, (~v2_compts_1(k1_xboole_0,esk1_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_83]), c_0_44])])).
% 0.19/0.58  cnf(c_0_89, negated_conjecture, (~v2_compts_1(k1_xboole_0,esk1_0)|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_88, c_0_36])).
% 0.19/0.58  cnf(c_0_90, negated_conjecture, (v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|v2_compts_1(k1_xboole_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_79]), c_0_79])).
% 0.19/0.58  cnf(c_0_91, negated_conjecture, (~v2_compts_1(k1_xboole_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_15]), c_0_44])])).
% 0.19/0.58  cnf(c_0_92, negated_conjecture, (v2_compts_1(k1_xboole_0,esk1_0)|m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_79]), c_0_79])).
% 0.19/0.58  cnf(c_0_93, plain, (v1_compts_1(k1_pre_topc(X1,k1_xboole_0))|~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_87, c_0_59])).
% 0.19/0.58  cnf(c_0_94, negated_conjecture, (v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(sr,[status(thm)],[c_0_90, c_0_91])).
% 0.19/0.58  cnf(c_0_95, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(sr,[status(thm)],[c_0_92, c_0_91])).
% 0.19/0.58  cnf(c_0_96, negated_conjecture, (v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_83]), c_0_44])]), c_0_95])])).
% 0.19/0.58  cnf(c_0_97, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_96]), c_0_83]), c_0_44])]), c_0_91])).
% 0.19/0.58  cnf(c_0_98, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_97, c_0_36])).
% 0.19/0.58  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_15]), c_0_44])]), ['proof']).
% 0.19/0.58  # SZS output end CNFRefutation
% 0.19/0.58  # Proof object total steps             : 100
% 0.19/0.58  # Proof object clause steps            : 77
% 0.19/0.58  # Proof object formula steps           : 23
% 0.19/0.58  # Proof object conjectures             : 44
% 0.19/0.58  # Proof object clause conjectures      : 41
% 0.19/0.58  # Proof object formula conjectures     : 3
% 0.19/0.58  # Proof object initial clauses used    : 23
% 0.19/0.58  # Proof object initial formulas used   : 11
% 0.19/0.58  # Proof object generating inferences   : 42
% 0.19/0.58  # Proof object simplifying inferences  : 85
% 0.19/0.58  # Training examples: 0 positive, 0 negative
% 0.19/0.58  # Parsed axioms                        : 11
% 0.19/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.58  # Initial clauses                      : 27
% 0.19/0.58  # Removed in clause preprocessing      : 0
% 0.19/0.58  # Initial clauses in saturation        : 27
% 0.19/0.58  # Processed clauses                    : 1269
% 0.19/0.58  # ...of these trivial                  : 2
% 0.19/0.58  # ...subsumed                          : 864
% 0.19/0.58  # ...remaining for further processing  : 403
% 0.19/0.58  # Other redundant clauses eliminated   : 42
% 0.19/0.58  # Clauses deleted for lack of memory   : 0
% 0.19/0.58  # Backward-subsumed                    : 138
% 0.19/0.58  # Backward-rewritten                   : 53
% 0.19/0.58  # Generated clauses                    : 5504
% 0.19/0.58  # ...of the previous two non-trivial   : 5264
% 0.19/0.58  # Contextual simplify-reflections      : 62
% 0.19/0.58  # Paramodulations                      : 5423
% 0.19/0.58  # Factorizations                       : 0
% 0.19/0.58  # Equation resolutions                 : 73
% 0.19/0.58  # Propositional unsat checks           : 0
% 0.19/0.58  #    Propositional check models        : 0
% 0.19/0.58  #    Propositional check unsatisfiable : 0
% 0.19/0.58  #    Propositional clauses             : 0
% 0.19/0.58  #    Propositional clauses after purity: 0
% 0.19/0.58  #    Propositional unsat core size     : 0
% 0.19/0.58  #    Propositional preprocessing time  : 0.000
% 0.19/0.58  #    Propositional encoding time       : 0.000
% 0.19/0.58  #    Propositional solver time         : 0.000
% 0.19/0.58  #    Success case prop preproc time    : 0.000
% 0.19/0.58  #    Success case prop encoding time   : 0.000
% 0.19/0.58  #    Success case prop solver time     : 0.000
% 0.19/0.58  # Current number of processed clauses  : 173
% 0.19/0.58  #    Positive orientable unit clauses  : 11
% 0.19/0.58  #    Positive unorientable unit clauses: 0
% 0.19/0.58  #    Negative unit clauses             : 5
% 0.19/0.58  #    Non-unit-clauses                  : 157
% 0.19/0.58  # Current number of unprocessed clauses: 3933
% 0.19/0.58  # ...number of literals in the above   : 25039
% 0.19/0.58  # Current number of archived formulas  : 0
% 0.19/0.58  # Current number of archived clauses   : 226
% 0.19/0.58  # Clause-clause subsumption calls (NU) : 33330
% 0.19/0.58  # Rec. Clause-clause subsumption calls : 8349
% 0.19/0.58  # Non-unit clause-clause subsumptions  : 941
% 0.19/0.58  # Unit Clause-clause subsumption calls : 61
% 0.19/0.58  # Rewrite failures with RHS unbound    : 0
% 0.19/0.58  # BW rewrite match attempts            : 18
% 0.19/0.58  # BW rewrite match successes           : 8
% 0.19/0.58  # Condensation attempts                : 0
% 0.19/0.58  # Condensation successes               : 0
% 0.19/0.58  # Termbank termtop insertions          : 269272
% 0.19/0.58  
% 0.19/0.58  # -------------------------------------------------
% 0.19/0.58  # User time                : 0.232 s
% 0.19/0.58  # System time              : 0.004 s
% 0.19/0.58  # Total time               : 0.236 s
% 0.19/0.58  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
