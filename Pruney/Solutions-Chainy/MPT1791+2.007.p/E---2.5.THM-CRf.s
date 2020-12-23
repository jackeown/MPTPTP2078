%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:13 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 (2904 expanded)
%              Number of clauses        :   44 ( 957 expanded)
%              Number of leaves         :   10 ( 712 expanded)
%              Depth                    :   15
%              Number of atoms          :  240 (14309 expanded)
%              Number of equality atoms :   41 (2330 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(dt_m2_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m2_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(t35_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => m2_connsp_2(k2_struct_0(X1),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(t43_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k1_tops_1(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tmap_1])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | ~ m2_connsp_2(X15,X13,X14)
      | m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | m2_connsp_2(k2_struct_0(X16),X16,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_connsp_2])])])])).

fof(c_0_14,plain,(
    ! [X12] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | k1_tops_1(X12,k2_struct_0(X12)) = k2_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_tops_1])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m2_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m2_connsp_2(k2_struct_0(X1),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | v3_pre_topc(k1_tops_1(X10,X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_22,plain,
    ( k1_tops_1(X1,k2_struct_0(X1)) = k2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m2_connsp_2(X1,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( m2_connsp_2(k2_struct_0(esk1_0),esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_17]),c_0_18])]),c_0_20])).

fof(c_0_25,plain,(
    ! [X6,X7] :
      ( ( ~ v3_pre_topc(X7,X6)
        | r2_hidden(X7,u1_pre_topc(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( ~ r2_hidden(X7,u1_pre_topc(X6))
        | v3_pre_topc(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_26,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_struct_0(esk1_0)) = k2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | ~ v1_pre_topc(X4)
      | X4 = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_30,plain,(
    ! [X22,X23] :
      ( ( u1_struct_0(k6_tmap_1(X22,X23)) = u1_struct_0(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( u1_pre_topc(k6_tmap_1(X22,X23)) = k5_tmap_1(X22,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_31,plain,(
    ! [X18,X19] :
      ( ( v1_pre_topc(k6_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) )
      & ( v2_pre_topc(k6_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) )
      & ( l1_pre_topc(k6_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_32,plain,(
    ! [X20,X21] :
      ( ( ~ r2_hidden(X21,u1_pre_topc(X20))
        | u1_pre_topc(X20) = k5_tmap_1(X20,X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( u1_pre_topc(X20) != k5_tmap_1(X20,X21)
        | r2_hidden(X21,u1_pre_topc(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v3_pre_topc(k2_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_17]),c_0_18])]),c_0_28])])).

cnf(c_0_35,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k2_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28]),c_0_18])])).

cnf(c_0_41,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k6_tmap_1(X1,X2))) = k6_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_45,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(esk1_0)
    | ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_16]),c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( u1_pre_topc(esk1_0) = k5_tmap_1(esk1_0,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_17]),c_0_18])]),c_0_20]),c_0_40])])).

cnf(c_0_48,negated_conjecture,
    ( k6_tmap_1(esk1_0,esk2_0) = g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))
    | r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_41]),c_0_16]),c_0_18])])).

cnf(c_0_49,negated_conjecture,
    ( k6_tmap_1(esk1_0,esk2_0) != g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_16]),c_0_18])])).

cnf(c_0_50,plain,
    ( g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) = k6_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = k5_tmap_1(esk1_0,k2_struct_0(esk1_0))
    | ~ r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k6_tmap_1(esk1_0,esk2_0) = g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))
    | r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_47]),c_0_47])).

cnf(c_0_53,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_48]),c_0_17]),c_0_16]),c_0_18])]),c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( k6_tmap_1(esk1_0,esk2_0) != g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_47]),c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( k6_tmap_1(esk1_0,esk2_0) = g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_17]),c_0_16]),c_0_18])]),c_0_20]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0))
    | k5_tmap_1(esk1_0,esk2_0) != u1_pre_topc(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_16]),c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_58,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0))))
    | r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_47]),c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))
    | k5_tmap_1(esk1_0,esk2_0) != k5_tmap_1(esk1_0,k2_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_47]),c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))) != k5_tmap_1(esk1_0,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk1_0,k2_struct_0(esk1_0))) != k5_tmap_1(esk1_0,k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_50]),c_0_17]),c_0_28]),c_0_18])]),c_0_20])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_45]),c_0_17]),c_0_28]),c_0_18])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.19/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.041 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t106_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.19/0.41  fof(dt_m2_connsp_2, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m2_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 0.19/0.41  fof(t35_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>m2_connsp_2(k2_struct_0(X1),X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 0.19/0.41  fof(t43_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>k1_tops_1(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 0.19/0.41  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.19/0.41  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.41  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.19/0.41  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.19/0.41  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.19/0.41  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.19/0.41  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t106_tmap_1])).
% 0.19/0.41  fof(c_0_11, plain, ![X13, X14, X15]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(~m2_connsp_2(X15,X13,X14)|m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).
% 0.19/0.41  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.41  fof(c_0_13, plain, ![X16, X17]:(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|m2_connsp_2(k2_struct_0(X16),X16,X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_connsp_2])])])])).
% 0.19/0.41  fof(c_0_14, plain, ![X12]:(~v2_pre_topc(X12)|~l1_pre_topc(X12)|k1_tops_1(X12,k2_struct_0(X12))=k2_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_tops_1])])).
% 0.19/0.41  cnf(c_0_15, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m2_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_19, plain, (v2_struct_0(X1)|m2_connsp_2(k2_struct_0(X1),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  fof(c_0_21, plain, ![X10, X11]:(~v2_pre_topc(X10)|~l1_pre_topc(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|v3_pre_topc(k1_tops_1(X10,X11),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.19/0.41  cnf(c_0_22, plain, (k1_tops_1(X1,k2_struct_0(X1))=k2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m2_connsp_2(X1,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.19/0.41  cnf(c_0_24, negated_conjecture, (m2_connsp_2(k2_struct_0(esk1_0),esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_16]), c_0_17]), c_0_18])]), c_0_20])).
% 0.19/0.41  fof(c_0_25, plain, ![X6, X7]:((~v3_pre_topc(X7,X6)|r2_hidden(X7,u1_pre_topc(X6))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|~l1_pre_topc(X6))&(~r2_hidden(X7,u1_pre_topc(X6))|v3_pre_topc(X7,X6)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|~l1_pre_topc(X6))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.41  cnf(c_0_26, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (k1_tops_1(esk1_0,k2_struct_0(esk1_0))=k2_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_18])])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.41  fof(c_0_29, plain, ![X4]:(~l1_pre_topc(X4)|(~v1_pre_topc(X4)|X4=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.19/0.41  fof(c_0_30, plain, ![X22, X23]:((u1_struct_0(k6_tmap_1(X22,X23))=u1_struct_0(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(u1_pre_topc(k6_tmap_1(X22,X23))=k5_tmap_1(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.19/0.41  fof(c_0_31, plain, ![X18, X19]:(((v1_pre_topc(k6_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))))&(v2_pre_topc(k6_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))))))&(l1_pre_topc(k6_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.19/0.41  fof(c_0_32, plain, ![X20, X21]:((~r2_hidden(X21,u1_pre_topc(X20))|u1_pre_topc(X20)=k5_tmap_1(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(u1_pre_topc(X20)!=k5_tmap_1(X20,X21)|r2_hidden(X21,u1_pre_topc(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.19/0.41  cnf(c_0_33, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (v3_pre_topc(k2_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_17]), c_0_18])]), c_0_28])])).
% 0.19/0.41  cnf(c_0_35, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_36, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_37, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_38, plain, (v1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_39, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (r2_hidden(k2_struct_0(esk1_0),u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28]), c_0_18])])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_43, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_44, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k6_tmap_1(X1,X2)))=k6_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.41  cnf(c_0_45, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(esk1_0)|~r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_16]), c_0_17]), c_0_18])]), c_0_20])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (u1_pre_topc(esk1_0)=k5_tmap_1(esk1_0,k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_28]), c_0_17]), c_0_18])]), c_0_20]), c_0_40])])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (k6_tmap_1(esk1_0,esk2_0)=g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))|r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_41]), c_0_16]), c_0_18])])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (k6_tmap_1(esk1_0,esk2_0)!=g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))|~r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_16]), c_0_18])])).
% 0.19/0.41  cnf(c_0_50, plain, (g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))=k6_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=k5_tmap_1(esk1_0,k2_struct_0(esk1_0))|~r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (k6_tmap_1(esk1_0,esk2_0)=g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))|r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_47]), c_0_47])).
% 0.19/0.41  cnf(c_0_53, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_48]), c_0_17]), c_0_16]), c_0_18])]), c_0_20])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (k6_tmap_1(esk1_0,esk2_0)!=g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))|~r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_47]), c_0_47])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (k6_tmap_1(esk1_0,esk2_0)=g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_17]), c_0_16]), c_0_18])]), c_0_20]), c_0_52])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))|k5_tmap_1(esk1_0,esk2_0)!=u1_pre_topc(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_16]), c_0_17]), c_0_18])]), c_0_20])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0))))|r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_47]), c_0_47])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (~r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (r2_hidden(esk2_0,k5_tmap_1(esk1_0,k2_struct_0(esk1_0)))|k5_tmap_1(esk1_0,esk2_0)!=k5_tmap_1(esk1_0,k2_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_47]), c_0_47])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0))))), inference(sr,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,k2_struct_0(esk1_0))))!=k5_tmap_1(esk1_0,k2_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_59])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk1_0,k2_struct_0(esk1_0)))!=k5_tmap_1(esk1_0,k2_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_50]), c_0_17]), c_0_28]), c_0_18])]), c_0_20])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_45]), c_0_17]), c_0_28]), c_0_18])]), c_0_20]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 65
% 0.19/0.41  # Proof object clause steps            : 44
% 0.19/0.41  # Proof object formula steps           : 21
% 0.19/0.41  # Proof object conjectures             : 32
% 0.19/0.41  # Proof object clause conjectures      : 29
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 19
% 0.19/0.41  # Proof object initial formulas used   : 10
% 0.19/0.41  # Proof object generating inferences   : 17
% 0.19/0.41  # Proof object simplifying inferences  : 75
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 13
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 23
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 23
% 0.19/0.41  # Processed clauses                    : 173
% 0.19/0.41  # ...of these trivial                  : 5
% 0.19/0.41  # ...subsumed                          : 27
% 0.19/0.41  # ...remaining for further processing  : 141
% 0.19/0.41  # Other redundant clauses eliminated   : 0
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 2
% 0.19/0.41  # Backward-rewritten                   : 19
% 0.19/0.41  # Generated clauses                    : 307
% 0.19/0.41  # ...of the previous two non-trivial   : 266
% 0.19/0.41  # Contextual simplify-reflections      : 15
% 0.19/0.41  # Paramodulations                      : 302
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 0
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
% 0.19/0.41  # Current number of processed clauses  : 92
% 0.19/0.41  #    Positive orientable unit clauses  : 31
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 6
% 0.19/0.41  #    Non-unit-clauses                  : 55
% 0.19/0.41  # Current number of unprocessed clauses: 135
% 0.19/0.41  # ...number of literals in the above   : 504
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 49
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 732
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 307
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 42
% 0.19/0.41  # Unit Clause-clause subsumption calls : 117
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 8
% 0.19/0.41  # BW rewrite match successes           : 4
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 9325
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.057 s
% 0.19/0.41  # System time              : 0.009 s
% 0.19/0.41  # Total time               : 0.065 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
