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
% DateTime   : Thu Dec  3 11:18:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 (1293 expanded)
%              Number of clauses        :   54 ( 438 expanded)
%              Number of leaves         :    9 ( 319 expanded)
%              Depth                    :   12
%              Number of atoms          :  323 (8482 expanded)
%              Number of equality atoms :   57 (1372 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( ( v1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X1) )
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

fof(d1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tsep_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t106_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(t114_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
            & ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

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

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( ( v1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X1) )
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_tmap_1])).

fof(c_0_10,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_tsep_1(X6,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | X7 != u1_struct_0(X6)
        | v3_pre_topc(X7,X5)
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_2(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))
        | v1_tsep_1(X6,X5)
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X5) )
      & ( esk1_2(X5,X6) = u1_struct_0(X6)
        | v1_tsep_1(X6,X5)
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ v3_pre_topc(esk1_2(X5,X6),X5)
        | v1_tsep_1(X6,X5)
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | m1_subset_1(u1_struct_0(X21),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ( ~ v1_tsep_1(esk3_0,esk2_0)
      | ~ m1_pre_topc(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0) )
    & ( v1_tsep_1(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) )
    & ( m1_pre_topc(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

cnf(c_0_13,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ( ~ v3_pre_topc(X16,X15)
        | g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)) = k6_tmap_1(X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)) != k6_tmap_1(X15,X16)
        | v3_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X17,X18,X19] :
      ( ( u1_struct_0(k8_tmap_1(X17,X18)) = u1_struct_0(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | X19 != u1_struct_0(X18)
        | u1_pre_topc(k8_tmap_1(X17,X18)) = k5_tmap_1(X17,X19)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

cnf(c_0_19,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X11,X12] :
      ( ( v1_pre_topc(k8_tmap_1(X11,X12))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_pre_topc(X12,X11) )
      & ( v2_pre_topc(k8_tmap_1(X11,X12))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_pre_topc(X12,X11) )
      & ( l1_pre_topc(k8_tmap_1(X11,X12))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_pre_topc(X12,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_22,plain,(
    ! [X13,X14] :
      ( ( u1_struct_0(k6_tmap_1(X13,X14)) = u1_struct_0(X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( u1_pre_topc(k6_tmap_1(X13,X14)) = k5_tmap_1(X13,X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

cnf(c_0_23,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k6_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_16]),c_0_17])])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | v3_pre_topc(u1_struct_0(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_16]),c_0_17])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_30,plain,(
    ! [X9,X10] :
      ( ( v1_pre_topc(k6_tmap_1(X9,X10))
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))) )
      & ( v2_pre_topc(k6_tmap_1(X9,X10))
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))) )
      & ( l1_pre_topc(k6_tmap_1(X9,X10))
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_31,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | ~ v1_pre_topc(X4)
      | X4 = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_34,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ v3_pre_topc(u1_struct_0(esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_17])]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = u1_struct_0(esk2_0)
    | v3_pre_topc(u1_struct_0(esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_25]),c_0_16]),c_0_17])]),c_0_29]),c_0_26])).

cnf(c_0_37,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk3_0),esk2_0)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_25]),c_0_16]),c_0_17])]),c_0_26])).

cnf(c_0_39,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk3_0),esk2_0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_25]),c_0_16]),c_0_17])]),c_0_26])).

cnf(c_0_41,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
    ( u1_pre_topc(k8_tmap_1(X2,X3)) = k5_tmap_1(X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != u1_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,X1)) = u1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_17])]),c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_17])]),c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_24]),c_0_25]),c_0_17])]),c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_40])).

cnf(c_0_50,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(X1,X2)),k5_tmap_1(X1,X2)) = k6_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_37]),c_0_39])).

cnf(c_0_51,plain,
    ( u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_24])])).

cnf(c_0_53,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_24])])).

cnf(c_0_54,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,esk2_0)
    | ~ m1_pre_topc(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_58,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,X1)) = k6_tmap_1(esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_44]),c_0_25]),c_0_17])]),c_0_26])).

cnf(c_0_60,negated_conjecture,
    ( k5_tmap_1(esk2_0,u1_struct_0(esk3_0)) = u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v3_pre_topc(u1_struct_0(esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_25]),c_0_16]),c_0_17])]),c_0_26]),c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_52]),c_0_53])]),c_0_54])])).

cnf(c_0_62,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_16])])).

cnf(c_0_63,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk3_0),esk2_0)
    | k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_24]),c_0_25]),c_0_17])]),c_0_26])).

cnf(c_0_65,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_24])]),c_0_35])).

cnf(c_0_66,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k8_tmap_1(X1,X2))) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_27]),c_0_31]),c_0_32])).

cnf(c_0_67,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ v3_pre_topc(u1_struct_0(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_16]),c_0_17])])).

cnf(c_0_68,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_69,plain,
    ( g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,u1_struct_0(X2))) = k8_tmap_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( k5_tmap_1(esk2_0,u1_struct_0(esk3_0)) = u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_65]),c_0_25]),c_0_24]),c_0_17])]),c_0_26])).

cnf(c_0_71,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk3_0) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_61]),c_0_25]),c_0_16]),c_0_17])]),c_0_71]),c_0_29]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:31:36 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t116_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_tmap_1)).
% 0.20/0.39  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.20/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.39  fof(t106_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.20/0.39  fof(t114_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_tmap_1)).
% 0.20/0.39  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.20/0.39  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.20/0.39  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.20/0.39  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.20/0.39  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t116_tmap_1])).
% 0.20/0.39  fof(c_0_10, plain, ![X5, X6, X7]:((~v1_tsep_1(X6,X5)|(~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))|(X7!=u1_struct_0(X6)|v3_pre_topc(X7,X5)))|~m1_pre_topc(X6,X5)|~l1_pre_topc(X5))&((m1_subset_1(esk1_2(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))|v1_tsep_1(X6,X5)|~m1_pre_topc(X6,X5)|~l1_pre_topc(X5))&((esk1_2(X5,X6)=u1_struct_0(X6)|v1_tsep_1(X6,X5)|~m1_pre_topc(X6,X5)|~l1_pre_topc(X5))&(~v3_pre_topc(esk1_2(X5,X6),X5)|v1_tsep_1(X6,X5)|~m1_pre_topc(X6,X5)|~l1_pre_topc(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.20/0.39  fof(c_0_11, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|m1_subset_1(u1_struct_0(X21),k1_zfmisc_1(u1_struct_0(X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.39  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0))&((v1_tsep_1(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0))&(m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.20/0.39  cnf(c_0_13, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_14, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  fof(c_0_15, plain, ![X15, X16]:((~v3_pre_topc(X16,X15)|g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))=k6_tmap_1(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))!=k6_tmap_1(X15,X16)|v3_pre_topc(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).
% 0.20/0.39  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  fof(c_0_18, plain, ![X17, X18, X19]:((u1_struct_0(k8_tmap_1(X17,X18))=u1_struct_0(X17)|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(X19!=u1_struct_0(X18)|u1_pre_topc(k8_tmap_1(X17,X18))=k5_tmap_1(X17,X19))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).
% 0.20/0.39  cnf(c_0_19, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_14])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (v1_tsep_1(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  fof(c_0_21, plain, ![X11, X12]:(((v1_pre_topc(k8_tmap_1(X11,X12))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|~m1_pre_topc(X12,X11)))&(v2_pre_topc(k8_tmap_1(X11,X12))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|~m1_pre_topc(X12,X11))))&(l1_pre_topc(k8_tmap_1(X11,X12))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|~m1_pre_topc(X12,X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.20/0.39  fof(c_0_22, plain, ![X13, X14]:((u1_struct_0(k6_tmap_1(X13,X14))=u1_struct_0(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(u1_pre_topc(k6_tmap_1(X13,X14))=k5_tmap_1(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.20/0.39  cnf(c_0_23, plain, (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=k6_tmap_1(X2,X1)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_16]), c_0_17])])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_27, plain, (u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|v3_pre_topc(u1_struct_0(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_16]), c_0_17])])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  fof(c_0_30, plain, ![X9, X10]:(((v1_pre_topc(k6_tmap_1(X9,X10))|(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))))&(v2_pre_topc(k6_tmap_1(X9,X10))|(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))))))&(l1_pre_topc(k6_tmap_1(X9,X10))|(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_31, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_32, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  fof(c_0_33, plain, ![X4]:(~l1_pre_topc(X4)|(~v1_pre_topc(X4)|X4=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.20/0.39  cnf(c_0_34, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~v3_pre_topc(u1_struct_0(esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_17])]), c_0_26])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=u1_struct_0(esk2_0)|v3_pre_topc(u1_struct_0(esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_25]), c_0_16]), c_0_17])]), c_0_29]), c_0_26])).
% 0.20/0.39  cnf(c_0_37, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (v3_pre_topc(u1_struct_0(esk3_0),esk2_0)|l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_25]), c_0_16]), c_0_17])]), c_0_26])).
% 0.20/0.39  cnf(c_0_39, plain, (v1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (v3_pre_topc(u1_struct_0(esk3_0),esk2_0)|v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_25]), c_0_16]), c_0_17])]), c_0_26])).
% 0.20/0.39  cnf(c_0_41, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  cnf(c_0_42, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_43, plain, (u1_pre_topc(k8_tmap_1(X2,X3))=k5_tmap_1(X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X1!=u1_struct_0(X3)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (u1_struct_0(k6_tmap_1(esk2_0,X1))=u1_struct_0(esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_17])]), c_0_26])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=u1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_25]), c_0_17])]), c_0_26])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_35, c_0_38])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_24]), c_0_25]), c_0_17])]), c_0_26])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_35, c_0_40])).
% 0.20/0.39  cnf(c_0_50, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1(X1,X2)),k5_tmap_1(X1,X2))=k6_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_37]), c_0_39])).
% 0.20/0.39  cnf(c_0_51, plain, (u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]), c_0_14])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_24])])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_24])])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (~v1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_56, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk1_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_57, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_58, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=k6_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,X1))=k6_tmap_1(esk2_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_44]), c_0_25]), c_0_17])]), c_0_26])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (k5_tmap_1(esk2_0,u1_struct_0(esk3_0))=u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|v3_pre_topc(u1_struct_0(esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_28]), c_0_25]), c_0_16]), c_0_17])]), c_0_26]), c_0_29])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_52]), c_0_53])]), c_0_54])])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)!=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_16])])).
% 0.20/0.39  cnf(c_0_63, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (v3_pre_topc(u1_struct_0(esk3_0),esk2_0)|k6_tmap_1(esk2_0,u1_struct_0(esk3_0))!=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_24]), c_0_25]), c_0_17])]), c_0_26])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_24])]), c_0_35])).
% 0.20/0.39  cnf(c_0_66, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k8_tmap_1(X1,X2)))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_27]), c_0_31]), c_0_32])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)!=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~v3_pre_topc(u1_struct_0(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_16]), c_0_17])])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (v3_pre_topc(u1_struct_0(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65])])).
% 0.20/0.39  cnf(c_0_69, plain, (g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,u1_struct_0(X2)))=k8_tmap_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_66, c_0_51])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (k5_tmap_1(esk2_0,u1_struct_0(esk3_0))=u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_65]), c_0_25]), c_0_24]), c_0_17])]), c_0_26])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (k8_tmap_1(esk2_0,esk3_0)!=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_61]), c_0_25]), c_0_16]), c_0_17])]), c_0_71]), c_0_29]), c_0_26]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 73
% 0.20/0.39  # Proof object clause steps            : 54
% 0.20/0.39  # Proof object formula steps           : 19
% 0.20/0.39  # Proof object conjectures             : 36
% 0.20/0.39  # Proof object clause conjectures      : 33
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 22
% 0.20/0.39  # Proof object initial formulas used   : 9
% 0.20/0.39  # Proof object generating inferences   : 27
% 0.20/0.39  # Proof object simplifying inferences  : 91
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 9
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 26
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 26
% 0.20/0.39  # Processed clauses                    : 123
% 0.20/0.39  # ...of these trivial                  : 1
% 0.20/0.39  # ...subsumed                          : 10
% 0.20/0.39  # ...remaining for further processing  : 112
% 0.20/0.39  # Other redundant clauses eliminated   : 2
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 22
% 0.20/0.39  # Generated clauses                    : 191
% 0.20/0.39  # ...of the previous two non-trivial   : 163
% 0.20/0.39  # Contextual simplify-reflections      : 12
% 0.20/0.39  # Paramodulations                      : 188
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 2
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 62
% 0.20/0.39  #    Positive orientable unit clauses  : 13
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 46
% 0.20/0.39  # Current number of unprocessed clauses: 82
% 0.20/0.39  # ...number of literals in the above   : 562
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 48
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 638
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 103
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 22
% 0.20/0.39  # Unit Clause-clause subsumption calls : 49
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 8
% 0.20/0.39  # BW rewrite match successes           : 8
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 8461
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.039 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.043 s
% 0.20/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
