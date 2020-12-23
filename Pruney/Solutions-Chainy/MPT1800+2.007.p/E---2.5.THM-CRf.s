%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:23 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  122 (10069 expanded)
%              Number of clauses        :   91 (3396 expanded)
%              Number of leaves         :   15 (2521 expanded)
%              Depth                    :   21
%              Number of atoms          :  442 (63185 expanded)
%              Number of equality atoms :   81 (10657 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

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

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

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

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | m1_subset_1(u1_struct_0(X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X16,X17] :
      ( ( v1_pre_topc(k6_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))) )
      & ( v2_pre_topc(k6_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))) )
      & ( l1_pre_topc(k6_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] :
      ( ( u1_struct_0(k8_tmap_1(X24,X25)) = u1_struct_0(X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | X26 != u1_struct_0(X25)
        | u1_pre_topc(k8_tmap_1(X24,X25)) = k5_tmap_1(X24,X26)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

cnf(c_0_20,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).

cnf(c_0_23,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( u1_pre_topc(k8_tmap_1(X2,X3)) = k5_tmap_1(X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != u1_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X18,X19] :
      ( ( v1_pre_topc(k8_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( v2_pre_topc(k8_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( l1_pre_topc(k8_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_27,plain,(
    ! [X7] :
      ( ~ l1_struct_0(X7)
      | k2_struct_0(X7) = u1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_28,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | l1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_29,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | ~ v1_pre_topc(X6)
      | X6 = g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_30,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_37,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( k5_tmap_1(X1,u1_struct_0(X2)) = u1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_43,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_44,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_45,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_47,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_51,plain,
    ( u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2))) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( k5_tmap_1(esk2_0,u1_struct_0(esk3_0)) = u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_32]),c_0_33])]),c_0_34]),c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_31]),c_0_32]),c_0_33])]),c_0_39]),c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = k2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_45]),c_0_46])).

cnf(c_0_59,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(k2_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_45]),c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))) = k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_61,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) = u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_31]),c_0_52]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_53]),c_0_54]),c_0_55])])).

fof(c_0_63,plain,(
    ! [X8,X9] :
      ( ( ~ v3_pre_topc(X9,X8)
        | r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( ~ r2_hidden(X9,u1_pre_topc(X8))
        | v3_pre_topc(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = k2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

fof(c_0_67,plain,(
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

cnf(c_0_68,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1))) = k5_tmap_1(X1,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk2_0) = k2_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_31]),c_0_66]),c_0_53]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_71,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X1))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_64])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_64])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_64])).

cnf(c_0_74,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_77,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,k2_struct_0(esk2_0))) = k5_tmap_1(esk2_0,k2_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,k2_struct_0(esk2_0))) = k2_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_70]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_79,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk2_0,k2_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_70]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_80,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,k2_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_70]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_81,plain,
    ( k5_tmap_1(X1,u1_struct_0(X1)) = u1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_64])])).

cnf(c_0_82,negated_conjecture,
    ( g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0)
    | v1_tsep_1(esk3_0,esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_45])).

cnf(c_0_83,negated_conjecture,
    ( g1_pre_topc(k2_struct_0(esk2_0),k5_tmap_1(esk2_0,k2_struct_0(esk2_0))) = k6_tmap_1(esk2_0,k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_77]),c_0_78]),c_0_79]),c_0_80])])).

cnf(c_0_84,negated_conjecture,
    ( k5_tmap_1(esk2_0,k2_struct_0(esk2_0)) = u1_pre_topc(esk2_0)
    | ~ v3_pre_topc(k2_struct_0(esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_70]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_85,negated_conjecture,
    ( g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0)
    | v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_46]),c_0_33])])).

cnf(c_0_86,negated_conjecture,
    ( g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k6_tmap_1(esk2_0,k2_struct_0(esk2_0))
    | ~ v3_pre_topc(k2_struct_0(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_87,plain,(
    ! [X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v3_pre_topc(k2_struct_0(X11),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

cnf(c_0_88,negated_conjecture,
    ( k6_tmap_1(esk2_0,k2_struct_0(esk2_0)) = k8_tmap_1(esk2_0,esk3_0)
    | v1_tsep_1(esk3_0,esk2_0)
    | ~ v3_pre_topc(k2_struct_0(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk2_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_70]),c_0_33])])).

cnf(c_0_91,negated_conjecture,
    ( k6_tmap_1(esk2_0,k2_struct_0(esk2_0)) = k8_tmap_1(esk2_0,esk3_0)
    | v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_32]),c_0_33])])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(esk2_0))
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_59]),c_0_33])])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(k2_struct_0(esk2_0)))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_70]),c_0_33])])).

fof(c_0_94,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_tsep_1(X13,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != u1_struct_0(X13)
        | v3_pre_topc(X14,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk1_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v1_tsep_1(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( esk1_2(X12,X13) = u1_struct_0(X13)
        | v1_tsep_1(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ v3_pre_topc(esk1_2(X12,X13),X12)
        | v1_tsep_1(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_95,negated_conjecture,
    ( k5_tmap_1(esk2_0,k2_struct_0(esk2_0)) = u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | v1_tsep_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( k5_tmap_1(esk2_0,u1_struct_0(X1)) = u1_pre_topc(esk2_0)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_92]),c_0_32]),c_0_33]),c_0_70])]),c_0_34]),c_0_93])).

cnf(c_0_97,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = u1_pre_topc(esk2_0)
    | v1_tsep_1(esk3_0,esk2_0)
    | ~ v3_pre_topc(k2_struct_0(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_95])).

cnf(c_0_99,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,esk2_0)
    | ~ m1_pre_topc(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_101,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = u1_pre_topc(esk2_0)
    | ~ v3_pre_topc(u1_struct_0(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_96]),c_0_31])])).

cnf(c_0_102,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_97]),c_0_21])).

cnf(c_0_103,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = u1_pre_topc(esk2_0)
    | v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_89]),c_0_32]),c_0_33])])).

cnf(c_0_104,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk3_0),u1_pre_topc(esk2_0))
    | u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) != u1_pre_topc(esk2_0)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_52]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_106,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0)
    | ~ v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_31])])).

cnf(c_0_107,negated_conjecture,
    ( g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_70])).

cnf(c_0_108,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = u1_pre_topc(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_31]),c_0_33])]),c_0_103])).

cnf(c_0_109,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_104,c_0_21])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk3_0),u1_pre_topc(esk2_0))
    | u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) != u1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_21]),c_0_31]),c_0_33])])).

cnf(c_0_111,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_112,negated_conjecture,
    ( g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0)
    | ~ v1_tsep_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_106,c_0_70])).

cnf(c_0_113,negated_conjecture,
    ( g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk3_0),esk2_0)
    | u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) != u1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_31]),c_0_33])])).

cnf(c_0_115,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk1_2(esk2_0,esk3_0)
    | v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_31]),c_0_33])])).

cnf(c_0_116,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113])])).

cnf(c_0_117,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_108])])).

cnf(c_0_118,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk1_2(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_119,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_120,negated_conjecture,
    ( v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_31]),c_0_33])]),c_0_116]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:11:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.52  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.18/0.52  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.18/0.52  #
% 0.18/0.52  # Preprocessing time       : 0.028 s
% 0.18/0.52  # Presaturation interreduction done
% 0.18/0.52  
% 0.18/0.52  # Proof found!
% 0.18/0.52  # SZS status Theorem
% 0.18/0.52  # SZS output start CNFRefutation
% 0.18/0.52  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.18/0.52  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.18/0.52  fof(t116_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_tmap_1)).
% 0.18/0.52  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.18/0.52  fof(t114_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_tmap_1)).
% 0.18/0.52  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.18/0.52  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.18/0.52  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.52  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.18/0.52  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.18/0.52  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.18/0.52  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.18/0.52  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.18/0.52  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.18/0.52  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.18/0.52  fof(c_0_15, plain, ![X22, X23]:((u1_struct_0(k6_tmap_1(X22,X23))=u1_struct_0(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(u1_pre_topc(k6_tmap_1(X22,X23))=k5_tmap_1(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.18/0.52  fof(c_0_16, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_pre_topc(X28,X27)|m1_subset_1(u1_struct_0(X28),k1_zfmisc_1(u1_struct_0(X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.18/0.52  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t116_tmap_1])).
% 0.18/0.52  fof(c_0_18, plain, ![X16, X17]:(((v1_pre_topc(k6_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))))&(v2_pre_topc(k6_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))))))&(l1_pre_topc(k6_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.18/0.52  fof(c_0_19, plain, ![X24, X25, X26]:((u1_struct_0(k8_tmap_1(X24,X25))=u1_struct_0(X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X24))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(X26!=u1_struct_0(X25)|u1_pre_topc(k8_tmap_1(X24,X25))=k5_tmap_1(X24,X26))|(v2_struct_0(X25)|~m1_pre_topc(X25,X24))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).
% 0.18/0.52  cnf(c_0_20, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.52  cnf(c_0_21, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.52  fof(c_0_22, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0))&((v1_tsep_1(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0))&(m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).
% 0.18/0.52  cnf(c_0_23, plain, (v1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.52  cnf(c_0_24, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.52  cnf(c_0_25, plain, (u1_pre_topc(k8_tmap_1(X2,X3))=k5_tmap_1(X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X1!=u1_struct_0(X3)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.52  fof(c_0_26, plain, ![X18, X19]:(((v1_pre_topc(k8_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))&(v2_pre_topc(k8_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18))))&(l1_pre_topc(k8_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.18/0.52  fof(c_0_27, plain, ![X7]:(~l1_struct_0(X7)|k2_struct_0(X7)=u1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.18/0.52  fof(c_0_28, plain, ![X10]:(~l1_pre_topc(X10)|l1_struct_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.52  fof(c_0_29, plain, ![X6]:(~l1_pre_topc(X6)|(~v1_pre_topc(X6)|X6=g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.18/0.52  cnf(c_0_30, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.52  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.52  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.52  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.52  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.52  cnf(c_0_35, plain, (v2_struct_0(X1)|v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.18/0.52  cnf(c_0_36, plain, (v2_struct_0(X1)|l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.18/0.52  cnf(c_0_37, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.52  cnf(c_0_38, plain, (k5_tmap_1(X1,u1_struct_0(X2))=u1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_21])).
% 0.18/0.52  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.52  cnf(c_0_40, plain, (u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.52  cnf(c_0_41, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.52  cnf(c_0_42, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.52  fof(c_0_43, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.18/0.52  fof(c_0_44, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.18/0.52  cnf(c_0_45, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.52  cnf(c_0_46, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.52  cnf(c_0_47, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.52  cnf(c_0_48, negated_conjecture, (u1_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_49, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_50, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_51, plain, (u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))=k5_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_37, c_0_21])).
% 0.18/0.52  cnf(c_0_52, negated_conjecture, (k5_tmap_1(esk2_0,u1_struct_0(esk3_0))=u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_31]), c_0_32]), c_0_33])]), c_0_34]), c_0_39])).
% 0.18/0.52  cnf(c_0_53, negated_conjecture, (u1_struct_0(k8_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_31]), c_0_32]), c_0_33])]), c_0_39]), c_0_34])).
% 0.18/0.52  cnf(c_0_54, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_55, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_56, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.52  cnf(c_0_57, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.52  cnf(c_0_58, plain, (u1_struct_0(k6_tmap_1(X1,X2))=k2_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_45]), c_0_46])).
% 0.18/0.52  cnf(c_0_59, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(k2_struct_0(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_45]), c_0_46])).
% 0.18/0.52  cnf(c_0_60, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))))=k6_tmap_1(esk2_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])])).
% 0.18/0.52  cnf(c_0_61, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))=u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_31]), c_0_52]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_62, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)))=k8_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_53]), c_0_54]), c_0_55])])).
% 0.18/0.52  fof(c_0_63, plain, ![X8, X9]:((~v3_pre_topc(X9,X8)|r2_hidden(X9,u1_pre_topc(X8))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&(~r2_hidden(X9,u1_pre_topc(X8))|v3_pre_topc(X9,X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.18/0.52  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.52  cnf(c_0_65, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=k2_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.52  cnf(c_0_66, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(esk3_0))=k8_tmap_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.18/0.52  fof(c_0_67, plain, ![X20, X21]:((~r2_hidden(X21,u1_pre_topc(X20))|u1_pre_topc(X20)=k5_tmap_1(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(u1_pre_topc(X20)!=k5_tmap_1(X20,X21)|r2_hidden(X21,u1_pre_topc(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.18/0.52  cnf(c_0_68, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.52  cnf(c_0_69, plain, (u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))=k5_tmap_1(X1,u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_37, c_0_64])).
% 0.18/0.52  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk2_0)=k2_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_31]), c_0_66]), c_0_53]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_71, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X1)))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_64])).
% 0.18/0.52  cnf(c_0_72, plain, (v2_struct_0(X1)|v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_64])).
% 0.18/0.52  cnf(c_0_73, plain, (v2_struct_0(X1)|l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_64])).
% 0.18/0.52  cnf(c_0_74, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.18/0.52  cnf(c_0_75, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v3_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_68, c_0_64])).
% 0.18/0.52  cnf(c_0_76, negated_conjecture, (v1_tsep_1(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.52  cnf(c_0_77, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk2_0,k2_struct_0(esk2_0)))=k5_tmap_1(esk2_0,k2_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_78, negated_conjecture, (u1_struct_0(k6_tmap_1(esk2_0,k2_struct_0(esk2_0)))=k2_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_70]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_79, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk2_0,k2_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_70]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_80, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk2_0,k2_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_70]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_81, plain, (k5_tmap_1(X1,u1_struct_0(X1))=u1_pre_topc(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v3_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_64])])).
% 0.18/0.52  cnf(c_0_82, negated_conjecture, (g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)|v1_tsep_1(esk3_0,esk2_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_76, c_0_45])).
% 0.18/0.52  cnf(c_0_83, negated_conjecture, (g1_pre_topc(k2_struct_0(esk2_0),k5_tmap_1(esk2_0,k2_struct_0(esk2_0)))=k6_tmap_1(esk2_0,k2_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_77]), c_0_78]), c_0_79]), c_0_80])])).
% 0.18/0.52  cnf(c_0_84, negated_conjecture, (k5_tmap_1(esk2_0,k2_struct_0(esk2_0))=u1_pre_topc(esk2_0)|~v3_pre_topc(k2_struct_0(esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_70]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_85, negated_conjecture, (g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)|v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_46]), c_0_33])])).
% 0.18/0.52  cnf(c_0_86, negated_conjecture, (g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(esk2_0))=k6_tmap_1(esk2_0,k2_struct_0(esk2_0))|~v3_pre_topc(k2_struct_0(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.18/0.52  fof(c_0_87, plain, ![X11]:(~v2_pre_topc(X11)|~l1_pre_topc(X11)|v3_pre_topc(k2_struct_0(X11),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.18/0.52  cnf(c_0_88, negated_conjecture, (k6_tmap_1(esk2_0,k2_struct_0(esk2_0))=k8_tmap_1(esk2_0,esk3_0)|v1_tsep_1(esk3_0,esk2_0)|~v3_pre_topc(k2_struct_0(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.18/0.52  cnf(c_0_89, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.18/0.52  cnf(c_0_90, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk2_0))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_70]), c_0_33])])).
% 0.18/0.52  cnf(c_0_91, negated_conjecture, (k6_tmap_1(esk2_0,k2_struct_0(esk2_0))=k8_tmap_1(esk2_0,esk3_0)|v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_32]), c_0_33])])).
% 0.18/0.52  cnf(c_0_92, negated_conjecture, (r2_hidden(u1_struct_0(X1),u1_pre_topc(esk2_0))|~m1_pre_topc(X1,esk2_0)|~v3_pre_topc(u1_struct_0(X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_59]), c_0_33])])).
% 0.18/0.52  cnf(c_0_93, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(k2_struct_0(esk2_0)))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_70]), c_0_33])])).
% 0.18/0.52  fof(c_0_94, plain, ![X12, X13, X14]:((~v1_tsep_1(X13,X12)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(X14!=u1_struct_0(X13)|v3_pre_topc(X14,X12)))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&((m1_subset_1(esk1_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v1_tsep_1(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&((esk1_2(X12,X13)=u1_struct_0(X13)|v1_tsep_1(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&(~v3_pre_topc(esk1_2(X12,X13),X12)|v1_tsep_1(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.18/0.52  cnf(c_0_95, negated_conjecture, (k5_tmap_1(esk2_0,k2_struct_0(esk2_0))=u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))|v1_tsep_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_77, c_0_91])).
% 0.18/0.52  cnf(c_0_96, negated_conjecture, (k5_tmap_1(esk2_0,u1_struct_0(X1))=u1_pre_topc(esk2_0)|~m1_pre_topc(X1,esk2_0)|~v3_pre_topc(u1_struct_0(X1),esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_92]), c_0_32]), c_0_33]), c_0_70])]), c_0_34]), c_0_93])).
% 0.18/0.52  cnf(c_0_97, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.18/0.52  cnf(c_0_98, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))=u1_pre_topc(esk2_0)|v1_tsep_1(esk3_0,esk2_0)|~v3_pre_topc(k2_struct_0(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_84, c_0_95])).
% 0.18/0.52  cnf(c_0_99, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.18/0.52  cnf(c_0_100, negated_conjecture, (~v1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.52  cnf(c_0_101, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))=u1_pre_topc(esk2_0)|~v3_pre_topc(u1_struct_0(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_96]), c_0_31])])).
% 0.18/0.52  cnf(c_0_102, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_97]), c_0_21])).
% 0.18/0.52  cnf(c_0_103, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))=u1_pre_topc(esk2_0)|v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_89]), c_0_32]), c_0_33])])).
% 0.18/0.52  cnf(c_0_104, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.52  cnf(c_0_105, negated_conjecture, (r2_hidden(u1_struct_0(esk3_0),u1_pre_topc(esk2_0))|u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))!=u1_pre_topc(esk2_0)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_52]), c_0_32]), c_0_33])]), c_0_34])).
% 0.18/0.52  cnf(c_0_106, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0)|~v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_31])])).
% 0.18/0.52  cnf(c_0_107, negated_conjecture, (g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)))=k8_tmap_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_62, c_0_70])).
% 0.18/0.52  cnf(c_0_108, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))=u1_pre_topc(esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_31]), c_0_33])]), c_0_103])).
% 0.18/0.52  cnf(c_0_109, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_104, c_0_21])).
% 0.18/0.52  cnf(c_0_110, negated_conjecture, (r2_hidden(u1_struct_0(esk3_0),u1_pre_topc(esk2_0))|u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))!=u1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_21]), c_0_31]), c_0_33])])).
% 0.18/0.52  cnf(c_0_111, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.18/0.52  cnf(c_0_112, negated_conjecture, (g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0)|~v1_tsep_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_106, c_0_70])).
% 0.18/0.52  cnf(c_0_113, negated_conjecture, (g1_pre_topc(k2_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_107, c_0_108])).
% 0.18/0.52  cnf(c_0_114, negated_conjecture, (v3_pre_topc(u1_struct_0(esk3_0),esk2_0)|u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))!=u1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_31]), c_0_33])])).
% 0.18/0.52  cnf(c_0_115, negated_conjecture, (u1_struct_0(esk3_0)=esk1_2(esk2_0,esk3_0)|v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_31]), c_0_33])])).
% 0.18/0.52  cnf(c_0_116, negated_conjecture, (~v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113])])).
% 0.18/0.52  cnf(c_0_117, negated_conjecture, (v3_pre_topc(u1_struct_0(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_108])])).
% 0.18/0.52  cnf(c_0_118, negated_conjecture, (u1_struct_0(esk3_0)=esk1_2(esk2_0,esk3_0)), inference(sr,[status(thm)],[c_0_115, c_0_116])).
% 0.18/0.52  cnf(c_0_119, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk1_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.18/0.52  cnf(c_0_120, negated_conjecture, (v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0)), inference(rw,[status(thm)],[c_0_117, c_0_118])).
% 0.18/0.52  cnf(c_0_121, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_31]), c_0_33])]), c_0_116]), ['proof']).
% 0.18/0.52  # SZS output end CNFRefutation
% 0.18/0.52  # Proof object total steps             : 122
% 0.18/0.52  # Proof object clause steps            : 91
% 0.18/0.52  # Proof object formula steps           : 31
% 0.18/0.52  # Proof object conjectures             : 55
% 0.18/0.52  # Proof object clause conjectures      : 52
% 0.18/0.52  # Proof object formula conjectures     : 3
% 0.18/0.52  # Proof object initial clauses used    : 29
% 0.18/0.52  # Proof object initial formulas used   : 15
% 0.18/0.52  # Proof object generating inferences   : 50
% 0.18/0.52  # Proof object simplifying inferences  : 135
% 0.18/0.52  # Training examples: 0 positive, 0 negative
% 0.18/0.52  # Parsed axioms                        : 15
% 0.18/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.52  # Initial clauses                      : 33
% 0.18/0.52  # Removed in clause preprocessing      : 1
% 0.18/0.52  # Initial clauses in saturation        : 32
% 0.18/0.52  # Processed clauses                    : 1518
% 0.18/0.52  # ...of these trivial                  : 64
% 0.18/0.52  # ...subsumed                          : 650
% 0.18/0.52  # ...remaining for further processing  : 804
% 0.18/0.52  # Other redundant clauses eliminated   : 2
% 0.18/0.52  # Clauses deleted for lack of memory   : 0
% 0.18/0.52  # Backward-subsumed                    : 103
% 0.18/0.52  # Backward-rewritten                   : 353
% 0.18/0.52  # Generated clauses                    : 4731
% 0.18/0.52  # ...of the previous two non-trivial   : 4277
% 0.18/0.52  # Contextual simplify-reflections      : 88
% 0.18/0.52  # Paramodulations                      : 4704
% 0.18/0.52  # Factorizations                       : 0
% 0.18/0.52  # Equation resolutions                 : 2
% 0.18/0.52  # Propositional unsat checks           : 0
% 0.18/0.52  #    Propositional check models        : 0
% 0.18/0.52  #    Propositional check unsatisfiable : 0
% 0.18/0.52  #    Propositional clauses             : 0
% 0.18/0.52  #    Propositional clauses after purity: 0
% 0.18/0.52  #    Propositional unsat core size     : 0
% 0.18/0.52  #    Propositional preprocessing time  : 0.000
% 0.18/0.52  #    Propositional encoding time       : 0.000
% 0.18/0.52  #    Propositional solver time         : 0.000
% 0.18/0.52  #    Success case prop preproc time    : 0.000
% 0.18/0.52  #    Success case prop encoding time   : 0.000
% 0.18/0.52  #    Success case prop solver time     : 0.000
% 0.18/0.52  # Current number of processed clauses  : 290
% 0.18/0.52  #    Positive orientable unit clauses  : 22
% 0.18/0.52  #    Positive unorientable unit clauses: 0
% 0.18/0.52  #    Negative unit clauses             : 3
% 0.18/0.52  #    Non-unit-clauses                  : 265
% 0.18/0.52  # Current number of unprocessed clauses: 2703
% 0.18/0.52  # ...number of literals in the above   : 14022
% 0.18/0.52  # Current number of archived formulas  : 0
% 0.18/0.52  # Current number of archived clauses   : 513
% 0.18/0.52  # Clause-clause subsumption calls (NU) : 43688
% 0.18/0.52  # Rec. Clause-clause subsumption calls : 17885
% 0.18/0.52  # Non-unit clause-clause subsumptions  : 836
% 0.18/0.52  # Unit Clause-clause subsumption calls : 822
% 0.18/0.52  # Rewrite failures with RHS unbound    : 0
% 0.18/0.52  # BW rewrite match attempts            : 32
% 0.18/0.52  # BW rewrite match successes           : 15
% 0.18/0.52  # Condensation attempts                : 0
% 0.18/0.52  # Condensation successes               : 0
% 0.18/0.52  # Termbank termtop insertions          : 121887
% 0.18/0.52  
% 0.18/0.52  # -------------------------------------------------
% 0.18/0.52  # User time                : 0.178 s
% 0.18/0.52  # System time              : 0.006 s
% 0.18/0.52  # Total time               : 0.184 s
% 0.18/0.52  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
