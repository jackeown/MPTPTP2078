%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:20 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  109 (3198 expanded)
%              Number of clauses        :   82 (1005 expanded)
%              Number of leaves         :   13 ( 792 expanded)
%              Depth                    :   16
%              Number of atoms          :  667 (26933 expanded)
%              Number of equality atoms :   90 ( 717 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   68 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ( v1_funct_1(k7_tmap_1(X1,X2))
              & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
              & v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
              & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t52_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_struct_0(X2) = k1_xboole_0
                 => k2_struct_0(X1) = k1_xboole_0 )
               => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2)) = k2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(t55_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_struct_0(X2) = k1_xboole_0
                 => k2_struct_0(X1) = k1_xboole_0 )
               => ( v5_pre_topc(X3,X1,X2)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( v3_pre_topc(X4,X2)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(t171_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(t105_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
             => ( X3 = X2
               => v3_pre_topc(X3,k6_tmap_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t62_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(t106_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> ( v1_funct_1(k7_tmap_1(X1,X2))
                & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
                & v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
                & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t113_tmap_1])).

fof(c_0_14,plain,(
    ! [X31,X32] :
      ( ( u1_struct_0(k6_tmap_1(X31,X32)) = u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( u1_pre_topc(k6_tmap_1(X31,X32)) = k5_tmap_1(X31,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | ~ v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
      | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
      | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
      | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) )
    & ( v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))
      | v3_pre_topc(esk3_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k8_relset_1(X5,X6,X7,X8) = k10_relat_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_17,plain,(
    ! [X17,X18,X19] :
      ( ( k2_struct_0(X18) = k1_xboole_0
        | k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,k2_struct_0(X18)) = k2_struct_0(X17)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X17) )
      & ( k2_struct_0(X17) != k1_xboole_0
        | k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,k2_struct_0(X18)) = k2_struct_0(X17)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_tops_2])])])])).

fof(c_0_18,plain,(
    ! [X29,X30] :
      ( ( v1_funct_1(k7_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( v1_funct_2(k7_tmap_1(X29,X30),u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X30)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( m1_subset_1(k7_tmap_1(X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X30)))))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_19,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2)) = k2_struct_0(X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_28,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X27,X28] :
      ( ( v1_pre_topc(k6_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( v2_pre_topc(k6_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( l1_pre_topc(k6_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_31,plain,
    ( k2_struct_0(X1) = k10_relat_1(X2,k2_struct_0(X3))
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_1(X2)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21]),c_0_22]),c_0_20])]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_21]),c_0_22]),c_0_20])]),c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_35,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ v5_pre_topc(X22,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v3_pre_topc(X23,X21)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22,X23),X20)
        | k2_struct_0(X21) = k1_xboole_0
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk1_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X21)))
        | v5_pre_topc(X22,X20,X21)
        | k2_struct_0(X21) = k1_xboole_0
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( v3_pre_topc(esk1_3(X20,X21,X22),X21)
        | v5_pre_topc(X22,X20,X21)
        | k2_struct_0(X21) = k1_xboole_0
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22,esk1_3(X20,X21,X22)),X20)
        | v5_pre_topc(X22,X20,X21)
        | k2_struct_0(X21) = k1_xboole_0
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( ~ v5_pre_topc(X22,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v3_pre_topc(X23,X21)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22,X23),X20)
        | k2_struct_0(X20) != k1_xboole_0
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk1_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X21)))
        | v5_pre_topc(X22,X20,X21)
        | k2_struct_0(X20) != k1_xboole_0
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( v3_pre_topc(esk1_3(X20,X21,X22),X21)
        | v5_pre_topc(X22,X20,X21)
        | k2_struct_0(X20) != k1_xboole_0
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22,esk1_3(X20,X21,X22)),X20)
        | v5_pre_topc(X22,X20,X21)
        | k2_struct_0(X20) != k1_xboole_0
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

cnf(c_0_36,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | k7_tmap_1(X25,X26) = k6_partfun1(u1_struct_0(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

cnf(c_0_38,plain,
    ( k2_struct_0(X1) = k1_xboole_0
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k2_struct_0(X1)) = k2_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,plain,
    ( k8_relset_1(X1,X2,X3,X4) = k8_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(k7_tmap_1(esk2_0,esk3_0),k2_struct_0(esk2_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_41,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | k2_struct_0(X3) = k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_43,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k8_relset_1(X9,X9,k6_partfun1(X9),X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X33,X34))))
      | X35 != X34
      | v3_pre_topc(X35,k6_tmap_1(X33,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).

cnf(c_0_46,plain,
    ( k8_relset_1(X1,X2,X3,k2_struct_0(X4)) = k2_struct_0(X5)
    | k2_struct_0(X4) = k1_xboole_0
    | ~ v1_funct_2(X3,u1_struct_0(X5),u1_struct_0(X4))
    | ~ v1_funct_1(X3)
    | ~ l1_struct_0(X5)
    | ~ l1_struct_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k8_relset_1(X1,X2,k7_tmap_1(esk2_0,esk3_0),k2_struct_0(esk2_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)
    | ~ v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_27]),c_0_42])])).

cnf(c_0_49,plain,
    ( k8_relset_1(X2,X2,k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X3,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | X3 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) != k1_xboole_0
    | ~ v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( k8_relset_1(X1,X2,k7_tmap_1(esk2_0,esk3_0),k2_struct_0(esk2_0)) = k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_33]),c_0_34])]),c_0_47])).

fof(c_0_54,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_55,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_50]),c_0_33]),c_0_50]),c_0_34]),c_0_22]),c_0_50]),c_0_32])])).

cnf(c_0_56,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X2,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) != k1_xboole_0
    | ~ l1_struct_0(k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_33]),c_0_34]),c_0_32])])).

cnf(c_0_59,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(esk3_0,esk2_0)
    | v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(esk3_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_27]),c_0_21]),c_0_22]),c_0_20])]),c_0_23])).

cnf(c_0_62,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_63,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_64,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X4,X3)
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_42])])).

cnf(c_0_66,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_20])])).

cnf(c_0_67,plain,
    ( v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_68,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(X1)),X1,X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v3_pre_topc(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),X1)
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(X1))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ m1_subset_1(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_49])).

cnf(c_0_69,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_70,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(esk1_3(X1,k6_tmap_1(esk2_0,esk3_0),X2),k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_27]),c_0_42])])).

fof(c_0_71,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ v5_pre_topc(X15,X13,X14)
        | v5_pre_topc(X16,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),X14)
        | X15 != X16
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(X14))))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ v5_pre_topc(X16,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),X14)
        | v5_pre_topc(X15,X13,X14)
        | X15 != X16
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(X14))))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

fof(c_0_72,plain,(
    ! [X36,X37] :
      ( ( ~ v3_pre_topc(X37,X36)
        | g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36)) = k6_tmap_1(X36,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36)) != k6_tmap_1(X36,X37)
        | v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).

cnf(c_0_73,negated_conjecture,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_42])])).

cnf(c_0_74,negated_conjecture,
    ( k2_struct_0(esk2_0) = k1_xboole_0
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_76,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(X1)),X1,X1)
    | ~ v3_pre_topc(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),X1)
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(X1))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ m1_subset_1(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_49]),c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( k7_tmap_1(esk2_0,X1) = k7_tmap_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_50]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_78,negated_conjecture,
    ( v3_pre_topc(esk1_3(X1,k6_tmap_1(esk2_0,esk3_0),X2),k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_27]),c_0_42])])).

cnf(c_0_79,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_27]),c_0_42])])).

cnf(c_0_80,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k6_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_49]),c_0_50]),c_0_50]),c_0_33]),c_0_50]),c_0_34]),c_0_22]),c_0_50]),c_0_32])])).

cnf(c_0_83,negated_conjecture,
    ( k2_struct_0(esk2_0) = k1_xboole_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_59]),c_0_22])])).

cnf(c_0_84,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_85,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_27]),c_0_42])])).

cnf(c_0_86,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_27]),c_0_50]),c_0_50]),c_0_50]),c_0_33]),c_0_50]),c_0_34]),c_0_42]),c_0_50]),c_0_32]),c_0_50])])).

cnf(c_0_87,negated_conjecture,
    ( k7_tmap_1(esk2_0,X1) = k7_tmap_1(esk2_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_27]),c_0_42])]),c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_90,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k6_tmap_1(esk2_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_92,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_56])).

cnf(c_0_93,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_27]),c_0_42])])).

cnf(c_0_94,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_27]),c_0_42])])).

cnf(c_0_95,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,X1),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,X1)),k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,X1)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_20])])).

cnf(c_0_96,negated_conjecture,
    ( v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_97,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_34])]),c_0_27]),c_0_33]),c_0_27])])).

cnf(c_0_98,negated_conjecture,
    ( v5_pre_topc(X1,esk2_0,X2)
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),X2)
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_27]),c_0_21]),c_0_22]),c_0_27])])).

cnf(c_0_99,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_92]),c_0_61]),c_0_20])])).

cnf(c_0_100,negated_conjecture,
    ( v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_27]),c_0_42])]),c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_20])])).

cnf(c_0_102,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_103,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_32])])).

cnf(c_0_104,negated_conjecture,
    ( v5_pre_topc(X1,esk2_0,X2)
    | ~ v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),X2)
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99])])).

cnf(c_0_105,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_32]),c_0_33]),c_0_34])]),c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_107,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_99])])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_27]),c_0_33]),c_0_34]),c_0_106]),c_0_42]),c_0_27]),c_0_32])]),c_0_107]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.91/1.13  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.91/1.13  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.91/1.13  #
% 0.91/1.13  # Preprocessing time       : 0.038 s
% 0.91/1.13  
% 0.91/1.13  # Proof found!
% 0.91/1.13  # SZS status Theorem
% 0.91/1.13  # SZS output start CNFRefutation
% 0.91/1.13  fof(t113_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.91/1.13  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.91/1.13  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.91/1.13  fof(t52_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2))=k2_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tops_2)).
% 0.91/1.13  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.91/1.13  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.91/1.13  fof(t55_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X4,X2)=>v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_2)).
% 0.91/1.13  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.91/1.13  fof(t171_funct_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 0.91/1.13  fof(t105_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))=>(X3=X2=>v3_pre_topc(X3,k6_tmap_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tmap_1)).
% 0.91/1.13  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.91/1.13  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.91/1.13  fof(t106_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.91/1.13  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t113_tmap_1])).
% 0.91/1.13  fof(c_0_14, plain, ![X31, X32]:((u1_struct_0(k6_tmap_1(X31,X32))=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(u1_pre_topc(k6_tmap_1(X31,X32))=k5_tmap_1(X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.91/1.13  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|(~v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))))&((((v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0))&(v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|v3_pre_topc(esk3_0,esk2_0)))&(v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)))&(m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))|v3_pre_topc(esk3_0,esk2_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).
% 0.91/1.13  fof(c_0_16, plain, ![X5, X6, X7, X8]:(~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|k8_relset_1(X5,X6,X7,X8)=k10_relat_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.91/1.13  fof(c_0_17, plain, ![X17, X18, X19]:((k2_struct_0(X18)=k1_xboole_0|k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,k2_struct_0(X18))=k2_struct_0(X17)|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|~l1_struct_0(X18)|~l1_struct_0(X17))&(k2_struct_0(X17)!=k1_xboole_0|k8_relset_1(u1_struct_0(X17),u1_struct_0(X18),X19,k2_struct_0(X18))=k2_struct_0(X17)|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|~l1_struct_0(X18)|~l1_struct_0(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_tops_2])])])])).
% 0.91/1.13  fof(c_0_18, plain, ![X29, X30]:(((v1_funct_1(k7_tmap_1(X29,X30))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))))&(v1_funct_2(k7_tmap_1(X29,X30),u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X30)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))))))&(m1_subset_1(k7_tmap_1(X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X30)))))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.91/1.13  cnf(c_0_19, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.91/1.13  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.91/1.13  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.91/1.13  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.91/1.13  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.91/1.13  cnf(c_0_24, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.91/1.13  cnf(c_0_25, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2))=k2_struct_0(X1)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.91/1.13  cnf(c_0_26, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.91/1.13  cnf(c_0_27, negated_conjecture, (u1_struct_0(k6_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.91/1.13  cnf(c_0_28, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.91/1.13  cnf(c_0_29, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.91/1.13  fof(c_0_30, plain, ![X27, X28]:(((v1_pre_topc(k6_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))&(v2_pre_topc(k6_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))))))&(l1_pre_topc(k6_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.91/1.13  cnf(c_0_31, plain, (k2_struct_0(X1)=k10_relat_1(X2,k2_struct_0(X3))|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))|~v1_funct_1(X2)|~l1_struct_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.91/1.13  cnf(c_0_32, negated_conjecture, (m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_21]), c_0_22]), c_0_20])]), c_0_23])).
% 0.91/1.13  cnf(c_0_33, negated_conjecture, (v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_21]), c_0_22]), c_0_20])]), c_0_23])).
% 0.91/1.13  cnf(c_0_34, negated_conjecture, (v1_funct_1(k7_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.91/1.13  fof(c_0_35, plain, ![X20, X21, X22, X23]:(((~v5_pre_topc(X22,X20,X21)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~v3_pre_topc(X23,X21)|v3_pre_topc(k8_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22,X23),X20)))|k2_struct_0(X21)=k1_xboole_0|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|~l1_pre_topc(X21)|~l1_pre_topc(X20))&((m1_subset_1(esk1_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X21)))|v5_pre_topc(X22,X20,X21)|k2_struct_0(X21)=k1_xboole_0|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|~l1_pre_topc(X21)|~l1_pre_topc(X20))&((v3_pre_topc(esk1_3(X20,X21,X22),X21)|v5_pre_topc(X22,X20,X21)|k2_struct_0(X21)=k1_xboole_0|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|~l1_pre_topc(X21)|~l1_pre_topc(X20))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22,esk1_3(X20,X21,X22)),X20)|v5_pre_topc(X22,X20,X21)|k2_struct_0(X21)=k1_xboole_0|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|~l1_pre_topc(X21)|~l1_pre_topc(X20)))))&((~v5_pre_topc(X22,X20,X21)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~v3_pre_topc(X23,X21)|v3_pre_topc(k8_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22,X23),X20)))|k2_struct_0(X20)!=k1_xboole_0|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|~l1_pre_topc(X21)|~l1_pre_topc(X20))&((m1_subset_1(esk1_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X21)))|v5_pre_topc(X22,X20,X21)|k2_struct_0(X20)!=k1_xboole_0|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|~l1_pre_topc(X21)|~l1_pre_topc(X20))&((v3_pre_topc(esk1_3(X20,X21,X22),X21)|v5_pre_topc(X22,X20,X21)|k2_struct_0(X20)!=k1_xboole_0|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|~l1_pre_topc(X21)|~l1_pre_topc(X20))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22,esk1_3(X20,X21,X22)),X20)|v5_pre_topc(X22,X20,X21)|k2_struct_0(X20)!=k1_xboole_0|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|~l1_pre_topc(X21)|~l1_pre_topc(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).
% 0.91/1.13  cnf(c_0_36, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.91/1.13  fof(c_0_37, plain, ![X25, X26]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|k7_tmap_1(X25,X26)=k6_partfun1(u1_struct_0(X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.91/1.13  cnf(c_0_38, plain, (k2_struct_0(X1)=k1_xboole_0|k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k2_struct_0(X1))=k2_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.91/1.13  cnf(c_0_39, plain, (k8_relset_1(X1,X2,X3,X4)=k8_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_24, c_0_24])).
% 0.91/1.13  cnf(c_0_40, negated_conjecture, (k10_relat_1(k7_tmap_1(esk2_0,esk3_0),k2_struct_0(esk2_0))=k2_struct_0(esk2_0)|k2_struct_0(esk2_0)!=k1_xboole_0|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.91/1.13  cnf(c_0_41, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|k2_struct_0(X3)=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v3_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.13  cnf(c_0_42, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.91/1.13  fof(c_0_43, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|k8_relset_1(X9,X9,k6_partfun1(X9),X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).
% 0.91/1.13  cnf(c_0_44, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.91/1.13  fof(c_0_45, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X33,X34))))|(X35!=X34|v3_pre_topc(X35,k6_tmap_1(X33,X34)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).
% 0.91/1.13  cnf(c_0_46, plain, (k8_relset_1(X1,X2,X3,k2_struct_0(X4))=k2_struct_0(X5)|k2_struct_0(X4)=k1_xboole_0|~v1_funct_2(X3,u1_struct_0(X5),u1_struct_0(X4))|~v1_funct_1(X3)|~l1_struct_0(X5)|~l1_struct_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.91/1.13  cnf(c_0_47, negated_conjecture, (k8_relset_1(X1,X2,k7_tmap_1(esk2_0,esk3_0),k2_struct_0(esk2_0))=k2_struct_0(esk2_0)|k2_struct_0(esk2_0)!=k1_xboole_0|~l1_struct_0(esk2_0)|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_24, c_0_40])).
% 0.91/1.13  cnf(c_0_48, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)|~v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))|~v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_27]), c_0_42])])).
% 0.91/1.13  cnf(c_0_49, plain, (k8_relset_1(X2,X2,k6_partfun1(X2),X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.91/1.13  cnf(c_0_50, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.91/1.13  cnf(c_0_51, plain, (v2_struct_0(X1)|v3_pre_topc(X3,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|X3!=X2), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.91/1.13  cnf(c_0_52, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(X1),X2,k2_struct_0(X1))=k2_struct_0(k6_tmap_1(esk2_0,esk3_0))|k2_struct_0(k6_tmap_1(esk2_0,esk3_0))!=k1_xboole_0|~v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_struct_0(k6_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_25, c_0_27])).
% 0.91/1.13  cnf(c_0_53, negated_conjecture, (k8_relset_1(X1,X2,k7_tmap_1(esk2_0,esk3_0),k2_struct_0(esk2_0))=k2_struct_0(esk2_0)|~l1_struct_0(esk2_0)|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_32]), c_0_33]), c_0_34])]), c_0_47])).
% 0.91/1.13  fof(c_0_54, plain, ![X12]:(~l1_pre_topc(X12)|l1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.91/1.13  cnf(c_0_55, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_50]), c_0_33]), c_0_50]), c_0_34]), c_0_22]), c_0_50]), c_0_32])])).
% 0.91/1.13  cnf(c_0_56, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.91/1.13  cnf(c_0_57, plain, (v2_struct_0(X1)|v3_pre_topc(X2,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_51])).
% 0.91/1.13  cnf(c_0_58, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k2_struct_0(esk2_0)|k2_struct_0(k6_tmap_1(esk2_0,esk3_0))!=k1_xboole_0|~l1_struct_0(k6_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_33]), c_0_34]), c_0_32])])).
% 0.91/1.13  cnf(c_0_59, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.91/1.13  cnf(c_0_60, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(esk3_0,esk2_0)|v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.91/1.13  cnf(c_0_61, negated_conjecture, (v3_pre_topc(esk3_0,k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_27]), c_0_21]), c_0_22]), c_0_20])]), c_0_23])).
% 0.91/1.13  cnf(c_0_62, plain, (v5_pre_topc(X3,X1,X2)|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.13  cnf(c_0_63, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.13  cnf(c_0_64, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v3_pre_topc(X4,X3)|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.13  cnf(c_0_65, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k2_struct_0(esk2_0)|k2_struct_0(k6_tmap_1(esk2_0,esk3_0))!=k1_xboole_0|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_42])])).
% 0.91/1.13  cnf(c_0_66, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_20])])).
% 0.91/1.13  cnf(c_0_67, plain, (v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.13  cnf(c_0_68, plain, (v5_pre_topc(k6_partfun1(u1_struct_0(X1)),X1,X1)|k2_struct_0(X1)!=k1_xboole_0|~v3_pre_topc(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),X1)|~v1_funct_2(k6_partfun1(u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(X1))|~v1_funct_1(k6_partfun1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(k6_partfun1(u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~m1_subset_1(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_62, c_0_49])).
% 0.91/1.13  cnf(c_0_69, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.13  cnf(c_0_70, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(esk1_3(X1,k6_tmap_1(esk2_0,esk3_0),X2),k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_27]), c_0_42])])).
% 0.91/1.13  fof(c_0_71, plain, ![X13, X14, X15, X16]:((~v5_pre_topc(X15,X13,X14)|v5_pre_topc(X16,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),X14)|X15!=X16|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(X14))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(X14)))))|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|(~v2_pre_topc(X14)|~l1_pre_topc(X14))|(~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~v5_pre_topc(X16,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),X14)|v5_pre_topc(X15,X13,X14)|X15!=X16|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(X14))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(X14)))))|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|(~v2_pre_topc(X14)|~l1_pre_topc(X14))|(~v2_pre_topc(X13)|~l1_pre_topc(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.91/1.13  fof(c_0_72, plain, ![X36, X37]:((~v3_pre_topc(X37,X36)|g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36))=k6_tmap_1(X36,X37)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36))!=k6_tmap_1(X36,X37)|v3_pre_topc(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).
% 0.91/1.13  cnf(c_0_73, negated_conjecture, (v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)|k2_struct_0(X1)!=k1_xboole_0|~v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))|~v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_27]), c_0_42])])).
% 0.91/1.13  cnf(c_0_74, negated_conjecture, (k2_struct_0(esk2_0)=k1_xboole_0|v3_pre_topc(esk3_0,esk2_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.91/1.13  cnf(c_0_75, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.13  cnf(c_0_76, plain, (v5_pre_topc(k6_partfun1(u1_struct_0(X1)),X1,X1)|~v3_pre_topc(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),X1)|~v1_funct_2(k6_partfun1(u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(X1))|~v1_funct_1(k6_partfun1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(k6_partfun1(u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~m1_subset_1(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_49]), c_0_68])).
% 0.91/1.13  cnf(c_0_77, negated_conjecture, (k7_tmap_1(esk2_0,X1)=k7_tmap_1(esk2_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_50]), c_0_21]), c_0_22])]), c_0_23])).
% 0.91/1.13  cnf(c_0_78, negated_conjecture, (v3_pre_topc(esk1_3(X1,k6_tmap_1(esk2_0,esk3_0),X2),k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_27]), c_0_42])])).
% 0.91/1.13  cnf(c_0_79, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_27]), c_0_42])])).
% 0.91/1.13  cnf(c_0_80, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.91/1.13  cnf(c_0_81, plain, (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=k6_tmap_1(X2,X1)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.91/1.13  cnf(c_0_82, negated_conjecture, (v3_pre_topc(X1,esk2_0)|k2_struct_0(esk2_0)!=k1_xboole_0|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_49]), c_0_50]), c_0_50]), c_0_33]), c_0_50]), c_0_34]), c_0_22]), c_0_50]), c_0_32])])).
% 0.91/1.13  cnf(c_0_83, negated_conjecture, (k2_struct_0(esk2_0)=k1_xboole_0|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_59]), c_0_22])])).
% 0.91/1.13  cnf(c_0_84, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.13  cnf(c_0_85, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_27]), c_0_42])])).
% 0.91/1.13  cnf(c_0_86, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_27]), c_0_50]), c_0_50]), c_0_50]), c_0_33]), c_0_50]), c_0_34]), c_0_42]), c_0_50]), c_0_32]), c_0_50])])).
% 0.91/1.13  cnf(c_0_87, negated_conjecture, (k7_tmap_1(esk2_0,X1)=k7_tmap_1(esk2_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_77, c_0_77])).
% 0.91/1.13  cnf(c_0_88, negated_conjecture, (v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_27]), c_0_42])]), c_0_79])).
% 0.91/1.13  cnf(c_0_89, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.91/1.13  cnf(c_0_90, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_80])).
% 0.91/1.13  cnf(c_0_91, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k6_tmap_1(esk2_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.91/1.13  cnf(c_0_92, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_56])).
% 0.91/1.13  cnf(c_0_93, negated_conjecture, (v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_27]), c_0_42])])).
% 0.91/1.13  cnf(c_0_94, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_27]), c_0_42])])).
% 0.91/1.13  cnf(c_0_95, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,X1),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,X1)),k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,X1)),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_20])])).
% 0.91/1.13  cnf(c_0_96, negated_conjecture, (v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_32]), c_0_33]), c_0_34])])).
% 0.91/1.13  cnf(c_0_97, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_34])]), c_0_27]), c_0_33]), c_0_27])])).
% 0.91/1.13  cnf(c_0_98, negated_conjecture, (v5_pre_topc(X1,esk2_0,X2)|~v3_pre_topc(esk3_0,esk2_0)|~v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),X2)|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(X2))|~v1_funct_1(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_27]), c_0_21]), c_0_22]), c_0_27])])).
% 0.91/1.13  cnf(c_0_99, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_92]), c_0_61]), c_0_20])])).
% 0.91/1.13  cnf(c_0_100, negated_conjecture, (v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_27]), c_0_42])]), c_0_94])).
% 0.91/1.13  cnf(c_0_101, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_20])])).
% 0.91/1.13  cnf(c_0_102, plain, (v2_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.91/1.13  cnf(c_0_103, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_32])])).
% 0.91/1.13  cnf(c_0_104, negated_conjecture, (v5_pre_topc(X1,esk2_0,X2)|~v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),X2)|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(X2))|~v1_funct_1(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99])])).
% 0.91/1.13  cnf(c_0_105, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_32]), c_0_33]), c_0_34])]), c_0_101])).
% 0.91/1.13  cnf(c_0_106, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.91/1.13  cnf(c_0_107, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_99])])).
% 0.91/1.13  cnf(c_0_108, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_27]), c_0_33]), c_0_34]), c_0_106]), c_0_42]), c_0_27]), c_0_32])]), c_0_107]), ['proof']).
% 0.91/1.13  # SZS output end CNFRefutation
% 0.91/1.13  # Proof object total steps             : 109
% 0.91/1.13  # Proof object clause steps            : 82
% 0.91/1.13  # Proof object formula steps           : 27
% 0.91/1.13  # Proof object conjectures             : 55
% 0.91/1.13  # Proof object clause conjectures      : 52
% 0.91/1.13  # Proof object formula conjectures     : 3
% 0.91/1.13  # Proof object initial clauses used    : 29
% 0.91/1.13  # Proof object initial formulas used   : 13
% 0.91/1.13  # Proof object generating inferences   : 47
% 0.91/1.13  # Proof object simplifying inferences  : 155
% 0.91/1.13  # Training examples: 0 positive, 0 negative
% 0.91/1.13  # Parsed axioms                        : 14
% 0.91/1.13  # Removed by relevancy pruning/SinE    : 0
% 0.91/1.13  # Initial clauses                      : 37
% 0.91/1.13  # Removed in clause preprocessing      : 0
% 0.91/1.13  # Initial clauses in saturation        : 37
% 0.91/1.13  # Processed clauses                    : 3591
% 0.91/1.13  # ...of these trivial                  : 81
% 0.91/1.13  # ...subsumed                          : 2333
% 0.91/1.13  # ...remaining for further processing  : 1177
% 0.91/1.13  # Other redundant clauses eliminated   : 3
% 0.91/1.13  # Clauses deleted for lack of memory   : 0
% 0.91/1.13  # Backward-subsumed                    : 186
% 0.91/1.13  # Backward-rewritten                   : 432
% 0.91/1.13  # Generated clauses                    : 10942
% 0.91/1.13  # ...of the previous two non-trivial   : 10042
% 0.91/1.13  # Contextual simplify-reflections      : 534
% 0.91/1.13  # Paramodulations                      : 10907
% 0.91/1.13  # Factorizations                       : 11
% 0.91/1.13  # Equation resolutions                 : 3
% 0.91/1.13  # Propositional unsat checks           : 0
% 0.91/1.13  #    Propositional check models        : 0
% 0.91/1.13  #    Propositional check unsatisfiable : 0
% 0.91/1.13  #    Propositional clauses             : 0
% 0.91/1.13  #    Propositional clauses after purity: 0
% 0.91/1.13  #    Propositional unsat core size     : 0
% 0.91/1.13  #    Propositional preprocessing time  : 0.000
% 0.91/1.13  #    Propositional encoding time       : 0.000
% 0.91/1.13  #    Propositional solver time         : 0.000
% 0.91/1.13  #    Success case prop preproc time    : 0.000
% 0.91/1.13  #    Success case prop encoding time   : 0.000
% 0.91/1.13  #    Success case prop solver time     : 0.000
% 0.91/1.13  # Current number of processed clauses  : 535
% 0.91/1.13  #    Positive orientable unit clauses  : 34
% 0.91/1.13  #    Positive unorientable unit clauses: 0
% 0.91/1.13  #    Negative unit clauses             : 5
% 0.91/1.13  #    Non-unit-clauses                  : 496
% 0.91/1.13  # Current number of unprocessed clauses: 5512
% 0.91/1.13  # ...number of literals in the above   : 50328
% 0.91/1.13  # Current number of archived formulas  : 0
% 0.91/1.13  # Current number of archived clauses   : 639
% 0.91/1.13  # Clause-clause subsumption calls (NU) : 422616
% 0.91/1.13  # Rec. Clause-clause subsumption calls : 18310
% 0.91/1.13  # Non-unit clause-clause subsumptions  : 2769
% 0.91/1.13  # Unit Clause-clause subsumption calls : 3436
% 0.91/1.13  # Rewrite failures with RHS unbound    : 0
% 0.91/1.13  # BW rewrite match attempts            : 51
% 0.91/1.13  # BW rewrite match successes           : 20
% 0.91/1.13  # Condensation attempts                : 0
% 0.91/1.13  # Condensation successes               : 0
% 0.91/1.13  # Termbank termtop insertions          : 562830
% 0.91/1.14  
% 0.91/1.14  # -------------------------------------------------
% 0.91/1.14  # User time                : 0.779 s
% 0.91/1.14  # System time              : 0.013 s
% 0.91/1.14  # Total time               : 0.791 s
% 0.91/1.14  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
