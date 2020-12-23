%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 260 expanded)
%              Number of clauses        :   35 (  98 expanded)
%              Number of leaves         :    9 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  222 (1733 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_waybel_9,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_waybel_9(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => v5_pre_topc(k4_waybel_1(X1,X3),X1,X1) )
           => v4_pre_topc(k6_waybel_0(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_waybel_9)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(dt_l1_waybel_9,axiom,(
    ! [X1] :
      ( l1_waybel_9(X1)
     => ( l1_pre_topc(X1)
        & l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(dt_k4_waybel_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( v1_funct_1(k4_waybel_1(X1,X2))
        & v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
        & m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(t6_waybel_9,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k7_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_waybel_0(X1,X2)) = k6_domain_1(u1_struct_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_waybel_9)).

fof(d12_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( v4_pre_topc(X4,X2)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

fof(t10_pcomps_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v8_pre_topc(X1)
           => v4_pre_topc(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_pcomps_1)).

fof(t7_waybel_9,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_domain_1(u1_struct_0(X1),X2)) = k6_waybel_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_waybel_9)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & v8_pre_topc(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_waybel_9(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => v5_pre_topc(k4_waybel_1(X1,X3),X1,X1) )
             => v4_pre_topc(k6_waybel_0(X1,X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_waybel_9])).

fof(c_0_10,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | ~ v2_lattice3(X14)
      | ~ v2_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_11,negated_conjecture,(
    ! [X26] :
      ( v2_pre_topc(esk2_0)
      & v8_pre_topc(esk2_0)
      & v3_orders_2(esk2_0)
      & v4_orders_2(esk2_0)
      & v5_orders_2(esk2_0)
      & v1_lattice3(esk2_0)
      & v2_lattice3(esk2_0)
      & l1_waybel_9(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & ( ~ m1_subset_1(X26,u1_struct_0(esk2_0))
        | v5_pre_topc(k4_waybel_1(esk2_0,X26),esk2_0,esk2_0) )
      & ~ v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X17] :
      ( ( l1_pre_topc(X17)
        | ~ l1_waybel_9(X17) )
      & ( l1_orders_2(X17)
        | ~ l1_waybel_9(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

cnf(c_0_13,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v2_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_waybel_9(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ( v1_funct_1(k4_waybel_1(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15)) )
      & ( v1_funct_2(k4_waybel_1(X15,X16),u1_struct_0(X15),u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15)) )
      & ( m1_subset_1(k4_waybel_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X15))))
        | v2_struct_0(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_1])])])])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    | ~ l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X5,X6,X7,X8] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | m1_subset_1(k7_relset_1(X5,X6,X7,X8),k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_21,plain,
    ( m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ~ v3_orders_2(X20)
      | ~ v5_orders_2(X20)
      | ~ v2_lattice3(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | k7_relset_1(u1_struct_0(X20),u1_struct_0(X20),k4_waybel_1(X20,X21),k6_waybel_0(X20,X21)) = k6_domain_1(u1_struct_0(X20),X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_waybel_9])])])).

fof(c_0_25,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v5_pre_topc(X11,X9,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v4_pre_topc(X12,X10)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,X12),X9)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(u1_struct_0(X10)))
        | v5_pre_topc(X11,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) )
      & ( v4_pre_topc(esk1_3(X9,X10,X11),X10)
        | v5_pre_topc(X11,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,esk1_3(X9,X10,X11)),X9)
        | v5_pre_topc(X11,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_26,plain,
    ( v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk2_0,X1),esk2_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( v1_funct_1(k4_waybel_1(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( l1_pre_topc(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_30,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v8_pre_topc(X18)
      | v4_pre_topc(k6_domain_1(u1_struct_0(X18),X19),X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_pcomps_1])])])])).

fof(c_0_31,plain,(
    ! [X22,X23] :
      ( ~ v3_orders_2(X22)
      | ~ v5_orders_2(X22)
      | ~ v2_lattice3(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | k8_relset_1(u1_struct_0(X22),u1_struct_0(X22),k4_waybel_1(X22,X23),k6_domain_1(u1_struct_0(X22),X23)) = k6_waybel_0(X22,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_waybel_9])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k4_waybel_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19])]),c_0_23])).

cnf(c_0_34,plain,
    ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_waybel_0(X1,X2)) = k6_domain_1(u1_struct_0(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(k4_waybel_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_22]),c_0_19])]),c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk2_0,esk3_0),esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(k4_waybel_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_19])]),c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v4_pre_topc(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( v8_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_domain_1(u1_struct_0(X1),X2)) = k6_waybel_0(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),k6_waybel_0(esk2_0,esk3_0)) = k6_domain_1(u1_struct_0(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_22]),c_0_35]),c_0_36]),c_0_14]),c_0_19])])).

cnf(c_0_48,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),X1),esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_33])])).

cnf(c_0_49,negated_conjecture,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_22]),c_0_43]),c_0_44]),c_0_41])]),c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),k6_domain_1(u1_struct_0(esk2_0),esk3_0)) = k6_waybel_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_22]),c_0_35]),c_0_36]),c_0_14]),c_0_19])])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( ~ v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t27_waybel_9, conjecture, ![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X3),X1,X1))=>v4_pre_topc(k6_waybel_0(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_waybel_9)).
% 0.19/0.38  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.19/0.38  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.19/0.38  fof(dt_k4_waybel_1, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((v1_funct_1(k4_waybel_1(X1,X2))&v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1)))&m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 0.19/0.38  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.19/0.38  fof(t6_waybel_9, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_waybel_0(X1,X2))=k6_domain_1(u1_struct_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_waybel_9)).
% 0.19/0.38  fof(d12_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X4,X2)=>v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 0.19/0.38  fof(t10_pcomps_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v8_pre_topc(X1)=>v4_pre_topc(k6_domain_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_pcomps_1)).
% 0.19/0.38  fof(t7_waybel_9, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_domain_1(u1_struct_0(X1),X2))=k6_waybel_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_waybel_9)).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X3),X1,X1))=>v4_pre_topc(k6_waybel_0(X1,X2),X1))))), inference(assume_negation,[status(cth)],[t27_waybel_9])).
% 0.19/0.38  fof(c_0_10, plain, ![X14]:(~l1_orders_2(X14)|(~v2_lattice3(X14)|~v2_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.19/0.38  fof(c_0_11, negated_conjecture, ![X26]:((((((((v2_pre_topc(esk2_0)&v8_pre_topc(esk2_0))&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&v1_lattice3(esk2_0))&v2_lattice3(esk2_0))&l1_waybel_9(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((~m1_subset_1(X26,u1_struct_0(esk2_0))|v5_pre_topc(k4_waybel_1(esk2_0,X26),esk2_0,esk2_0))&~v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.19/0.38  fof(c_0_12, plain, ![X17]:((l1_pre_topc(X17)|~l1_waybel_9(X17))&(l1_orders_2(X17)|~l1_waybel_9(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.19/0.38  cnf(c_0_13, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (v2_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_15, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (l1_waybel_9(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  fof(c_0_17, plain, ![X15, X16]:(((v1_funct_1(k4_waybel_1(X15,X16))|(v2_struct_0(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))))&(v1_funct_2(k4_waybel_1(X15,X16),u1_struct_0(X15),u1_struct_0(X15))|(v2_struct_0(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15)))))&(m1_subset_1(k4_waybel_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X15))))|(v2_struct_0(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_1])])])])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk2_0)|~l1_orders_2(esk2_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk2_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.38  fof(c_0_20, plain, ![X5, X6, X7, X8]:(~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|m1_subset_1(k7_relset_1(X5,X6,X7,X8),k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.19/0.38  cnf(c_0_21, plain, (m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19])])).
% 0.19/0.38  fof(c_0_24, plain, ![X20, X21]:(~v3_orders_2(X20)|~v5_orders_2(X20)|~v2_lattice3(X20)|~l1_orders_2(X20)|(~m1_subset_1(X21,u1_struct_0(X20))|k7_relset_1(u1_struct_0(X20),u1_struct_0(X20),k4_waybel_1(X20,X21),k6_waybel_0(X20,X21))=k6_domain_1(u1_struct_0(X20),X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_waybel_9])])])).
% 0.19/0.38  fof(c_0_25, plain, ![X9, X10, X11, X12]:((~v5_pre_topc(X11,X9,X10)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))|(~v4_pre_topc(X12,X10)|v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,X12),X9)))|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))&((m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(u1_struct_0(X10)))|v5_pre_topc(X11,X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))&((v4_pre_topc(esk1_3(X9,X10,X11),X10)|v5_pre_topc(X11,X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))&(~v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,esk1_3(X9,X10,X11)),X9)|v5_pre_topc(X11,X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|~l1_pre_topc(X10)|~l1_pre_topc(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).
% 0.19/0.38  cnf(c_0_26, plain, (v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk2_0,X1),esk2_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_28, plain, (v1_funct_1(k4_waybel_1(X1,X2))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_29, plain, (l1_pre_topc(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_30, plain, ![X18, X19]:(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|(~v8_pre_topc(X18)|v4_pre_topc(k6_domain_1(u1_struct_0(X18),X19),X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_pcomps_1])])])])).
% 0.19/0.38  fof(c_0_31, plain, ![X22, X23]:(~v3_orders_2(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)|(~m1_subset_1(X23,u1_struct_0(X22))|k8_relset_1(u1_struct_0(X22),u1_struct_0(X22),k4_waybel_1(X22,X23),k6_domain_1(u1_struct_0(X22),X23))=k6_waybel_0(X22,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_waybel_9])])])).
% 0.19/0.38  cnf(c_0_32, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(k4_waybel_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_19])]), c_0_23])).
% 0.19/0.38  cnf(c_0_34, plain, (k7_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_waybel_0(X1,X2))=k6_domain_1(u1_struct_0(X1),X2)|~v3_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_37, plain, (v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v4_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (v1_funct_2(k4_waybel_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_22]), c_0_19])]), c_0_23])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk2_0,esk3_0),esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (v1_funct_1(k4_waybel_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_22]), c_0_19])]), c_0_23])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_16])).
% 0.19/0.38  cnf(c_0_42, plain, (v2_struct_0(X1)|v4_pre_topc(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v8_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (v8_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_45, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_domain_1(u1_struct_0(X1),X2))=k6_waybel_0(X1,X2)|~v3_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),k6_waybel_0(esk2_0,esk3_0))=k6_domain_1(u1_struct_0(esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_22]), c_0_35]), c_0_36]), c_0_14]), c_0_19])])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),X1),esk2_0)|~v4_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_33])])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (v4_pre_topc(k6_domain_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_22]), c_0_43]), c_0_44]), c_0_41])]), c_0_23])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),k6_domain_1(u1_struct_0(esk2_0),esk3_0))=k6_waybel_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_22]), c_0_35]), c_0_36]), c_0_14]), c_0_19])])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (~v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])]), c_0_52]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 54
% 0.19/0.38  # Proof object clause steps            : 35
% 0.19/0.38  # Proof object formula steps           : 19
% 0.19/0.38  # Proof object conjectures             : 27
% 0.19/0.38  # Proof object clause conjectures      : 24
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 20
% 0.19/0.38  # Proof object initial formulas used   : 9
% 0.19/0.38  # Proof object generating inferences   : 14
% 0.19/0.38  # Proof object simplifying inferences  : 35
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 9
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 25
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 25
% 0.19/0.38  # Processed clauses                    : 64
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 64
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 1
% 0.19/0.38  # Generated clauses                    : 17
% 0.19/0.38  # ...of the previous two non-trivial   : 14
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 17
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 38
% 0.19/0.38  #    Positive orientable unit clauses  : 20
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 16
% 0.19/0.38  # Current number of unprocessed clauses: 0
% 0.19/0.38  # ...number of literals in the above   : 0
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 26
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 392
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 54
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 3
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 2
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3203
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.029 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.035 s
% 0.19/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
