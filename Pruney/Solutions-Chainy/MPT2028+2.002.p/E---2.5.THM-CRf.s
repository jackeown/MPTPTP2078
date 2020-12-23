%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 278 expanded)
%              Number of clauses        :   41 ( 107 expanded)
%              Number of leaves         :   11 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 (1801 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

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

fof(dt_k6_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_waybel_0)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(fc9_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k6_waybel_0(X1,X2))
        & v2_waybel_0(k6_waybel_0(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_waybel_0)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | ~ v1_lattice3(X14)
      | ~ v2_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_13,negated_conjecture,(
    ! [X28] :
      ( v2_pre_topc(esk2_0)
      & v8_pre_topc(esk2_0)
      & v3_orders_2(esk2_0)
      & v4_orders_2(esk2_0)
      & v5_orders_2(esk2_0)
      & v1_lattice3(esk2_0)
      & v2_lattice3(esk2_0)
      & l1_waybel_9(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & ( ~ m1_subset_1(X28,u1_struct_0(esk2_0))
        | v5_pre_topc(k4_waybel_1(esk2_0,X28),esk2_0,esk2_0) )
      & ~ v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X21] :
      ( ( l1_pre_topc(X21)
        | ~ l1_waybel_9(X21) )
      & ( l1_orders_2(X21)
        | ~ l1_waybel_9(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

cnf(c_0_15,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_waybel_9(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X19,X20] :
      ( ( v1_funct_1(k4_waybel_1(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( v1_funct_2(k4_waybel_1(X19,X20),u1_struct_0(X19),u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( m1_subset_1(k4_waybel_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X19))))
        | v2_struct_0(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_1])])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    | ~ l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ v5_pre_topc(X9,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v4_pre_topc(X10,X8)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9,X10),X7)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),k1_zfmisc_1(u1_struct_0(X8)))
        | v5_pre_topc(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( v4_pre_topc(esk1_3(X7,X8,X9),X8)
        | v5_pre_topc(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9,esk1_3(X7,X8,X9)),X7)
        | v5_pre_topc(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_23,plain,
    ( v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk2_0,X1),esk2_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( v1_funct_1(k4_waybel_1(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( l1_pre_topc(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ v8_pre_topc(X22)
      | v4_pre_topc(k6_domain_1(u1_struct_0(X22),X23),X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_pcomps_1])])])])).

fof(c_0_31,plain,(
    ! [X24,X25] :
      ( ~ v3_orders_2(X24)
      | ~ v5_orders_2(X24)
      | ~ v2_lattice3(X24)
      | ~ l1_orders_2(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | k8_relset_1(u1_struct_0(X24),u1_struct_0(X24),k4_waybel_1(X24,X25),k6_domain_1(u1_struct_0(X24),X25)) = k6_waybel_0(X24,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_waybel_9])])])).

fof(c_0_32,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | m1_subset_1(k6_waybel_0(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_waybel_0])])])).

fof(c_0_33,plain,(
    ! [X12,X13] :
      ( v1_xboole_0(X12)
      | ~ m1_subset_1(X13,X12)
      | m1_subset_1(k6_domain_1(X12,X13),k1_zfmisc_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_34,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(k4_waybel_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk2_0,esk3_0),esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(k4_waybel_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k4_waybel_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | v4_pre_topc(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( v8_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_43,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_domain_1(u1_struct_0(X1),X2)) = k6_waybel_0(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( v2_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_47,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_xboole_0(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),X1),esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_51,negated_conjecture,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_24]),c_0_41]),c_0_42]),c_0_38])]),c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),k6_domain_1(u1_struct_0(esk2_0),esk3_0)) = k6_waybel_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_24]),c_0_44]),c_0_45]),c_0_46]),c_0_21])])).

cnf(c_0_53,negated_conjecture,
    ( ~ v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k6_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])).

fof(c_0_58,plain,(
    ! [X17,X18] :
      ( ( ~ v1_xboole_0(k6_waybel_0(X17,X18))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17)) )
      & ( v2_waybel_0(k6_waybel_0(X17,X18),X17)
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_waybel_0])])])])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(k6_waybel_0(esk2_0,esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k6_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(k6_waybel_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_46]),c_0_21]),c_0_24])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.36  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.016 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t27_waybel_9, conjecture, ![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X3),X1,X1))=>v4_pre_topc(k6_waybel_0(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_waybel_9)).
% 0.19/0.36  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.19/0.36  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.19/0.36  fof(dt_k4_waybel_1, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((v1_funct_1(k4_waybel_1(X1,X2))&v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1)))&m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 0.19/0.36  fof(d12_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X4,X2)=>v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 0.19/0.36  fof(t10_pcomps_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v8_pre_topc(X1)=>v4_pre_topc(k6_domain_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_pcomps_1)).
% 0.19/0.36  fof(t7_waybel_9, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_domain_1(u1_struct_0(X1),X2))=k6_waybel_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_waybel_9)).
% 0.19/0.36  fof(dt_k6_waybel_0, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_waybel_0)).
% 0.19/0.36  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.19/0.36  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.36  fof(fc9_waybel_0, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>(~(v1_xboole_0(k6_waybel_0(X1,X2)))&v2_waybel_0(k6_waybel_0(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_waybel_0)).
% 0.19/0.36  fof(c_0_11, negated_conjecture, ~(![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X3),X1,X1))=>v4_pre_topc(k6_waybel_0(X1,X2),X1))))), inference(assume_negation,[status(cth)],[t27_waybel_9])).
% 0.19/0.36  fof(c_0_12, plain, ![X14]:(~l1_orders_2(X14)|(~v1_lattice3(X14)|~v2_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.19/0.36  fof(c_0_13, negated_conjecture, ![X28]:((((((((v2_pre_topc(esk2_0)&v8_pre_topc(esk2_0))&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&v1_lattice3(esk2_0))&v2_lattice3(esk2_0))&l1_waybel_9(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((~m1_subset_1(X28,u1_struct_0(esk2_0))|v5_pre_topc(k4_waybel_1(esk2_0,X28),esk2_0,esk2_0))&~v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.19/0.36  fof(c_0_14, plain, ![X21]:((l1_pre_topc(X21)|~l1_waybel_9(X21))&(l1_orders_2(X21)|~l1_waybel_9(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.19/0.36  cnf(c_0_15, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  cnf(c_0_16, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  cnf(c_0_17, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.36  cnf(c_0_18, negated_conjecture, (l1_waybel_9(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  fof(c_0_19, plain, ![X19, X20]:(((v1_funct_1(k4_waybel_1(X19,X20))|(v2_struct_0(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))))&(v1_funct_2(k4_waybel_1(X19,X20),u1_struct_0(X19),u1_struct_0(X19))|(v2_struct_0(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19)))))&(m1_subset_1(k4_waybel_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X19))))|(v2_struct_0(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_1])])])])).
% 0.19/0.36  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)|~l1_orders_2(esk2_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.36  cnf(c_0_21, negated_conjecture, (l1_orders_2(esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.36  fof(c_0_22, plain, ![X7, X8, X9, X10]:((~v5_pre_topc(X9,X7,X8)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|(~v4_pre_topc(X10,X8)|v4_pre_topc(k8_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9,X10),X7)))|(~v1_funct_1(X9)|~v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8)))))|~l1_pre_topc(X8)|~l1_pre_topc(X7))&((m1_subset_1(esk1_3(X7,X8,X9),k1_zfmisc_1(u1_struct_0(X8)))|v5_pre_topc(X9,X7,X8)|(~v1_funct_1(X9)|~v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8)))))|~l1_pre_topc(X8)|~l1_pre_topc(X7))&((v4_pre_topc(esk1_3(X7,X8,X9),X8)|v5_pre_topc(X9,X7,X8)|(~v1_funct_1(X9)|~v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8)))))|~l1_pre_topc(X8)|~l1_pre_topc(X7))&(~v4_pre_topc(k8_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9,esk1_3(X7,X8,X9)),X7)|v5_pre_topc(X9,X7,X8)|(~v1_funct_1(X9)|~v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8)))))|~l1_pre_topc(X8)|~l1_pre_topc(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).
% 0.19/0.36  cnf(c_0_23, plain, (v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.36  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])])).
% 0.19/0.36  cnf(c_0_26, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk2_0,X1),esk2_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  cnf(c_0_27, plain, (v1_funct_1(k4_waybel_1(X1,X2))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.36  cnf(c_0_28, plain, (l1_pre_topc(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.36  cnf(c_0_29, plain, (m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.36  fof(c_0_30, plain, ![X22, X23]:(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~m1_subset_1(X23,u1_struct_0(X22))|(~v8_pre_topc(X22)|v4_pre_topc(k6_domain_1(u1_struct_0(X22),X23),X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_pcomps_1])])])])).
% 0.19/0.36  fof(c_0_31, plain, ![X24, X25]:(~v3_orders_2(X24)|~v5_orders_2(X24)|~v2_lattice3(X24)|~l1_orders_2(X24)|(~m1_subset_1(X25,u1_struct_0(X24))|k8_relset_1(u1_struct_0(X24),u1_struct_0(X24),k4_waybel_1(X24,X25),k6_domain_1(u1_struct_0(X24),X25))=k6_waybel_0(X24,X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_waybel_9])])])).
% 0.19/0.36  fof(c_0_32, plain, ![X15, X16]:(v2_struct_0(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|m1_subset_1(k6_waybel_0(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_waybel_0])])])).
% 0.19/0.36  fof(c_0_33, plain, ![X12, X13]:(v1_xboole_0(X12)|~m1_subset_1(X13,X12)|m1_subset_1(k6_domain_1(X12,X13),k1_zfmisc_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.19/0.36  cnf(c_0_34, plain, (v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v4_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.36  cnf(c_0_35, negated_conjecture, (v1_funct_2(k4_waybel_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21])]), c_0_25])).
% 0.19/0.36  cnf(c_0_36, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk2_0,esk3_0),esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.19/0.36  cnf(c_0_37, negated_conjecture, (v1_funct_1(k4_waybel_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_21])]), c_0_25])).
% 0.19/0.36  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.19/0.36  cnf(c_0_39, negated_conjecture, (m1_subset_1(k4_waybel_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_21])]), c_0_25])).
% 0.19/0.36  cnf(c_0_40, plain, (v2_struct_0(X1)|v4_pre_topc(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v8_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.36  cnf(c_0_41, negated_conjecture, (v8_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  cnf(c_0_42, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  cnf(c_0_43, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_domain_1(u1_struct_0(X1),X2))=k6_waybel_0(X1,X2)|~v3_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.36  cnf(c_0_44, negated_conjecture, (v2_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  cnf(c_0_45, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  cnf(c_0_46, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  fof(c_0_47, plain, ![X5, X6]:(~v1_xboole_0(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.36  cnf(c_0_48, plain, (v2_struct_0(X1)|m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.36  cnf(c_0_49, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.36  cnf(c_0_50, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),X1),esk2_0)|~v4_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])])).
% 0.19/0.36  cnf(c_0_51, negated_conjecture, (v4_pre_topc(k6_domain_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_24]), c_0_41]), c_0_42]), c_0_38])]), c_0_25])).
% 0.19/0.36  cnf(c_0_52, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),k6_domain_1(u1_struct_0(esk2_0),esk3_0))=k6_waybel_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_24]), c_0_44]), c_0_45]), c_0_46]), c_0_21])])).
% 0.19/0.36  cnf(c_0_53, negated_conjecture, (~v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  cnf(c_0_54, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.36  cnf(c_0_55, negated_conjecture, (m1_subset_1(k6_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_24]), c_0_21])]), c_0_25])).
% 0.19/0.36  cnf(c_0_56, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_49, c_0_24])).
% 0.19/0.36  cnf(c_0_57, negated_conjecture, (~m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])).
% 0.19/0.36  fof(c_0_58, plain, ![X17, X18]:((~v1_xboole_0(k6_waybel_0(X17,X18))|(v2_struct_0(X17)|~v3_orders_2(X17)|~l1_orders_2(X17)|~m1_subset_1(X18,u1_struct_0(X17))))&(v2_waybel_0(k6_waybel_0(X17,X18),X17)|(v2_struct_0(X17)|~v3_orders_2(X17)|~l1_orders_2(X17)|~m1_subset_1(X18,u1_struct_0(X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_waybel_0])])])])).
% 0.19/0.36  cnf(c_0_59, negated_conjecture, (v1_xboole_0(k6_waybel_0(esk2_0,esk3_0))|~v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.36  cnf(c_0_60, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.36  cnf(c_0_61, plain, (v2_struct_0(X1)|~v1_xboole_0(k6_waybel_0(X1,X2))|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.36  cnf(c_0_62, negated_conjecture, (v1_xboole_0(k6_waybel_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 0.19/0.36  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_46]), c_0_21]), c_0_24])]), c_0_25]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 64
% 0.19/0.36  # Proof object clause steps            : 41
% 0.19/0.36  # Proof object formula steps           : 23
% 0.19/0.36  # Proof object conjectures             : 31
% 0.19/0.36  # Proof object clause conjectures      : 28
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 23
% 0.19/0.36  # Proof object initial formulas used   : 11
% 0.19/0.36  # Proof object generating inferences   : 15
% 0.19/0.36  # Proof object simplifying inferences  : 39
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 11
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 28
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 28
% 0.19/0.36  # Processed clauses                    : 80
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 0
% 0.19/0.36  # ...remaining for further processing  : 80
% 0.19/0.36  # Other redundant clauses eliminated   : 0
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 4
% 0.19/0.36  # Generated clauses                    : 35
% 0.19/0.36  # ...of the previous two non-trivial   : 27
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 34
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 0
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 47
% 0.19/0.36  #    Positive orientable unit clauses  : 21
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 3
% 0.19/0.36  #    Non-unit-clauses                  : 23
% 0.19/0.36  # Current number of unprocessed clauses: 3
% 0.19/0.36  # ...number of literals in the above   : 12
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 33
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 558
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 102
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.36  # Unit Clause-clause subsumption calls : 37
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 2
% 0.19/0.36  # BW rewrite match successes           : 2
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 3872
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.017 s
% 0.19/0.36  # System time              : 0.005 s
% 0.19/0.36  # Total time               : 0.022 s
% 0.19/0.36  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
