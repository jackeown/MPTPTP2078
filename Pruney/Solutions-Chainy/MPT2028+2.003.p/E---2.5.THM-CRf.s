%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:44 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 291 expanded)
%              Number of clauses        :   46 ( 113 expanded)
%              Number of leaves         :   13 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  276 (1859 expanded)
%              Number of equality atoms :    8 (   8 expanded)
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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(dt_k4_waybel_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( v1_funct_1(k4_waybel_1(X1,X2))
        & v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
        & m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

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

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | ~ v1_lattice3(X18)
      | ~ v2_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_15,negated_conjecture,(
    ! [X32] :
      ( v2_pre_topc(esk2_0)
      & v8_pre_topc(esk2_0)
      & v3_orders_2(esk2_0)
      & v4_orders_2(esk2_0)
      & v5_orders_2(esk2_0)
      & v1_lattice3(esk2_0)
      & v2_lattice3(esk2_0)
      & l1_waybel_9(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & ( ~ m1_subset_1(X32,u1_struct_0(esk2_0))
        | v5_pre_topc(k4_waybel_1(esk2_0,X32),esk2_0,esk2_0) )
      & ~ v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X25] :
      ( ( l1_pre_topc(X25)
        | ~ l1_waybel_9(X25) )
      & ( l1_orders_2(X25)
        | ~ l1_waybel_9(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

cnf(c_0_17,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_waybel_9(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X9,X10)
      | v1_xboole_0(X10)
      | r2_hidden(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_22,plain,(
    ! [X23,X24] :
      ( ( v1_funct_1(k4_waybel_1(X23,X24))
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) )
      & ( v1_funct_2(k4_waybel_1(X23,X24),u1_struct_0(X23),u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) )
      & ( m1_subset_1(k4_waybel_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_1])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    | ~ l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | m1_subset_1(k1_tarski(X5),k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( v1_xboole_0(X16)
      | ~ m1_subset_1(X17,X16)
      | k6_domain_1(X16,X17) = k1_tarski(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_29,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ v5_pre_topc(X13,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v4_pre_topc(X14,X12)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X11),u1_struct_0(X12),X13,X14),X11)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
        | ~ l1_pre_topc(X12)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v5_pre_topc(X13,X11,X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
        | ~ l1_pre_topc(X12)
        | ~ l1_pre_topc(X11) )
      & ( v4_pre_topc(esk1_3(X11,X12,X13),X12)
        | v5_pre_topc(X13,X11,X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
        | ~ l1_pre_topc(X12)
        | ~ l1_pre_topc(X11) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X11),u1_struct_0(X12),X13,esk1_3(X11,X12,X13)),X11)
        | v5_pre_topc(X13,X11,X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
        | ~ l1_pre_topc(X12)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_30,plain,
    ( v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk2_0,X1),esk2_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( v1_funct_1(k4_waybel_1(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( l1_pre_topc(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_36,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | ~ v8_pre_topc(X26)
      | v4_pre_topc(k6_domain_1(u1_struct_0(X26),X27),X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_pcomps_1])])])])).

fof(c_0_37,plain,(
    ! [X28,X29] :
      ( ~ v3_orders_2(X28)
      | ~ v5_orders_2(X28)
      | ~ v2_lattice3(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | k8_relset_1(u1_struct_0(X28),u1_struct_0(X28),k4_waybel_1(X28,X29),k6_domain_1(u1_struct_0(X28),X29)) = k6_waybel_0(X28,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_waybel_9])])])).

fof(c_0_38,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | m1_subset_1(k6_waybel_0(X19,X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_waybel_0])])])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(k4_waybel_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_24])]),c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk2_0,esk3_0),esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(k4_waybel_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_24])]),c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k4_waybel_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_24])]),c_0_31])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | v4_pre_topc(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( v8_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_domain_1(u1_struct_0(X1),X2)) = k6_waybel_0(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( v2_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_55,plain,(
    ! [X7,X8] :
      ( ~ v1_xboole_0(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_xboole_0(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_58,negated_conjecture,
    ( k1_tarski(esk3_0) = k6_domain_1(u1_struct_0(esk2_0),esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),X1),esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_60,negated_conjecture,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_27]),c_0_49]),c_0_50]),c_0_46])]),c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),k6_domain_1(u1_struct_0(esk2_0),esk3_0)) = k6_waybel_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_27]),c_0_52]),c_0_53]),c_0_54]),c_0_24])])).

cnf(c_0_62,negated_conjecture,
    ( ~ v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k6_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_27]),c_0_24])]),c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])).

fof(c_0_67,plain,(
    ! [X21,X22] :
      ( ( ~ v1_xboole_0(k6_waybel_0(X21,X22))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21)) )
      & ( v2_waybel_0(k6_waybel_0(X21,X22),X21)
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_waybel_0])])])])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(k6_waybel_0(esk2_0,esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k6_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(k6_waybel_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_54]),c_0_24]),c_0_27])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:53:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.12/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t27_waybel_9, conjecture, ![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X3),X1,X1))=>v4_pre_topc(k6_waybel_0(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_waybel_9)).
% 0.12/0.38  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.12/0.38  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.12/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.38  fof(dt_k4_waybel_1, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((v1_funct_1(k4_waybel_1(X1,X2))&v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1)))&m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 0.12/0.38  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.12/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.12/0.38  fof(d12_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X4,X2)=>v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 0.12/0.38  fof(t10_pcomps_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v8_pre_topc(X1)=>v4_pre_topc(k6_domain_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_pcomps_1)).
% 0.12/0.38  fof(t7_waybel_9, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_domain_1(u1_struct_0(X1),X2))=k6_waybel_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_waybel_9)).
% 0.12/0.38  fof(dt_k6_waybel_0, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_waybel_0)).
% 0.12/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.12/0.38  fof(fc9_waybel_0, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>(~(v1_xboole_0(k6_waybel_0(X1,X2)))&v2_waybel_0(k6_waybel_0(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_waybel_0)).
% 0.12/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X3),X1,X1))=>v4_pre_topc(k6_waybel_0(X1,X2),X1))))), inference(assume_negation,[status(cth)],[t27_waybel_9])).
% 0.12/0.38  fof(c_0_14, plain, ![X18]:(~l1_orders_2(X18)|(~v1_lattice3(X18)|~v2_struct_0(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.12/0.38  fof(c_0_15, negated_conjecture, ![X32]:((((((((v2_pre_topc(esk2_0)&v8_pre_topc(esk2_0))&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&v1_lattice3(esk2_0))&v2_lattice3(esk2_0))&l1_waybel_9(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((~m1_subset_1(X32,u1_struct_0(esk2_0))|v5_pre_topc(k4_waybel_1(esk2_0,X32),esk2_0,esk2_0))&~v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.12/0.38  fof(c_0_16, plain, ![X25]:((l1_pre_topc(X25)|~l1_waybel_9(X25))&(l1_orders_2(X25)|~l1_waybel_9(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.12/0.38  cnf(c_0_17, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_19, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (l1_waybel_9(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  fof(c_0_21, plain, ![X9, X10]:(~m1_subset_1(X9,X10)|(v1_xboole_0(X10)|r2_hidden(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.38  fof(c_0_22, plain, ![X23, X24]:(((v1_funct_1(k4_waybel_1(X23,X24))|(v2_struct_0(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,u1_struct_0(X23))))&(v1_funct_2(k4_waybel_1(X23,X24),u1_struct_0(X23),u1_struct_0(X23))|(v2_struct_0(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,u1_struct_0(X23)))))&(m1_subset_1(k4_waybel_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))|(v2_struct_0(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,u1_struct_0(X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_1])])])])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)|~l1_orders_2(esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (l1_orders_2(esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.38  fof(c_0_25, plain, ![X5, X6]:(~r2_hidden(X5,X6)|m1_subset_1(k1_tarski(X5),k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.12/0.38  cnf(c_0_26, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  fof(c_0_28, plain, ![X16, X17]:(v1_xboole_0(X16)|~m1_subset_1(X17,X16)|k6_domain_1(X16,X17)=k1_tarski(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.12/0.38  fof(c_0_29, plain, ![X11, X12, X13, X14]:((~v5_pre_topc(X13,X11,X12)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(~v4_pre_topc(X14,X12)|v4_pre_topc(k8_relset_1(u1_struct_0(X11),u1_struct_0(X12),X13,X14),X11)))|(~v1_funct_1(X13)|~v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12)))))|~l1_pre_topc(X12)|~l1_pre_topc(X11))&((m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v5_pre_topc(X13,X11,X12)|(~v1_funct_1(X13)|~v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12)))))|~l1_pre_topc(X12)|~l1_pre_topc(X11))&((v4_pre_topc(esk1_3(X11,X12,X13),X12)|v5_pre_topc(X13,X11,X12)|(~v1_funct_1(X13)|~v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12)))))|~l1_pre_topc(X12)|~l1_pre_topc(X11))&(~v4_pre_topc(k8_relset_1(u1_struct_0(X11),u1_struct_0(X12),X13,esk1_3(X11,X12,X13)),X11)|v5_pre_topc(X13,X11,X12)|(~v1_funct_1(X13)|~v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12)))))|~l1_pre_topc(X12)|~l1_pre_topc(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).
% 0.12/0.38  cnf(c_0_30, plain, (v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk2_0,X1),esk2_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_33, plain, (v1_funct_1(k4_waybel_1(X1,X2))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_34, plain, (l1_pre_topc(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_35, plain, (m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  fof(c_0_36, plain, ![X26, X27]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(~m1_subset_1(X27,u1_struct_0(X26))|(~v8_pre_topc(X26)|v4_pre_topc(k6_domain_1(u1_struct_0(X26),X27),X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_pcomps_1])])])])).
% 0.12/0.38  fof(c_0_37, plain, ![X28, X29]:(~v3_orders_2(X28)|~v5_orders_2(X28)|~v2_lattice3(X28)|~l1_orders_2(X28)|(~m1_subset_1(X29,u1_struct_0(X28))|k8_relset_1(u1_struct_0(X28),u1_struct_0(X28),k4_waybel_1(X28,X29),k6_domain_1(u1_struct_0(X28),X29))=k6_waybel_0(X28,X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_waybel_9])])])).
% 0.12/0.38  fof(c_0_38, plain, ![X19, X20]:(v2_struct_0(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|m1_subset_1(k6_waybel_0(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_waybel_0])])])).
% 0.12/0.38  cnf(c_0_39, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.38  cnf(c_0_41, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_42, plain, (v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v4_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (v1_funct_2(k4_waybel_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_27]), c_0_24])]), c_0_31])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk2_0,esk3_0),esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_27])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (v1_funct_1(k4_waybel_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_27]), c_0_24])]), c_0_31])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_20])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (m1_subset_1(k4_waybel_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_24])]), c_0_31])).
% 0.12/0.38  cnf(c_0_48, plain, (v2_struct_0(X1)|v4_pre_topc(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v8_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (v8_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_51, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),k6_domain_1(u1_struct_0(X1),X2))=k6_waybel_0(X1,X2)|~v3_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (v2_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  fof(c_0_55, plain, ![X7, X8]:(~v1_xboole_0(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.12/0.38  cnf(c_0_56, plain, (v2_struct_0(X1)|m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.38  cnf(c_0_57, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (k1_tarski(esk3_0)=k6_domain_1(u1_struct_0(esk2_0),esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),X1),esk2_0)|~v4_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (v4_pre_topc(k6_domain_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_27]), c_0_49]), c_0_50]), c_0_46])]), c_0_31])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk3_0),k6_domain_1(u1_struct_0(esk2_0),esk3_0))=k6_waybel_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_27]), c_0_52]), c_0_53]), c_0_54]), c_0_24])])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (~v4_pre_topc(k6_waybel_0(esk2_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_63, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (m1_subset_1(k6_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_27]), c_0_24])]), c_0_31])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (~m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])).
% 0.12/0.38  fof(c_0_67, plain, ![X21, X22]:((~v1_xboole_0(k6_waybel_0(X21,X22))|(v2_struct_0(X21)|~v3_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,u1_struct_0(X21))))&(v2_waybel_0(k6_waybel_0(X21,X22),X21)|(v2_struct_0(X21)|~v3_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,u1_struct_0(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_waybel_0])])])])).
% 0.12/0.38  cnf(c_0_68, negated_conjecture, (v1_xboole_0(k6_waybel_0(esk2_0,esk3_0))|~v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[c_0_65, c_0_66])).
% 0.12/0.38  cnf(c_0_70, plain, (v2_struct_0(X1)|~v1_xboole_0(k6_waybel_0(X1,X2))|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (v1_xboole_0(k6_waybel_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])])).
% 0.12/0.38  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_54]), c_0_24]), c_0_27])]), c_0_31]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 73
% 0.12/0.38  # Proof object clause steps            : 46
% 0.12/0.38  # Proof object formula steps           : 27
% 0.12/0.38  # Proof object conjectures             : 34
% 0.12/0.38  # Proof object clause conjectures      : 31
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 25
% 0.12/0.38  # Proof object initial formulas used   : 13
% 0.12/0.38  # Proof object generating inferences   : 18
% 0.12/0.38  # Proof object simplifying inferences  : 39
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 13
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 30
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 30
% 0.12/0.38  # Processed clauses                    : 98
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 2
% 0.12/0.38  # ...remaining for further processing  : 96
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 10
% 0.12/0.38  # Generated clauses                    : 59
% 0.12/0.38  # ...of the previous two non-trivial   : 51
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 58
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 55
% 0.12/0.38  #    Positive orientable unit clauses  : 21
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 3
% 0.12/0.38  #    Non-unit-clauses                  : 31
% 0.12/0.38  # Current number of unprocessed clauses: 13
% 0.12/0.38  # ...number of literals in the above   : 40
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 41
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 997
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 365
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.12/0.38  # Unit Clause-clause subsumption calls : 42
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 2
% 0.12/0.38  # BW rewrite match successes           : 2
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 4481
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.035 s
% 0.12/0.38  # System time              : 0.002 s
% 0.12/0.38  # Total time               : 0.038 s
% 0.12/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
