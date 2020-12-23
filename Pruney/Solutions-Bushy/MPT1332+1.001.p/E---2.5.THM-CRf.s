%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1332+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:08 EST 2020

% Result     : Theorem 10.64s
% Output     : CNFRefutation 10.64s
% Verified   : 
% Statistics : Number of formulae       :  154 (27285 expanded)
%              Number of clauses        :  123 (10507 expanded)
%              Number of leaves         :   15 (6790 expanded)
%              Depth                    :   40
%              Number of atoms          :  503 (165784 expanded)
%              Number of equality atoms :  159 (32781 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_tops_2,conjecture,(
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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

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

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t55_tops_2])).

fof(c_0_16,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k8_relset_1(X27,X28,X29,X30) = k10_relat_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_17,negated_conjecture,(
    ! [X45] :
      ( l1_pre_topc(esk2_0)
      & l1_pre_topc(esk3_0)
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
      & ( k2_struct_0(esk3_0) != k1_xboole_0
        | k2_struct_0(esk2_0) = k1_xboole_0 )
      & ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) )
      & ( v3_pre_topc(esk5_0,esk3_0)
        | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0),esk2_0)
        | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) )
      & ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v3_pre_topc(X45,esk3_0)
        | v3_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X45),esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).

fof(c_0_18,plain,(
    ! [X38,X39,X40] :
      ( ( k2_struct_0(X39) = k1_xboole_0
        | k8_relset_1(u1_struct_0(X38),u1_struct_0(X39),X40,k2_struct_0(X39)) = k2_struct_0(X38)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))
        | ~ l1_struct_0(X39)
        | ~ l1_struct_0(X38) )
      & ( k2_struct_0(X38) != k1_xboole_0
        | k8_relset_1(u1_struct_0(X38),u1_struct_0(X39),X40,k2_struct_0(X39)) = k2_struct_0(X38)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))
        | ~ l1_struct_0(X39)
        | ~ l1_struct_0(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_tops_2])])])])).

cnf(c_0_19,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k2_struct_0(X1) = k1_xboole_0
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k2_struct_0(X1)) = k2_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1) = k10_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | l1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_26,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | k10_relat_1(X33,k6_subset_1(X31,X32)) = k6_subset_1(k10_relat_1(X33,X31),k10_relat_1(X33,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_27,plain,(
    ! [X25,X26] : k6_subset_1(X25,X26) = k4_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_28,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_struct_0(esk3_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(esk3_0) = k1_xboole_0
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_29,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_31,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_32,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_struct_0(esk3_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(esk3_0) = k1_xboole_0
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X13] :
      ( ~ l1_struct_0(X13)
      | k2_struct_0(X13) = u1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_38,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_struct_0(esk3_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_35])])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_41,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk2_0),k10_relat_1(esk4_0,X1)) = k10_relat_1(esk4_0,k4_xboole_0(k2_struct_0(esk3_0),X1))
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_24]),c_0_40])])).

cnf(c_0_43,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_29])).

fof(c_0_44,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | m1_subset_1(k8_relset_1(X18,X19,X20,X21),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_45,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | k3_subset_1(X14,X15) = k4_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_46,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(k2_struct_0(esk3_0),k2_struct_0(esk3_0))) = k4_xboole_0(k2_struct_0(esk2_0),k2_struct_0(esk2_0))
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(k2_struct_0(esk3_0),X1)) = k4_xboole_0(u1_struct_0(esk2_0),k10_relat_1(esk4_0,X1))
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_30])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_49,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k3_subset_1(X23,k3_subset_1(X23,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_50,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk2_0),k10_relat_1(esk4_0,k2_struct_0(esk3_0))) = k4_xboole_0(k2_struct_0(esk2_0),k2_struct_0(esk2_0))
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k10_relat_1(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_22]),c_0_20])])).

cnf(c_0_53,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2)) = k2_struct_0(X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k10_relat_1(esk4_0,k2_struct_0(esk3_0))) = k4_xboole_0(k2_struct_0(esk2_0),k2_struct_0(esk2_0))
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

fof(c_0_56,plain,(
    ! [X16,X17] : m1_subset_1(k6_subset_1(X16,X17),k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

cnf(c_0_57,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_struct_0(esk3_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_53]),c_0_23]),c_0_24]),c_0_20])])).

cnf(c_0_58,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k4_xboole_0(k2_struct_0(esk2_0),k2_struct_0(esk2_0))) = k10_relat_1(esk4_0,k2_struct_0(esk3_0))
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_52])])).

cnf(c_0_59,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k4_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))) = k10_relat_1(esk4_0,k2_struct_0(esk3_0))
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_43]),c_0_30])])).

cnf(c_0_62,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_33])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_43]),c_0_30])])).

cnf(c_0_64,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k10_relat_1(esk4_0,k2_struct_0(esk3_0))) = k4_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_61]),c_0_62])])).

cnf(c_0_65,negated_conjecture,
    ( k2_struct_0(esk2_0) = k1_xboole_0
    | k2_struct_0(esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_66,negated_conjecture,
    ( k2_struct_0(esk3_0) = k1_xboole_0
    | m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_39])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_29]),c_0_30])])).

cnf(c_0_68,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X2)) = k2_struct_0(X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0)) = k4_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_39])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | k2_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_43]),c_0_30])])).

cnf(c_0_71,negated_conjecture,
    ( k2_struct_0(esk3_0) = k1_xboole_0
    | m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_43]),c_0_30])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_29]),c_0_35])])).

cnf(c_0_73,negated_conjecture,
    ( k10_relat_1(esk4_0,u1_struct_0(esk3_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_68]),c_0_23]),c_0_24]),c_0_35]),c_0_20])])).

cnf(c_0_74,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k4_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))) = k2_struct_0(esk2_0)
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_69]),c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk2_0),k10_relat_1(esk4_0,X1)) = k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1))
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_73]),c_0_24]),c_0_40])])).

cnf(c_0_77,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))) = k2_struct_0(esk2_0)
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_50]),c_0_75])])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk2_0),k2_struct_0(esk2_0)) = k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0)
    | k2_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_77]),c_0_75])])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk2_0),k10_relat_1(esk4_0,X1)) = k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_43]),c_0_30])])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_43]),c_0_35])])).

cnf(c_0_82,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0))) = k4_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | k2_struct_0(esk3_0) = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0))) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | k2_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_65])).

cnf(c_0_84,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1)) = k4_xboole_0(k1_xboole_0,k10_relat_1(esk4_0,X1))
    | k2_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_65])).

cnf(c_0_85,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1)) = k3_subset_1(u1_struct_0(esk2_0),k10_relat_1(esk4_0,X1))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_80]),c_0_52])])).

cnf(c_0_86,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1)) = k4_xboole_0(k1_xboole_0,k10_relat_1(esk4_0,X1))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0))) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_81]),c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k10_relat_1(esk4_0,X1)) = k3_subset_1(u1_struct_0(esk2_0),k10_relat_1(esk4_0,X1))
    | k2_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k10_relat_1(esk4_0,X1)) = k3_subset_1(u1_struct_0(esk2_0),k10_relat_1(esk4_0,X1))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_85]),c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k10_relat_1(esk4_0,u1_struct_0(esk3_0))) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k2_struct_0(esk2_0)) = k3_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0))
    | k2_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_73]),c_0_65])).

cnf(c_0_92,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k10_relat_1(esk4_0,u1_struct_0(esk3_0))) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k10_relat_1(esk4_0,X1),k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_81])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k2_struct_0(esk2_0)) = k3_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_39]),c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(esk3_0) != k1_xboole_0
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_73])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_57])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk2_0),k2_struct_0(esk2_0)) = k3_subset_1(u1_struct_0(esk2_0),k10_relat_1(esk4_0,u1_struct_0(esk3_0)))
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_43]),c_0_35])])).

cnf(c_0_98,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,u1_struct_0(esk2_0)) = k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_43]),c_0_30])])).

cnf(c_0_99,negated_conjecture,
    ( k3_subset_1(k1_xboole_0,k2_struct_0(esk2_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(esk3_0) != k1_xboole_0
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_81])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_43]),c_0_30])]),c_0_81])).

cnf(c_0_101,negated_conjecture,
    ( k3_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0)) = k3_subset_1(u1_struct_0(esk2_0),k10_relat_1(esk4_0,u1_struct_0(esk3_0)))
    | u1_struct_0(esk3_0) = k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_subset_1(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_81])).

cnf(c_0_103,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_subset_1(k1_xboole_0,u1_struct_0(esk2_0))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_43]),c_0_30])]),c_0_81])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_29]),c_0_30])])).

cnf(c_0_105,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k10_relat_1(esk4_0,u1_struct_0(esk3_0))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_92]),c_0_52])])).

cnf(c_0_106,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k10_relat_1(esk4_0,u1_struct_0(esk3_0))) = k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_43]),c_0_75]),c_0_30])])).

cnf(c_0_107,negated_conjecture,
    ( k3_subset_1(k1_xboole_0,u1_struct_0(esk2_0)) = k3_subset_1(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_29]),c_0_35])])).

cnf(c_0_109,negated_conjecture,
    ( k3_subset_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k10_relat_1(esk4_0,u1_struct_0(esk3_0))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_81])).

cnf(c_0_110,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))) = k10_relat_1(esk4_0,u1_struct_0(esk3_0))
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_106]),c_0_52])])).

cnf(c_0_111,plain,
    ( k3_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3)) = k10_relat_1(X1,k4_xboole_0(X2,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k10_relat_1(X1,X3),k1_zfmisc_1(k10_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_38])).

cnf(c_0_112,negated_conjecture,
    ( k3_subset_1(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_107]),c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( k3_subset_1(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) = k10_relat_1(esk4_0,u1_struct_0(esk3_0))
    | u1_struct_0(esk3_0) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_102])).

cnf(c_0_114,negated_conjecture,
    ( k10_relat_1(esk4_0,u1_struct_0(esk3_0)) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_110]),c_0_75])])).

fof(c_0_115,plain,(
    ! [X34,X35] :
      ( ( ~ v4_pre_topc(X35,X34)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X34),X35),X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X34),X35),X34)
        | v4_pre_topc(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_116,plain,
    ( k3_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,k4_xboole_0(X2,X3))) = k10_relat_1(X1,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k10_relat_1(X1,X3),k1_zfmisc_1(k10_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_111])).

cnf(c_0_117,negated_conjecture,
    ( k10_relat_1(esk4_0,u1_struct_0(esk3_0)) = u1_struct_0(esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])).

fof(c_0_118,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ v5_pre_topc(X10,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ v4_pre_topc(X11,X9)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10,X11),X8)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk1_3(X8,X9,X10),k1_zfmisc_1(u1_struct_0(X9)))
        | v5_pre_topc(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( v4_pre_topc(esk1_3(X8,X9,X10),X9)
        | v5_pre_topc(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X8),u1_struct_0(X9),X10,esk1_3(X8,X9,X10)),X8)
        | v5_pre_topc(X10,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_119,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_120,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1))) = k10_relat_1(esk4_0,X1)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_24]),c_0_40]),c_0_52])])).

cnf(c_0_121,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( v3_pre_topc(k10_relat_1(esk4_0,X1),esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v4_pre_topc(k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_30]),c_0_52])])).

cnf(c_0_123,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk4_0,X1),esk2_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_22]),c_0_23]),c_0_24]),c_0_35]),c_0_30]),c_0_20])])).

cnf(c_0_124,negated_conjecture,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0),esk2_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_125,negated_conjecture,
    ( v3_pre_topc(k10_relat_1(esk4_0,X1),esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(esk3_0),X1),esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_62])])).

cnf(c_0_126,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | v3_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v3_pre_topc(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_127,negated_conjecture,
    ( ~ v3_pre_topc(k10_relat_1(esk4_0,esk5_0),esk2_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_124,c_0_22])).

cnf(c_0_128,negated_conjecture,
    ( v3_pre_topc(k10_relat_1(esk4_0,X1),esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(esk3_0),X1),esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_125,c_0_50])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_130,plain,(
    ! [X36,X37] :
      ( ( ~ v3_pre_topc(X37,X36)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X36),X37),X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X36),X37),X36)
        | v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

cnf(c_0_131,negated_conjecture,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1)),esk2_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(esk3_0),X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_62])).

cnf(c_0_132,negated_conjecture,
    ( ~ l1_struct_0(esk2_0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk5_0),esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129])).

cnf(c_0_133,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_135,negated_conjecture,
    ( v3_pre_topc(k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1)),esk2_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(esk3_0),X1),esk3_0) ),
    inference(rw,[status(thm)],[c_0_131,c_0_22])).

cnf(c_0_136,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_137,negated_conjecture,
    ( ~ l1_struct_0(esk2_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_35])]),c_0_129]),c_0_134])).

cnf(c_0_138,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_139,negated_conjecture,
    ( v3_pre_topc(k10_relat_1(esk4_0,k3_subset_1(u1_struct_0(esk3_0),X1)),esk2_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_135,c_0_50])).

cnf(c_0_140,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_20]),c_0_23]),c_0_24]),c_0_35]),c_0_30])])).

cnf(c_0_141,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_29]),c_0_30])])).

cnf(c_0_142,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_20]),c_0_23]),c_0_24]),c_0_35]),c_0_30])])).

cnf(c_0_143,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk4_0,X1),esk2_0)
    | ~ v3_pre_topc(k10_relat_1(esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1)),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_120]),c_0_30]),c_0_52])])).

cnf(c_0_144,negated_conjecture,
    ( v3_pre_topc(k10_relat_1(esk4_0,k3_subset_1(u1_struct_0(esk3_0),X1)),esk2_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_119]),c_0_35])])).

cnf(c_0_145,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_146,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[c_0_142,c_0_141])).

cnf(c_0_147,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_148,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk4_0,X1),esk2_0)
    | ~ v3_pre_topc(k10_relat_1(esk4_0,k3_subset_1(u1_struct_0(esk3_0),X1)),esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_143,c_0_50])).

cnf(c_0_149,negated_conjecture,
    ( v3_pre_topc(k10_relat_1(esk4_0,k3_subset_1(u1_struct_0(esk3_0),esk1_3(esk2_0,esk3_0,esk4_0))),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_146])]),c_0_141])).

cnf(c_0_150,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v4_pre_topc(k10_relat_1(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_22]),c_0_23]),c_0_24]),c_0_35]),c_0_30]),c_0_20])])).

cnf(c_0_151,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_145])])).

cnf(c_0_152,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_141])).

cnf(c_0_153,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_29]),c_0_30])]),
    [proof]).

%------------------------------------------------------------------------------
