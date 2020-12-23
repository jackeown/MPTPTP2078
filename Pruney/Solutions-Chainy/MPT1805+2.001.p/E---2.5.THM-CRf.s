%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 967 expanded)
%              Number of clauses        :   53 ( 312 expanded)
%              Number of leaves         :   10 ( 242 expanded)
%              Depth                    :   25
%              Number of atoms          :  439 (6583 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   34 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t121_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))
            & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2)))
            & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2))
            & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_tmap_1)).

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(t49_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( v5_pre_topc(X3,X2,X1)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t119_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_tmap_1)).

fof(fc5_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( ~ v2_struct_0(k8_tmap_1(X1,X2))
        & v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_tmap_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))
              & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2)))
              & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2))
              & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t121_tmap_1])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ( v1_funct_1(k9_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( v1_funct_2(k9_tmap_1(X18,X19),u1_struct_0(X18),u1_struct_0(k8_tmap_1(X18,X19)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( m1_subset_1(k9_tmap_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(k8_tmap_1(X18,X19)))))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0))
      | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
      | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X25,X26,X27,X28] :
      ( ( ~ v5_pre_topc(X27,X26,X25)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | r1_tmap_1(X26,X25,X27,X28)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk1_3(X25,X26,X27),u1_struct_0(X26))
        | v5_pre_topc(X27,X26,X25)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ r1_tmap_1(X26,X25,X27,esk1_3(X25,X26,X27))
        | v5_pre_topc(X27,X26,X25)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

fof(c_0_14,plain,(
    ! [X12,X13,X14,X15] :
      ( ( v1_funct_1(k2_tmap_1(X12,X13,X14,X15))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_struct_0(X15) )
      & ( v1_funct_2(k2_tmap_1(X12,X13,X14,X15),u1_struct_0(X15),u1_struct_0(X13))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_struct_0(X15) )
      & ( m1_subset_1(k2_tmap_1(X12,X13,X14,X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_struct_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_15,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X16,X17] :
      ( ( v1_pre_topc(k8_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) )
      & ( v2_pre_topc(k8_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) )
      & ( l1_pre_topc(k8_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X2))
    | v5_pre_topc(X3,X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_31,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | m1_subset_1(esk1_3(X2,X4,k2_tmap_1(X1,X2,X3,X4)),u1_struct_0(X4))
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28]),c_0_29]),c_0_30]),c_0_35]),c_0_36])]),c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_18])])).

cnf(c_0_39,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_42,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_26])).

fof(c_0_43,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | l1_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_44,plain,(
    ! [X5,X6] :
      ( ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X6,X5)
      | v2_pre_topc(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_45,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_18])])).

cnf(c_0_46,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_48,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | v2_struct_0(X23)
      | ~ m1_pre_topc(X23,X22)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | r1_tmap_1(X23,k8_tmap_1(X22,X23),k2_tmap_1(X22,k8_tmap_1(X22,X23),k9_tmap_1(X22,X23),X23),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t119_tmap_1])])])])).

cnf(c_0_49,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_17]),c_0_18])])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),esk3_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)),u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_55,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,esk1_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | r1_tmap_1(esk3_0,k8_tmap_1(X1,esk3_0),k2_tmap_1(X1,k8_tmap_1(X1,esk3_0),k9_tmap_1(X1,esk3_0),esk3_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),esk3_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_52])).

cnf(c_0_57,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),esk1_3(X2,X4,k2_tmap_1(X1,X2,X3,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | r1_tmap_1(esk3_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),esk3_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_28]),c_0_29]),c_0_30]),c_0_35]),c_0_50]),c_0_36]),c_0_51])]),c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_26]),c_0_18])])).

cnf(c_0_61,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_41]),c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_26]),c_0_18])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_64,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_26]),c_0_50])])).

cnf(c_0_65,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_25]),c_0_28]),c_0_29]),c_0_30])]),c_0_41])).

cnf(c_0_66,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_26]),c_0_35])])).

fof(c_0_67,plain,(
    ! [X20,X21] :
      ( ( ~ v2_struct_0(k8_tmap_1(X20,X21))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_pre_topc(X21,X20) )
      & ( v1_pre_topc(k8_tmap_1(X20,X21))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_pre_topc(X21,X20) )
      & ( v2_pre_topc(k8_tmap_1(X20,X21))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_pre_topc(X21,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_tmap_1])])])])).

cnf(c_0_68,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_34])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_26]),c_0_35])])).

cnf(c_0_71,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_26]),c_0_18])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_26]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t121_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(((v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))&v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2)))&m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_tmap_1)).
% 0.20/0.39  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.20/0.39  fof(t49_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(v5_pre_topc(X3,X2,X1)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>r1_tmap_1(X2,X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tmap_1)).
% 0.20/0.39  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.20/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.39  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.20/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.39  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.39  fof(t119_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_tmap_1)).
% 0.20/0.39  fof(fc5_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((~(v2_struct_0(k8_tmap_1(X1,X2)))&v1_pre_topc(k8_tmap_1(X1,X2)))&v2_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_tmap_1)).
% 0.20/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(((v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))&v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2)))&m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))))))), inference(assume_negation,[status(cth)],[t121_tmap_1])).
% 0.20/0.39  fof(c_0_11, plain, ![X18, X19]:(((v1_funct_1(k9_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))&(v1_funct_2(k9_tmap_1(X18,X19),u1_struct_0(X18),u1_struct_0(k8_tmap_1(X18,X19)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18))))&(m1_subset_1(k9_tmap_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(k8_tmap_1(X18,X19)))))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.20/0.39  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(~v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0))|~v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))|~v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.20/0.39  fof(c_0_13, plain, ![X25, X26, X27, X28]:((~v5_pre_topc(X27,X26,X25)|(~m1_subset_1(X28,u1_struct_0(X26))|r1_tmap_1(X26,X25,X27,X28))|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25)))))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&((m1_subset_1(esk1_3(X25,X26,X27),u1_struct_0(X26))|v5_pre_topc(X27,X26,X25)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25)))))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(~r1_tmap_1(X26,X25,X27,esk1_3(X25,X26,X27))|v5_pre_topc(X27,X26,X25)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25)))))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).
% 0.20/0.39  fof(c_0_14, plain, ![X12, X13, X14, X15]:(((v1_funct_1(k2_tmap_1(X12,X13,X14,X15))|(~l1_struct_0(X12)|~l1_struct_0(X13)|~v1_funct_1(X14)|~v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))|~l1_struct_0(X15)))&(v1_funct_2(k2_tmap_1(X12,X13,X14,X15),u1_struct_0(X15),u1_struct_0(X13))|(~l1_struct_0(X12)|~l1_struct_0(X13)|~v1_funct_1(X14)|~v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))|~l1_struct_0(X15))))&(m1_subset_1(k2_tmap_1(X12,X13,X14,X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))|(~l1_struct_0(X12)|~l1_struct_0(X13)|~v1_funct_1(X14)|~v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))|~l1_struct_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.20/0.39  fof(c_0_15, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.39  cnf(c_0_16, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_21, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_22, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  fof(c_0_23, plain, ![X16, X17]:(((v1_pre_topc(k8_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_pre_topc(X17,X16)))&(v2_pre_topc(k8_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_pre_topc(X17,X16))))&(l1_pre_topc(k8_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_pre_topc(X17,X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_24, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X2))|v5_pre_topc(X3,X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_25, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_26, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_27, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (v1_funct_1(k9_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.39  cnf(c_0_31, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_32, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_33, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|m1_subset_1(esk1_3(X2,X4,k2_tmap_1(X1,X2,X3,X4)),u1_struct_0(X4))|v2_struct_0(X2)|v2_struct_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~v1_funct_1(X3)|~l1_struct_0(X1)|~l1_pre_topc(X4)|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_26])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28]), c_0_29]), c_0_30]), c_0_35]), c_0_36])]), c_0_26])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_18])])).
% 0.20/0.39  cnf(c_0_39, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_26]), c_0_35])])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_28]), c_0_29]), c_0_30])])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_26])).
% 0.20/0.39  fof(c_0_43, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|l1_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.39  fof(c_0_44, plain, ![X5, X6]:(~v2_pre_topc(X5)|~l1_pre_topc(X5)|(~m1_pre_topc(X6,X5)|v2_pre_topc(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_18])])).
% 0.20/0.39  cnf(c_0_46, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_47, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  fof(c_0_48, plain, ![X22, X23, X24]:(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(v2_struct_0(X23)|~m1_pre_topc(X23,X22)|(~m1_subset_1(X24,u1_struct_0(X23))|r1_tmap_1(X23,k8_tmap_1(X22,X23),k2_tmap_1(X22,k8_tmap_1(X22,X23),k9_tmap_1(X22,X23),X23),X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t119_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_26]), c_0_35])])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_17]), c_0_18])])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_53, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),esk3_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)),u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])]), c_0_52])).
% 0.20/0.39  cnf(c_0_55, plain, (v5_pre_topc(X3,X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,X3,esk1_3(X2,X1,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|r1_tmap_1(esk3_0,k8_tmap_1(X1,esk3_0),k2_tmap_1(X1,k8_tmap_1(X1,esk3_0),k9_tmap_1(X1,esk3_0),esk3_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),esk3_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_52])).
% 0.20/0.39  cnf(c_0_57, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|v2_struct_0(X4)|v2_struct_0(X2)|~r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),esk1_3(X2,X4,k2_tmap_1(X1,X2,X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~v1_funct_1(X3)|~l1_struct_0(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X4)|~v2_pre_topc(X2)|~v2_pre_topc(X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_25]), c_0_26]), c_0_26])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|r1_tmap_1(esk3_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),esk3_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))|~v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_28]), c_0_29]), c_0_30]), c_0_35]), c_0_50]), c_0_36]), c_0_51])]), c_0_52])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))|~v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_26]), c_0_18])])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_41]), c_0_34])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_26]), c_0_18])])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (~v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0))|~v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))|~v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_26]), c_0_50])])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_25]), c_0_28]), c_0_29]), c_0_30])]), c_0_41])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_26]), c_0_35])])).
% 0.20/0.39  fof(c_0_67, plain, ![X20, X21]:(((~v2_struct_0(k8_tmap_1(X20,X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_pre_topc(X21,X20)))&(v1_pre_topc(k8_tmap_1(X20,X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_pre_topc(X21,X20))))&(v2_pre_topc(k8_tmap_1(X20,X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_pre_topc(X21,X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_34])).
% 0.20/0.39  cnf(c_0_69, plain, (v2_struct_0(X1)|~v2_struct_0(k8_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_26]), c_0_35])])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_26]), c_0_18])])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_26]), c_0_50])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 74
% 0.20/0.39  # Proof object clause steps            : 53
% 0.20/0.39  # Proof object formula steps           : 21
% 0.20/0.39  # Proof object conjectures             : 39
% 0.20/0.39  # Proof object clause conjectures      : 36
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 21
% 0.20/0.39  # Proof object initial formulas used   : 10
% 0.20/0.39  # Proof object generating inferences   : 32
% 0.20/0.39  # Proof object simplifying inferences  : 94
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 12
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 27
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 27
% 0.20/0.39  # Processed clauses                    : 99
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 2
% 0.20/0.39  # ...remaining for further processing  : 97
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 18
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 53
% 0.20/0.39  # ...of the previous two non-trivial   : 51
% 0.20/0.39  # Contextual simplify-reflections      : 20
% 0.20/0.39  # Paramodulations                      : 53
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
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
% 0.20/0.39  # Current number of processed clauses  : 54
% 0.20/0.39  #    Positive orientable unit clauses  : 11
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 40
% 0.20/0.39  # Current number of unprocessed clauses: 4
% 0.20/0.39  # ...number of literals in the above   : 46
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 43
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2021
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 201
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 40
% 0.20/0.39  # Unit Clause-clause subsumption calls : 20
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 0
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 7307
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.040 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.044 s
% 0.20/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
