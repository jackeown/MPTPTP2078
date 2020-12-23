%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1804+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 832 expanded)
%              Number of clauses        :   49 ( 269 expanded)
%              Number of leaves         :   10 ( 207 expanded)
%              Depth                    :   13
%              Number of atoms          :  381 (6947 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t120_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_tsep_1(X2,X3)
               => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3))
                  & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))
                  & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X3,k8_tmap_1(X1,X2))
                  & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_tmap_1)).

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

fof(t118_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_tmap_1)).

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

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r1_tsep_1(X2,X3)
                 => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3))
                    & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))
                    & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X3,k8_tmap_1(X1,X2))
                    & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t120_tmap_1])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ( v1_funct_1(k9_tmap_1(X20,X21))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_pre_topc(X21,X20) )
      & ( v1_funct_2(k9_tmap_1(X20,X21),u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_pre_topc(X21,X20) )
      & ( m1_subset_1(k9_tmap_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_pre_topc(X21,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & r1_tsep_1(esk4_0,esk5_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0))
      | ~ v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),esk5_0,k8_tmap_1(esk3_0,esk4_0))
      | ~ m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X14,X15,X16,X17] :
      ( ( v1_funct_1(k2_tmap_1(X14,X15,X16,X17))
        | ~ l1_struct_0(X14)
        | ~ l1_struct_0(X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_struct_0(X17) )
      & ( v1_funct_2(k2_tmap_1(X14,X15,X16,X17),u1_struct_0(X17),u1_struct_0(X15))
        | ~ l1_struct_0(X14)
        | ~ l1_struct_0(X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_struct_0(X17) )
      & ( m1_subset_1(k2_tmap_1(X14,X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X15))))
        | ~ l1_struct_0(X14)
        | ~ l1_struct_0(X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_struct_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_14,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

fof(c_0_24,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | l1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_25,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X35,X36,X37,X38] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v2_struct_0(X36)
      | ~ m1_pre_topc(X36,X35)
      | v2_struct_0(X37)
      | ~ m1_pre_topc(X37,X35)
      | ~ r1_tsep_1(X36,X37)
      | ~ m1_subset_1(X38,u1_struct_0(X37))
      | r1_tmap_1(X37,k8_tmap_1(X35,X36),k2_tmap_1(X35,k8_tmap_1(X35,X36),k9_tmap_1(X35,X36),X37),X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t118_tmap_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))
    | ~ l1_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_23]),c_0_26])])).

cnf(c_0_33,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X27,X28] :
      ( ( ~ v2_struct_0(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) )
      & ( v1_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) )
      & ( v2_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_tmap_1])])])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))))
    | ~ l1_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_23]),c_0_26])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17])])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_41,plain,(
    ! [X39,X40,X41,X42] :
      ( ( ~ v5_pre_topc(X41,X40,X39)
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | r1_tmap_1(X40,X39,X41,X42)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X40))
        | v5_pre_topc(X41,X40,X39)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ r1_tmap_1(X40,X39,X41,esk2_3(X39,X40,X41))
        | v5_pre_topc(X41,X40,X39)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))
    | ~ l1_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_17])])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_44,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))))
    | ~ l1_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_17])])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_26])])).

fof(c_0_48,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | v2_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_49,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | l1_pre_topc(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tmap_1(esk5_0,k8_tmap_1(X1,esk4_0),k2_tmap_1(X1,k8_tmap_1(X1,esk4_0),k9_tmap_1(X1,esk4_0),esk5_0),X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_30]),c_0_43])])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_30]),c_0_43])])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_30]),c_0_43])])).

cnf(c_0_58,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( r1_tmap_1(esk5_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X1,k8_tmap_1(esk3_0,esk4_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk2_3(k8_tmap_1(esk3_0,esk4_0),X1,k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1)),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_43])]),c_0_55]),c_0_56]),c_0_57]),c_0_30])).

cnf(c_0_62,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_16]),c_0_17])])).

cnf(c_0_63,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_51]),c_0_17])])).

cnf(c_0_64,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,esk2_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),esk5_0,k8_tmap_1(esk3_0,esk4_0))
    | r1_tmap_1(esk5_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),esk2_3(k8_tmap_1(esk3_0,esk4_0),esk5_0,k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63])]),c_0_39])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),esk5_0,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_54]),c_0_62]),c_0_43]),c_0_63])]),c_0_55]),c_0_39]),c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( ~ l1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_53]),c_0_56]),c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_30]),c_0_63])]),
    [proof]).

%------------------------------------------------------------------------------
