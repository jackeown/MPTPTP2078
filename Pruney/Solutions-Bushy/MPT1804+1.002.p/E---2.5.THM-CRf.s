%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1804+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:48 EST 2020

% Result     : Theorem 0.23s
% Output     : CNFRefutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 721 expanded)
%              Number of clauses        :   56 ( 235 expanded)
%              Number of leaves         :   10 ( 181 expanded)
%              Depth                    :   22
%              Number of atoms          :  443 (5993 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   34 (   4 average)
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
    ! [X32,X33,X34,X35] :
      ( ( ~ v5_pre_topc(X34,X33,X32)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | r1_tmap_1(X33,X32,X34,X35)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X33),u1_struct_0(X32))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X32))))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(esk1_3(X32,X33,X34),u1_struct_0(X33))
        | v5_pre_topc(X34,X33,X32)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X33),u1_struct_0(X32))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X32))))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ r1_tmap_1(X33,X32,X34,esk1_3(X32,X33,X34))
        | v5_pre_topc(X34,X33,X32)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X33),u1_struct_0(X32))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X32))))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

fof(c_0_12,plain,(
    ! [X15,X16,X17,X18] :
      ( ( v1_funct_1(k2_tmap_1(X15,X16,X17,X18))
        | ~ l1_struct_0(X15)
        | ~ l1_struct_0(X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_struct_0(X18) )
      & ( v1_funct_2(k2_tmap_1(X15,X16,X17,X18),u1_struct_0(X18),u1_struct_0(X16))
        | ~ l1_struct_0(X15)
        | ~ l1_struct_0(X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_struct_0(X18) )
      & ( m1_subset_1(k2_tmap_1(X15,X16,X17,X18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X16))))
        | ~ l1_struct_0(X15)
        | ~ l1_struct_0(X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_struct_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_13,plain,(
    ! [X23] :
      ( ~ l1_pre_topc(X23)
      | l1_struct_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_14,plain,(
    ! [X21,X22] :
      ( ( v1_funct_1(k9_tmap_1(X21,X22))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X21) )
      & ( v1_funct_2(k9_tmap_1(X21,X22),u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X21) )
      & ( m1_subset_1(k9_tmap_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & r1_tsep_1(esk3_0,esk4_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0))
      | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
      | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_16,plain,(
    ! [X19,X20] :
      ( ( v1_pre_topc(k8_tmap_1(X19,X20))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X20,X19) )
      & ( v2_pre_topc(k8_tmap_1(X19,X20))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X20,X19) )
      & ( l1_pre_topc(k8_tmap_1(X19,X20))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X20,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_17,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | m1_subset_1(esk1_3(X2,X4,k2_tmap_1(X1,X2,X3,X4)),u1_struct_0(X4))
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_37,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | l1_pre_topc(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_38,plain,(
    ! [X5,X6] :
      ( ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X6,X5)
      | v2_pre_topc(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_39,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_40,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_43,plain,(
    ! [X28,X29,X30,X31] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ m1_pre_topc(X29,X28)
      | v2_struct_0(X30)
      | ~ m1_pre_topc(X30,X28)
      | ~ r1_tsep_1(X29,X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | r1_tmap_1(X30,k8_tmap_1(X28,X29),k2_tmap_1(X28,k8_tmap_1(X28,X29),k9_tmap_1(X28,X29),X30),X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t118_tmap_1])])])])).

cnf(c_0_44,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_21]),c_0_24])])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24])])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_24]),c_0_25])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),esk4_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_52,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | r1_tmap_1(esk4_0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),esk4_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),esk4_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | r1_tmap_1(esk4_0,k8_tmap_1(X1,esk3_0),k2_tmap_1(X1,k8_tmap_1(X1,esk3_0),k9_tmap_1(X1,esk3_0),esk4_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),esk4_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_21]),c_0_24])])).

cnf(c_0_59,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),esk1_3(X2,X4,k2_tmap_1(X1,X2,X3,X4)))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),esk4_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_41]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_21]),c_0_45])])).

cnf(c_0_62,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_45]),c_0_36]),c_0_46])]),c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_21]),c_0_35])])).

cnf(c_0_64,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_21]),c_0_24])])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_20]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_67,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_21]),c_0_45])])).

cnf(c_0_68,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_21]),c_0_24])])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_21]),c_0_35])])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_18]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_71,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_21]),c_0_45])])).

fof(c_0_72,plain,(
    ! [X26,X27] :
      ( ( ~ v2_struct_0(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) )
      & ( v1_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) )
      & ( v2_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_tmap_1])])])])).

cnf(c_0_73,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_21]),c_0_24])])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_21]),c_0_35])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),
    [proof]).

%------------------------------------------------------------------------------
