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
% DateTime   : Thu Dec  3 11:21:01 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 (1112 expanded)
%              Number of clauses        :   55 ( 371 expanded)
%              Number of leaves         :   13 ( 273 expanded)
%              Depth                    :   13
%              Number of atoms          :  304 (10868 expanded)
%              Number of equality atoms :   27 (1216 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_tex_2(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & v5_pre_topc(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_borsuk_1(X3,X1,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ( X4 = X5
                         => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

fof(cc18_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tdlat_3(X2)
           => v3_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc18_tex_2)).

fof(cc35_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & v4_tex_2(X2,X1) )
           => ( ~ v2_struct_0(X2)
              & v1_tdlat_3(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc35_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t66_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

fof(t46_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t76_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_tex_2(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & v5_pre_topc(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_borsuk_1(X3,X1,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( X4 = X5
                         => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k2_pre_topc(X1,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_tex_2(X2,X1)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v5_pre_topc(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( v3_borsuk_1(X3,X1,X2)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X2))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( X4 = X5
                           => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tex_2])).

fof(c_0_14,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | ~ v1_tdlat_3(X21)
      | v3_tdlat_3(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc18_tex_2])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & v3_tdlat_3(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v4_tex_2(esk3_0,esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & v5_pre_topc(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & v3_borsuk_1(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk2_0))
    & esk5_0 = esk6_0
    & k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)) != k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ( ~ v2_struct_0(X23)
        | v2_struct_0(X23)
        | ~ v4_tex_2(X23,X22)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22) )
      & ( v1_tdlat_3(X23)
        | v2_struct_0(X23)
        | ~ v4_tex_2(X23,X22)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc35_tex_2])])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v3_tdlat_3(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v4_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X11)
      | l1_pre_topc(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_25,plain,(
    ! [X9,X10] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | v2_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_26,plain,(
    ! [X26] :
      ( ( m1_subset_1(esk1_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ v3_tdlat_3(X26)
        | ~ l1_pre_topc(X26) )
      & ( v3_tex_2(esk1_1(X26),X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ v3_tdlat_3(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_tex_2])])])])])).

cnf(c_0_27,negated_conjecture,
    ( v3_tdlat_3(esk3_0)
    | ~ v1_tdlat_3(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_tdlat_3(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_18]),c_0_19])]),c_0_20]),c_0_23])).

cnf(c_0_29,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_32,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ v1_xboole_0(X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ v3_tex_2(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).

cnf(c_0_33,plain,
    ( v3_tex_2(esk1_1(X1),X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v3_tdlat_3(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_18]),c_0_19])])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_19]),c_0_31])])).

cnf(c_0_37,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v3_tex_2(esk1_1(esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_23])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( v3_tex_2(esk1_1(esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_19]),c_0_31])]),c_0_20])).

fof(c_0_42,plain,(
    ! [X18,X19] :
      ( v1_xboole_0(X18)
      | ~ m1_subset_1(X19,X18)
      | k6_domain_1(X18,X19) = k1_tarski(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_43,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_44,plain,(
    ! [X7,X8] :
      ( ~ v1_xboole_0(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_xboole_0(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_xboole_0(esk1_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_35]),c_0_36])]),c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_34]),c_0_35]),c_0_36])]),c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(esk1_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_xboole_0(esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_41]),c_0_19]),c_0_31])]),c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk1_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_37]),c_0_19]),c_0_31])]),c_0_20])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk1_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( esk5_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk1_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_56,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_46]),c_0_52])).

fof(c_0_59,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ v3_tdlat_3(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ v4_tex_2(X29,X28)
      | ~ m1_pre_topc(X29,X28)
      | ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
      | ~ v5_pre_topc(X30,X28,X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
      | ~ v3_borsuk_1(X30,X28,X29)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X28)))
      | X31 != X32
      | k8_relset_1(u1_struct_0(X28),u1_struct_0(X29),X30,X31) = k2_pre_topc(X28,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t76_tex_2])])])])).

fof(c_0_60,plain,(
    ! [X13,X14,X15] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_61,plain,(
    ! [X16,X17] :
      ( v1_xboole_0(X16)
      | ~ m1_subset_1(X17,X16)
      | m1_subset_1(k6_domain_1(X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_62,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)) != k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( k2_tarski(esk5_0,esk5_0) = k6_domain_1(u1_struct_0(esk3_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k2_pre_topc(X1,X5)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v3_borsuk_1(X3,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | X4 != X5 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0)) != k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_54])).

cnf(c_0_70,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk5_0) = k6_domain_1(u1_struct_0(esk2_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_71,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k2_pre_topc(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_borsuk_1(X3,X1,X2)
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v4_tex_2(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_73,negated_conjecture,
    ( v3_borsuk_1(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_74,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_57]),c_0_58])).

cnf(c_0_78,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k6_domain_1(u1_struct_0(esk2_0),esk5_0)) != k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1) = k2_pre_topc(esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74]),c_0_75]),c_0_76]),c_0_22]),c_0_37]),c_0_18]),c_0_19]),c_0_31])]),c_0_20]),c_0_23])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_77,c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t77_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 0.19/0.38  fof(cc18_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tdlat_3(X2)=>v3_tdlat_3(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc18_tex_2)).
% 0.19/0.38  fof(cc35_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((~(v2_struct_0(X2))&v4_tex_2(X2,X1))=>(~(v2_struct_0(X2))&v1_tdlat_3(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc35_tex_2)).
% 0.19/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.38  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.38  fof(t66_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 0.19/0.38  fof(t46_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 0.19/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.38  fof(t76_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 0.19/0.38  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.19/0.38  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5)))))))))), inference(assume_negation,[status(cth)],[t77_tex_2])).
% 0.19/0.38  fof(c_0_14, plain, ![X20, X21]:(v2_struct_0(X20)|~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|(~v1_tdlat_3(X21)|v3_tdlat_3(X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc18_tex_2])])])])).
% 0.19/0.38  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&v3_tdlat_3(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v4_tex_2(esk3_0,esk2_0))&m1_pre_topc(esk3_0,esk2_0))&((((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&v5_pre_topc(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(v3_borsuk_1(esk4_0,esk2_0,esk3_0)&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(m1_subset_1(esk6_0,u1_struct_0(esk2_0))&(esk5_0=esk6_0&k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))!=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk6_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.19/0.38  fof(c_0_16, plain, ![X22, X23]:((~v2_struct_0(X23)|(v2_struct_0(X23)|~v4_tex_2(X23,X22))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~l1_pre_topc(X22)))&(v1_tdlat_3(X23)|(v2_struct_0(X23)|~v4_tex_2(X23,X22))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc35_tex_2])])])])])).
% 0.19/0.38  cnf(c_0_17, plain, (v2_struct_0(X1)|v3_tdlat_3(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~v1_tdlat_3(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_21, plain, (v1_tdlat_3(X1)|v2_struct_0(X1)|v2_struct_0(X2)|~v4_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (v4_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_24, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_pre_topc(X12,X11)|l1_pre_topc(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.38  fof(c_0_25, plain, ![X9, X10]:(~v2_pre_topc(X9)|~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|v2_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.38  fof(c_0_26, plain, ![X26]:((m1_subset_1(esk1_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~v3_tdlat_3(X26)|~l1_pre_topc(X26)))&(v3_tex_2(esk1_1(X26),X26)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~v3_tdlat_3(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_tex_2])])])])])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (v3_tdlat_3(esk3_0)|~v1_tdlat_3(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_20])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (v1_tdlat_3(esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_18]), c_0_19])]), c_0_20]), c_0_23])).
% 0.19/0.38  cnf(c_0_29, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_30, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_32, plain, ![X24, X25]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~v3_tex_2(X25,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).
% 0.19/0.38  cnf(c_0_33, plain, (v3_tex_2(esk1_1(X1),X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (v3_tdlat_3(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_18]), c_0_19])])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_18]), c_0_19]), c_0_31])])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (v3_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_38, plain, (v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (v3_tex_2(esk1_1(esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), c_0_23])).
% 0.19/0.38  cnf(c_0_40, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (v3_tex_2(esk1_1(esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_37]), c_0_19]), c_0_31])]), c_0_20])).
% 0.19/0.38  fof(c_0_42, plain, ![X18, X19]:(v1_xboole_0(X18)|~m1_subset_1(X19,X18)|k6_domain_1(X18,X19)=k1_tarski(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.38  fof(c_0_43, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  fof(c_0_44, plain, ![X7, X8]:(~v1_xboole_0(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (~m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v1_xboole_0(esk1_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_35]), c_0_36])]), c_0_23])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_34]), c_0_35]), c_0_36])]), c_0_23])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (~m1_subset_1(esk1_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_xboole_0(esk1_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_41]), c_0_19]), c_0_31])]), c_0_20])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk1_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_37]), c_0_19]), c_0_31])]), c_0_20])).
% 0.19/0.38  cnf(c_0_49, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_50, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_51, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk1_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (esk5_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(esk1_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])])).
% 0.19/0.38  cnf(c_0_56, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_46]), c_0_52])).
% 0.19/0.38  fof(c_0_59, plain, ![X28, X29, X30, X31, X32]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~v3_tdlat_3(X28)|~l1_pre_topc(X28)|(v2_struct_0(X29)|~v4_tex_2(X29,X28)|~m1_pre_topc(X29,X28)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~v5_pre_topc(X30,X28,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))|(~v3_borsuk_1(X30,X28,X29)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X28)))|(X31!=X32|k8_relset_1(u1_struct_0(X28),u1_struct_0(X29),X30,X31)=k2_pre_topc(X28,X32)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t76_tex_2])])])])).
% 0.19/0.38  fof(c_0_60, plain, ![X13, X14, X15]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.19/0.38  fof(c_0_61, plain, ![X16, X17]:(v1_xboole_0(X16)|~m1_subset_1(X17,X16)|m1_subset_1(k6_domain_1(X16,X17),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))!=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_48]), c_0_55])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (k2_tarski(esk5_0,esk5_0)=k6_domain_1(u1_struct_0(esk3_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.19/0.38  cnf(c_0_66, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X5)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~v4_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v5_pre_topc(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v3_borsuk_1(X3,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))|X4!=X5), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.38  cnf(c_0_67, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.38  cnf(c_0_68, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk5_0))!=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk5_0))), inference(rw,[status(thm)],[c_0_62, c_0_54])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),esk5_0)=k6_domain_1(u1_struct_0(esk2_0),esk5_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_63]), c_0_64]), c_0_65])).
% 0.19/0.38  cnf(c_0_71, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~v3_borsuk_1(X3,X1,X2)|~v5_pre_topc(X3,X1,X2)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v4_tex_2(X2,X1)|~v3_tdlat_3(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]), c_0_67])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (v3_borsuk_1(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_57]), c_0_58])).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k6_domain_1(u1_struct_0(esk2_0),esk5_0))!=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk5_0))), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)=k2_pre_topc(esk2_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74]), c_0_75]), c_0_76]), c_0_22]), c_0_37]), c_0_18]), c_0_19]), c_0_31])]), c_0_20]), c_0_23])).
% 0.19/0.38  cnf(c_0_80, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_77, c_0_70])).
% 0.19/0.38  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 82
% 0.19/0.38  # Proof object clause steps            : 55
% 0.19/0.38  # Proof object formula steps           : 27
% 0.19/0.38  # Proof object conjectures             : 43
% 0.19/0.38  # Proof object clause conjectures      : 40
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 29
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 17
% 0.19/0.38  # Proof object simplifying inferences  : 70
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 30
% 0.19/0.38  # Removed in clause preprocessing      : 2
% 0.19/0.38  # Initial clauses in saturation        : 28
% 0.19/0.38  # Processed clauses                    : 95
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 4
% 0.19/0.38  # ...remaining for further processing  : 91
% 0.19/0.38  # Other redundant clauses eliminated   : 1
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 6
% 0.19/0.38  # Generated clauses                    : 63
% 0.19/0.38  # ...of the previous two non-trivial   : 65
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 62
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 1
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
% 0.19/0.38  # Current number of processed clauses  : 56
% 0.19/0.38  #    Positive orientable unit clauses  : 25
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 7
% 0.19/0.38  #    Non-unit-clauses                  : 24
% 0.19/0.38  # Current number of unprocessed clauses: 25
% 0.19/0.38  # ...number of literals in the above   : 77
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 35
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 447
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 27
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.38  # Unit Clause-clause subsumption calls : 8
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 6
% 0.19/0.38  # BW rewrite match successes           : 4
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4308
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.036 s
% 0.19/0.38  # System time              : 0.002 s
% 0.19/0.38  # Total time               : 0.038 s
% 0.19/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
