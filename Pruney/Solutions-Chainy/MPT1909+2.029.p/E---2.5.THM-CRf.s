%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:06 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 744 expanded)
%              Number of clauses        :   48 ( 274 expanded)
%              Number of leaves         :   10 ( 185 expanded)
%              Depth                    :   15
%              Number of atoms          :  276 (6357 expanded)
%              Number of equality atoms :   40 ( 780 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d4_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_tex_2(X1,X2)
              <=> u1_struct_0(X3) = k6_domain_1(u1_struct_0(X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & v3_tdlat_3(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_tex_2(esk2_0,esk1_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v3_borsuk_1(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk1_0))
    & esk4_0 = esk5_0
    & k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)) != k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( v1_xboole_0(X13)
      | ~ m1_subset_1(X14,X13)
      | k6_domain_1(X13,X14) = k1_tarski(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ l1_struct_0(X9)
      | ~ v1_xboole_0(u1_struct_0(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_19,negated_conjecture,
    ( k1_tarski(esk4_0) = k6_domain_1(u1_struct_0(esk2_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k1_tarski(esk4_0) = k6_domain_1(u1_struct_0(esk1_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_17])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | l1_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk4_0) = k6_domain_1(u1_struct_0(esk1_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_25,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_26,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk4_0) = k6_domain_1(u1_struct_0(esk1_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_32,plain,(
    ! [X17,X18,X19] :
      ( ( X19 != k1_tex_2(X17,X18)
        | u1_struct_0(X19) = k6_domain_1(u1_struct_0(X17),X18)
        | v2_struct_0(X19)
        | ~ v1_pre_topc(X19)
        | ~ m1_pre_topc(X19,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17) )
      & ( u1_struct_0(X19) != k6_domain_1(u1_struct_0(X17),X18)
        | X19 = k1_tex_2(X17,X18)
        | v2_struct_0(X19)
        | ~ v1_pre_topc(X19)
        | ~ m1_pre_topc(X19,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).

fof(c_0_33,plain,(
    ! [X20,X21] :
      ( ( ~ v2_struct_0(k1_tex_2(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) )
      & ( v1_pre_topc(k1_tex_2(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) )
      & ( m1_pre_topc(k1_tex_2(X20,X21),X20)
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

cnf(c_0_34,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk4_0) = k6_domain_1(u1_struct_0(esk1_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X2),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | X1 != k1_tex_2(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( v1_pre_topc(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk4_0) = k6_domain_1(u1_struct_0(esk1_0),esk4_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_34]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)) != k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( k6_domain_1(u1_struct_0(X1),X2) = u1_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk4_0) = k6_domain_1(u1_struct_0(esk1_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_28])])).

fof(c_0_44,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ v3_tdlat_3(X22)
      | ~ l1_pre_topc(X22)
      | v2_struct_0(X23)
      | ~ v4_tex_2(X23,X22)
      | ~ m1_pre_topc(X23,X22)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X23))
      | ~ v5_pre_topc(X24,X22,X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))
      | ~ v3_borsuk_1(X24,X22,X23)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X22)))
      | X25 != X26
      | k8_relset_1(u1_struct_0(X22),u1_struct_0(X23),X24,X25) = k2_pre_topc(X22,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t76_tex_2])])])])).

fof(c_0_45,plain,(
    ! [X10,X11,X12] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_46,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)) != k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk4_0) = u1_struct_0(k1_tex_2(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_16]),c_0_43]),c_0_31])]),c_0_24])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k6_domain_1(u1_struct_0(esk1_0),esk4_0)) != k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk4_0)) = u1_struct_0(k1_tex_2(esk1_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_17]),c_0_28])]),c_0_35]),c_0_47])).

cnf(c_0_52,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k2_pre_topc(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_borsuk_1(X3,X1,X2)
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v4_tex_2(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( v3_borsuk_1(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_58,negated_conjecture,
    ( v4_tex_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_59,negated_conjecture,
    ( v3_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_61,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | m1_subset_1(u1_struct_0(X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_62,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(k1_tex_2(esk1_0,esk4_0))) != k2_pre_topc(esk1_0,u1_struct_0(k1_tex_2(esk1_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_47]),c_0_47]),c_0_51]),c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) = k2_pre_topc(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_27]),c_0_28])]),c_0_35]),c_0_24])).

cnf(c_0_64,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(esk1_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(u1_struct_0(k1_tex_2(esk1_0,esk4_0)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk2_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16]),c_0_31])]),c_0_24])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t77_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 0.13/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.13/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(d4_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>(X3=k1_tex_2(X1,X2)<=>u1_struct_0(X3)=k6_domain_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 0.13/0.38  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.13/0.38  fof(t76_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 0.13/0.38  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.13/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_borsuk_1(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(X4=X5=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k6_domain_1(u1_struct_0(X2),X4))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X5)))))))))), inference(assume_negation,[status(cth)],[t77_tex_2])).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ((((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&v3_tdlat_3(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v4_tex_2(esk2_0,esk1_0))&m1_pre_topc(esk2_0,esk1_0))&((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&v5_pre_topc(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v3_borsuk_1(esk3_0,esk1_0,esk2_0)&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(esk1_0))&(esk4_0=esk5_0&k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))!=k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk5_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X13, X14]:(v1_xboole_0(X13)|~m1_subset_1(X14,X13)|k6_domain_1(X13,X14)=k1_tarski(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (esk4_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_15, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk1_0))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  fof(c_0_18, plain, ![X9]:(v2_struct_0(X9)|~l1_struct_0(X9)|~v1_xboole_0(u1_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (k1_tarski(esk4_0)=k6_domain_1(u1_struct_0(esk2_0),esk4_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (k1_tarski(esk4_0)=k6_domain_1(u1_struct_0(esk1_0),esk4_0)|v1_xboole_0(u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_15, c_0_17])).
% 0.13/0.38  fof(c_0_21, plain, ![X7, X8]:(~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|l1_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  cnf(c_0_22, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk4_0)=k6_domain_1(u1_struct_0(esk1_0),esk4_0)|v1_xboole_0(u1_struct_0(esk1_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_25, plain, ![X6]:(~l1_pre_topc(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  cnf(c_0_26, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk4_0)=k6_domain_1(u1_struct_0(esk1_0),esk4_0)|v1_xboole_0(u1_struct_0(esk1_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.13/0.38  cnf(c_0_30, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.13/0.38  fof(c_0_32, plain, ![X17, X18, X19]:((X19!=k1_tex_2(X17,X18)|u1_struct_0(X19)=k6_domain_1(u1_struct_0(X17),X18)|(v2_struct_0(X19)|~v1_pre_topc(X19)|~m1_pre_topc(X19,X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~l1_pre_topc(X17)))&(u1_struct_0(X19)!=k6_domain_1(u1_struct_0(X17),X18)|X19=k1_tex_2(X17,X18)|(v2_struct_0(X19)|~v1_pre_topc(X19)|~m1_pre_topc(X19,X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).
% 0.13/0.38  fof(c_0_33, plain, ![X20, X21]:(((~v2_struct_0(k1_tex_2(X20,X21))|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))))&(v1_pre_topc(k1_tex_2(X20,X21))|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20)))))&(m1_pre_topc(k1_tex_2(X20,X21),X20)|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk4_0)=k6_domain_1(u1_struct_0(esk1_0),esk4_0)|v1_xboole_0(u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_36, plain, (u1_struct_0(X1)=k6_domain_1(u1_struct_0(X2),X3)|v2_struct_0(X1)|v2_struct_0(X2)|X1!=k1_tex_2(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_37, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_38, plain, (v1_pre_topc(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_39, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk4_0)=k6_domain_1(u1_struct_0(esk1_0),esk4_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_34]), c_0_35])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))!=k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_42, plain, (k6_domain_1(u1_struct_0(X1),X2)=u1_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk4_0)=k6_domain_1(u1_struct_0(esk1_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_30]), c_0_28])])).
% 0.13/0.38  fof(c_0_44, plain, ![X22, X23, X24, X25, X26]:(v2_struct_0(X22)|~v2_pre_topc(X22)|~v3_tdlat_3(X22)|~l1_pre_topc(X22)|(v2_struct_0(X23)|~v4_tex_2(X23,X22)|~m1_pre_topc(X23,X22)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X23))|~v5_pre_topc(X24,X22,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))|(~v3_borsuk_1(X24,X22,X23)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X22)))|(X25!=X26|k8_relset_1(u1_struct_0(X22),u1_struct_0(X23),X24,X25)=k2_pre_topc(X22,X26)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t76_tex_2])])])])).
% 0.13/0.38  fof(c_0_45, plain, ![X10, X11, X12]:(~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))!=k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk4_0))), inference(rw,[status(thm)],[c_0_41, c_0_14])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (k6_domain_1(u1_struct_0(esk1_0),esk4_0)=u1_struct_0(k1_tex_2(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_16]), c_0_43]), c_0_31])]), c_0_24])).
% 0.13/0.38  cnf(c_0_48, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X5)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~v4_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v5_pre_topc(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v3_borsuk_1(X3,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))|X4!=X5), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_49, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k6_domain_1(u1_struct_0(esk1_0),esk4_0))!=k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk4_0))), inference(rw,[status(thm)],[c_0_46, c_0_43])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk4_0))=u1_struct_0(k1_tex_2(esk1_0,esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_17]), c_0_28])]), c_0_35]), c_0_47])).
% 0.13/0.38  cnf(c_0_52, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k2_pre_topc(X1,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~v3_borsuk_1(X3,X1,X2)|~v5_pre_topc(X3,X1,X2)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v4_tex_2(X2,X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_49])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (v3_borsuk_1(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (v4_tex_2(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (v3_tdlat_3(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_61, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|m1_subset_1(u1_struct_0(X16),k1_zfmisc_1(u1_struct_0(X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(k1_tex_2(esk1_0,esk4_0)))!=k2_pre_topc(esk1_0,u1_struct_0(k1_tex_2(esk1_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_47]), c_0_47]), c_0_51]), c_0_51])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)=k2_pre_topc(esk1_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_27]), c_0_28])]), c_0_35]), c_0_24])).
% 0.13/0.38  cnf(c_0_64, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (~m1_subset_1(u1_struct_0(k1_tex_2(esk1_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (m1_subset_1(u1_struct_0(k1_tex_2(esk1_0,esk4_0)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(k1_tex_2(esk2_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_64, c_0_51])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (m1_pre_topc(k1_tex_2(esk2_0,esk4_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_16]), c_0_31])]), c_0_24])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_31])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 69
% 0.13/0.38  # Proof object clause steps            : 48
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 38
% 0.13/0.38  # Proof object clause conjectures      : 35
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 27
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 15
% 0.13/0.38  # Proof object simplifying inferences  : 47
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 28
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 122
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 6
% 0.13/0.38  # ...remaining for further processing  : 116
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 12
% 0.13/0.38  # Generated clauses                    : 81
% 0.13/0.38  # ...of the previous two non-trivial   : 88
% 0.13/0.38  # Contextual simplify-reflections      : 6
% 0.13/0.38  # Paramodulations                      : 77
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 4
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 72
% 0.13/0.38  #    Positive orientable unit clauses  : 24
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 6
% 0.13/0.38  #    Non-unit-clauses                  : 42
% 0.13/0.38  # Current number of unprocessed clauses: 19
% 0.13/0.38  # ...number of literals in the above   : 95
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 42
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 620
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 184
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.38  # Unit Clause-clause subsumption calls : 11
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4784
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.039 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
