%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t69_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:55 EDT 2019

% Result     : Theorem 278.63s
% Output     : CNFRefutation 278.63s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 302 expanded)
%              Number of clauses        :   53 ( 129 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  296 ( 978 expanded)
%              Number of equality atoms :   33 ( 133 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_compts_1,axiom,(
    ! [X1] : k1_compts_1(X1) = g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1))) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',d8_compts_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',redefinition_k9_setfam_1)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',free_g1_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_k2_subset_1)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_g1_pre_topc)).

fof(dt_k1_compts_1,axiom,(
    ! [X1] : l1_pre_topc(k1_compts_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_k1_compts_1)).

fof(t18_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',t18_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',cc1_tdlat_3)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',abstractness_v1_pre_topc)).

fof(fc4_tex_1,axiom,(
    ! [X1] : v1_tdlat_3(k1_compts_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',fc4_tex_1)).

fof(t69_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => v5_pre_topc(X3,X1,X2) ) )
       => v1_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',t69_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',d12_pre_topc)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',fc3_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',redefinition_k6_partfun1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',redefinition_k8_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_k6_partfun1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',cc1_funct_2)).

fof(fc2_compts_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ~ v2_struct_0(k1_compts_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',fc2_compts_1)).

fof(t171_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',t171_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_l1_pre_topc)).

fof(c_0_21,plain,(
    ! [X20] : k1_compts_1(X20) = g1_pre_topc(X20,k2_subset_1(k9_setfam_1(X20))) ),
    inference(variable_rename,[status(thm)],[d8_compts_1])).

fof(c_0_22,plain,(
    ! [X52] : k9_setfam_1(X52) = k1_zfmisc_1(X52) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_23,plain,(
    ! [X42,X43,X44,X45] :
      ( ( X42 = X44
        | g1_pre_topc(X42,X43) != g1_pre_topc(X44,X45)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))) )
      & ( X43 = X45
        | g1_pre_topc(X42,X43) != g1_pre_topc(X44,X45)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_24,plain,(
    ! [X24] : m1_subset_1(k2_subset_1(X24),k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_25,plain,(
    ! [X21,X22] :
      ( ( v1_pre_topc(g1_pre_topc(X21,X22))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) )
      & ( l1_pre_topc(g1_pre_topc(X21,X22))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_26,plain,(
    ! [X23] : l1_pre_topc(k1_compts_1(X23)) ),
    inference(variable_rename,[status(thm)],[dt_k1_compts_1])).

cnf(c_0_27,plain,
    ( k1_compts_1(X1) = g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X55,X56] :
      ( ( ~ v1_tdlat_3(X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | v4_pre_topc(X56,X55)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55) )
      & ( m1_subset_1(esk7_1(X55),k1_zfmisc_1(u1_struct_0(X55)))
        | v1_tdlat_3(X55)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55) )
      & ( ~ v4_pre_topc(esk7_1(X55),X55)
        | v1_tdlat_3(X55)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).

fof(c_0_30,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | ~ v1_tdlat_3(X14)
      | v2_pre_topc(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | ~ v1_pre_topc(X8)
      | X8 = g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_34,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( l1_pre_topc(k1_compts_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k1_compts_1(X1) = g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_37,plain,(
    ! [X41] : v1_tdlat_3(k1_compts_1(X41)) ),
    inference(variable_rename,[status(thm)],[fc4_tex_1])).

cnf(c_0_38,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( X1 = X2
    | g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))) != g1_pre_topc(X2,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( v1_pre_topc(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_43,plain,
    ( l1_pre_topc(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( v1_tdlat_3(k1_compts_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( ! [X2] :
              ( ( ~ v2_struct_0(X2)
                & v2_pre_topc(X2)
                & l1_pre_topc(X2) )
             => ! [X3] :
                  ( ( v1_funct_1(X3)
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                 => v5_pre_topc(X3,X1,X2) ) )
         => v1_tdlat_3(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t69_tex_2])).

fof(c_0_46,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ v5_pre_topc(X17,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v4_pre_topc(X18,X16)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,X18),X15)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk2_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X16)))
        | v5_pre_topc(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( v4_pre_topc(esk2_3(X15,X16,X17),X16)
        | v5_pre_topc(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,esk2_3(X15,X16,X17)),X15)
        | v5_pre_topc(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_47,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41])]),c_0_42]),c_0_43])])).

cnf(c_0_49,plain,
    ( v1_tdlat_3(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_36])).

fof(c_0_50,negated_conjecture,(
    ! [X6,X7] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & ( v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(esk1_0),u1_struct_0(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X6))))
        | v5_pre_topc(X7,esk1_0,X6) )
      & ~ v1_tdlat_3(esk1_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_45])])])])])).

fof(c_0_51,plain,(
    ! [X40] :
      ( v1_relat_1(k6_relat_1(X40))
      & v1_funct_1(k6_relat_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_52,plain,(
    ! [X47] : k6_partfun1(X47) = k6_relat_1(X47) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_53,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( v4_pre_topc(X1,g1_pre_topc(X2,k2_subset_1(k1_zfmisc_1(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_43])])).

cnf(c_0_55,negated_conjecture,
    ( v2_struct_0(X1)
    | v5_pre_topc(X2,esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( v2_pre_topc(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_49]),c_0_43])])).

fof(c_0_57,plain,(
    ! [X48,X49,X50,X51] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k8_relset_1(X48,X49,X50,X51) = k10_relat_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_58,plain,(
    ! [X25] :
      ( v1_partfun1(k6_partfun1(X25),X25)
      & m1_subset_1(k6_partfun1(X25),k1_zfmisc_1(k2_zfmisc_1(X25,X25))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_59,plain,(
    ! [X11,X12,X13] :
      ( ( v1_funct_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_partfun1(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( v1_funct_2(X13,X11,X12)
        | ~ v1_funct_1(X13)
        | ~ v1_partfun1(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_60,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X1),X2,X3,X4),X1)
    | ~ v5_pre_topc(X3,X1,g1_pre_topc(X2,k2_subset_1(k1_zfmisc_1(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X1),X2)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_48]),c_0_43])]),c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( v5_pre_topc(X1,esk1_0,g1_pre_topc(X2,k2_subset_1(k1_zfmisc_1(X2))))
    | v2_struct_0(g1_pre_topc(X2,k2_subset_1(k1_zfmisc_1(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),X2)))
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),X2)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_43]),c_0_56])])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( v1_funct_1(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_70,plain,(
    ! [X38] :
      ( v1_xboole_0(X38)
      | ~ v2_struct_0(k1_compts_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_compts_1])])])).

cnf(c_0_71,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk1_0),X1,X2,X3),esk1_0)
    | v2_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),X1)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_72,plain,
    ( k8_relset_1(X1,X1,k6_partfun1(X1),X2) = k10_relat_1(k6_partfun1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( v1_funct_2(k6_partfun1(X1),X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_66]),c_0_68]),c_0_69])])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k1_compts_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(esk1_0)),X1),esk1_0)
    | v2_struct_0(g1_pre_topc(u1_struct_0(esk1_0),k2_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_66]),c_0_72]),c_0_73]),c_0_69])])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk7_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_79,plain,(
    ! [X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(X53))
      | k8_relset_1(X53,X53,k6_partfun1(X53),X54) = X54 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[c_0_74,c_0_36])).

cnf(c_0_81,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(esk1_0)),esk7_1(esk1_0)),esk1_0)
    | v2_struct_0(g1_pre_topc(u1_struct_0(esk1_0),k2_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_64]),c_0_77])]),c_0_78])).

cnf(c_0_82,plain,
    ( k8_relset_1(X2,X2,k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(esk1_0)),esk7_1(esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,plain,
    ( k10_relat_1(k6_partfun1(X1),X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_72])).

cnf(c_0_85,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | v4_pre_topc(esk7_1(esk1_0),esk1_0)
    | ~ m1_subset_1(esk7_1(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_86,plain,(
    ! [X39] :
      ( v2_struct_0(X39)
      | ~ l1_struct_0(X39)
      | ~ v1_xboole_0(u1_struct_0(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_87,plain,
    ( v1_tdlat_3(X1)
    | ~ v4_pre_topc(esk7_1(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | v4_pre_topc(esk7_1(esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_76]),c_0_64]),c_0_77])]),c_0_78])).

cnf(c_0_89,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_64]),c_0_77])]),c_0_78])).

cnf(c_0_91,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_92,plain,(
    ! [X32] :
      ( ~ l1_pre_topc(X32)
      | l1_struct_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_93,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_94,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
