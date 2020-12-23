%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1901+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:01 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 326 expanded)
%              Number of clauses        :   53 ( 139 expanded)
%              Number of leaves         :   21 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  302 (1032 expanded)
%              Number of equality atoms :   33 ( 140 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_compts_1,axiom,(
    ! [X1] : k1_compts_1(X1) = g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_compts_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(dt_k1_compts_1,axiom,(
    ! [X1] : l1_pre_topc(k1_compts_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_compts_1)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(fc4_tex_1,axiom,(
    ! [X1] : v1_tdlat_3(k1_compts_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tex_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tex_2)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(t18_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(t171_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(fc2_compts_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ~ v2_struct_0(k1_compts_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_compts_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_21,plain,(
    ! [X15] : k1_compts_1(X15) = g1_pre_topc(X15,k2_subset_1(k9_setfam_1(X15))) ),
    inference(variable_rename,[status(thm)],[d8_compts_1])).

fof(c_0_22,plain,(
    ! [X35] : k9_setfam_1(X35) = k1_zfmisc_1(X35) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_23,plain,(
    ! [X26,X27,X28,X29] :
      ( ( X26 = X28
        | g1_pre_topc(X26,X27) != g1_pre_topc(X28,X29)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) )
      & ( X27 = X29
        | g1_pre_topc(X26,X27) != g1_pre_topc(X28,X29)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_24,plain,(
    ! [X19] : m1_subset_1(k2_subset_1(X19),k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_25,plain,(
    ! [X18] : l1_pre_topc(k1_compts_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k1_compts_1])).

cnf(c_0_26,plain,
    ( k1_compts_1(X1) = g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_31,plain,
    ( l1_pre_topc(k1_compts_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_compts_1(X1) = g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,plain,(
    ! [X25] : v1_tdlat_3(k1_compts_1(X25)) ),
    inference(variable_rename,[status(thm)],[fc4_tex_1])).

fof(c_0_34,negated_conjecture,(
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

cnf(c_0_35,plain,
    ( X1 = X2
    | g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))) != g1_pre_topc(X2,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( l1_pre_topc(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_38,plain,(
    ! [X16,X17] :
      ( ( v1_pre_topc(g1_pre_topc(X16,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( l1_pre_topc(g1_pre_topc(X16,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_39,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | ~ v1_tdlat_3(X9)
      | v2_pre_topc(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

cnf(c_0_40,plain,
    ( v1_tdlat_3(k1_compts_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_41,plain,(
    ! [X24] :
      ( v1_relat_1(k6_relat_1(X24))
      & v1_funct_1(k6_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_42,plain,(
    ! [X30] : k6_partfun1(X30) = k6_relat_1(X30) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_43,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ v5_pre_topc(X12,X10,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v4_pre_topc(X13,X11)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12,X13),X10)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X12),k1_zfmisc_1(u1_struct_0(X11)))
        | v5_pre_topc(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( v4_pre_topc(esk1_3(X10,X11,X12),X11)
        | v5_pre_topc(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12,esk1_3(X10,X11,X12)),X10)
        | v5_pre_topc(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

fof(c_0_44,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k8_relset_1(X31,X32,X33,X34) = k10_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_45,negated_conjecture,(
    ! [X42,X43] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ( v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,u1_struct_0(esk3_0),u1_struct_0(X42))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X42))))
        | v5_pre_topc(X43,esk3_0,X42) )
      & ~ v1_tdlat_3(esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_34])])])])])).

cnf(c_0_46,plain,
    ( u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) = X1
    | ~ v1_pre_topc(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36])]),c_0_37])])).

cnf(c_0_47,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( v1_tdlat_3(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_32])).

fof(c_0_50,plain,(
    ! [X6,X7,X8] :
      ( ( v1_funct_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_partfun1(X8,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( v1_funct_2(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_partfun1(X8,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

fof(c_0_51,plain,(
    ! [X20] :
      ( v1_partfun1(k6_partfun1(X20),X20)
      & m1_subset_1(k6_partfun1(X20),k1_zfmisc_1(k2_zfmisc_1(X20,X20))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_52,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( v2_struct_0(X1)
    | v5_pre_topc(X2,esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( u1_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_29])])).

cnf(c_0_58,plain,
    ( v2_pre_topc(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_37])])).

cnf(c_0_59,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( v1_funct_1(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,plain,
    ( v4_pre_topc(k10_relat_1(X1,X2),X3)
    | ~ v4_pre_topc(X2,X4)
    | ~ v5_pre_topc(X1,X3,X4)
    | ~ v1_funct_2(X1,u1_struct_0(X3),u1_struct_0(X4))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( v2_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
    | v5_pre_topc(X2,esk3_0,g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk3_0),X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_37])])).

cnf(c_0_65,plain,
    ( v1_funct_2(k6_partfun1(X1),X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])])).

fof(c_0_66,plain,(
    ! [X38,X39] :
      ( ( ~ v1_tdlat_3(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v4_pre_topc(X39,X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_subset_1(esk2_1(X38),k1_zfmisc_1(u1_struct_0(X38)))
        | v1_tdlat_3(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ v4_pre_topc(esk2_1(X38),X38)
        | v1_tdlat_3(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).

cnf(c_0_67,plain,
    ( v4_pre_topc(k10_relat_1(X1,X2),X3)
    | ~ v4_pre_topc(X2,g1_pre_topc(X4,k2_subset_1(k1_zfmisc_1(X4))))
    | ~ v5_pre_topc(X1,X3,g1_pre_topc(X4,k2_subset_1(k1_zfmisc_1(X4))))
    | ~ v1_funct_2(X1,u1_struct_0(X3),X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ l1_pre_topc(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_57]),c_0_37])])).

cnf(c_0_68,negated_conjecture,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),k2_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)))))
    | v5_pre_topc(k6_partfun1(u1_struct_0(esk3_0)),esk3_0,g1_pre_topc(u1_struct_0(esk3_0),k2_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_60]),c_0_65]),c_0_62])])).

cnf(c_0_69,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_70,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),k2_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)))))
    | v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(esk3_0)),X1),esk3_0)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),k2_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_65]),c_0_62]),c_0_60]),c_0_69])])).

cnf(c_0_72,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_70,c_0_48])).

cnf(c_0_73,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_76,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | k8_relset_1(X36,X36,k6_partfun1(X36),X37) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).

fof(c_0_77,plain,(
    ! [X22] :
      ( v1_xboole_0(X22)
      | ~ v2_struct_0(k1_compts_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_compts_1])])])).

cnf(c_0_78,negated_conjecture,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),k2_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)))))
    | v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(esk3_0)),X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_49]),c_0_57]),c_0_37])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk2_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_69])]),c_0_75])).

cnf(c_0_80,plain,
    ( k8_relset_1(X2,X2,k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k1_compts_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),k2_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)))))
    | v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(esk3_0)),esk2_1(esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,plain,
    ( k10_relat_1(k6_partfun1(X1),X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_55]),c_0_60])])).

cnf(c_0_84,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(g1_pre_topc(X1,k2_subset_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[c_0_81,c_0_32])).

cnf(c_0_85,negated_conjecture,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),k2_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)))))
    | v4_pre_topc(esk2_1(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_79])])).

fof(c_0_86,plain,(
    ! [X23] :
      ( v2_struct_0(X23)
      | ~ l1_struct_0(X23)
      | ~ v1_xboole_0(u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_87,plain,
    ( v1_tdlat_3(X1)
    | ~ v4_pre_topc(esk2_1(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v4_pre_topc(esk2_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_74]),c_0_69])]),c_0_75])).

cnf(c_0_91,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_92,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_93,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_94,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_69])]),
    [proof]).

%------------------------------------------------------------------------------
