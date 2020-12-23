%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t71_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:56 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 326 expanded)
%              Number of clauses        :   51 ( 133 expanded)
%              Number of leaves         :   17 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  303 (1340 expanded)
%              Number of equality atoms :   45 ( 177 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',free_g1_pre_topc)).

fof(dt_k1_tex_1,axiom,(
    ! [X1] : m1_subset_1(k1_tex_1(X1),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',dt_k1_tex_1)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',abstractness_v1_pre_topc)).

fof(fc2_tex_1,axiom,(
    ! [X1] :
      ( v1_pre_topc(k2_tex_1(X1))
      & v2_pre_topc(k2_tex_1(X1))
      & v2_tdlat_3(k2_tex_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',fc2_tex_1)).

fof(d3_tex_1,axiom,(
    ! [X1] : k2_tex_1(X1) = g1_pre_topc(X1,k1_tex_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',d3_tex_1)).

fof(dt_k2_tex_1,axiom,(
    ! [X1] : l1_pre_topc(k2_tex_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',dt_k2_tex_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',fc3_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',d12_pre_topc)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',cc1_funct_2)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',dt_k6_partfun1)).

fof(t71_tex_2,conjecture,(
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
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
               => v5_pre_topc(X3,X2,X1) ) )
       => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',t71_tex_2)).

fof(t171_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',t171_funct_2)).

fof(t21_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v2_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ~ ( v4_pre_topc(X2,X1)
                & X2 != k1_xboole_0
                & X2 != u1_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',t21_tdlat_3)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',dt_l1_pre_topc)).

fof(fc3_tex_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ~ v2_struct_0(k2_tex_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',fc3_tex_1)).

fof(c_0_17,plain,(
    ! [X40,X41,X42,X43] :
      ( ( X40 = X42
        | g1_pre_topc(X40,X41) != g1_pre_topc(X42,X43)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k1_zfmisc_1(X40))) )
      & ( X41 = X43
        | g1_pre_topc(X40,X41) != g1_pre_topc(X42,X43)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k1_zfmisc_1(X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_18,plain,(
    ! [X22] : m1_subset_1(k1_tex_1(X22),k1_zfmisc_1(k1_zfmisc_1(X22))) ),
    inference(variable_rename,[status(thm)],[dt_k1_tex_1])).

cnf(c_0_19,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( m1_subset_1(k1_tex_1(X1),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | ~ v1_pre_topc(X8)
      | X8 = g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_22,plain,(
    ! [X37] :
      ( v1_pre_topc(k2_tex_1(X37))
      & v2_pre_topc(k2_tex_1(X37))
      & v2_tdlat_3(k2_tex_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[fc2_tex_1])).

fof(c_0_23,plain,(
    ! [X19] : k2_tex_1(X19) = g1_pre_topc(X19,k1_tex_1(X19)) ),
    inference(variable_rename,[status(thm)],[d3_tex_1])).

fof(c_0_24,plain,(
    ! [X23] : l1_pre_topc(k2_tex_1(X23)) ),
    inference(variable_rename,[status(thm)],[dt_k2_tex_1])).

cnf(c_0_25,plain,
    ( X1 = X2
    | g1_pre_topc(X1,k1_tex_1(X1)) != g1_pre_topc(X2,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v1_pre_topc(k2_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_tex_1(X1) = g1_pre_topc(X1,k1_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( l1_pre_topc(k2_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X38] :
      ( v1_relat_1(k6_relat_1(X38))
      & v1_funct_1(k6_relat_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_31,plain,(
    ! [X45] : k6_partfun1(X45) = k6_relat_1(X45) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_32,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ v5_pre_topc(X16,X14,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v4_pre_topc(X17,X15)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,X17),X14)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X15)))
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( v4_pre_topc(esk2_3(X14,X15,X16),X15)
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,esk2_3(X14,X15,X16)),X14)
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_33,plain,
    ( X1 = u1_struct_0(X2)
    | g1_pre_topc(X1,k1_tex_1(X1)) != X2
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( v1_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( l1_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

fof(c_0_36,plain,(
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

fof(c_0_37,plain,(
    ! [X24] :
      ( v1_partfun1(k6_partfun1(X24),X24)
      & m1_subset_1(k6_partfun1(X24),k1_zfmisc_1(k2_zfmisc_1(X24,X24))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_38,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_40,negated_conjecture,(
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
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => v5_pre_topc(X3,X2,X1) ) )
         => v2_tdlat_3(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t71_tex_2])).

cnf(c_0_41,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34]),c_0_35])])).

fof(c_0_43,plain,(
    ! [X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(X50))
      | k8_relset_1(X50,X50,k6_partfun1(X50),X51) = X51 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).

cnf(c_0_44,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( v1_funct_1(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_48,negated_conjecture,(
    ! [X6,X7] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & ( v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(esk1_0))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(esk1_0))))
        | v5_pre_topc(X7,X6,esk1_0) )
      & ~ v2_tdlat_3(esk1_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_40])])])])])).

cnf(c_0_49,plain,
    ( v2_pre_topc(k2_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,plain,
    ( v4_pre_topc(k8_relset_1(X1,u1_struct_0(X2),X3,X4),g1_pre_topc(X1,k1_tex_1(X1)))
    | ~ v4_pre_topc(X4,X2)
    | ~ v5_pre_topc(X3,g1_pre_topc(X1,k1_tex_1(X1)),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_2(X3,X1,u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_35])])).

cnf(c_0_51,plain,
    ( k8_relset_1(X2,X2,k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( v1_funct_2(k6_partfun1(X1),X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_53,negated_conjecture,
    ( v2_struct_0(X1)
    | v5_pre_topc(X2,X1,esk1_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( v2_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_55,plain,
    ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),k1_tex_1(u1_struct_0(X2))))
    | ~ v4_pre_topc(X1,X2)
    | ~ v5_pre_topc(k6_partfun1(u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X2),k1_tex_1(u1_struct_0(X2))),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_45]),c_0_52]),c_0_47])])).

cnf(c_0_56,negated_conjecture,
    ( v5_pre_topc(X1,g1_pre_topc(X2,k1_tex_1(X2)),esk1_0)
    | v2_struct_0(g1_pre_topc(X2,k1_tex_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk1_0))))
    | ~ v1_funct_2(X1,X2,u1_struct_0(esk1_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_42]),c_0_35]),c_0_54])])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_58,plain,(
    ! [X54,X55] :
      ( ( ~ v2_tdlat_3(X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ v4_pre_topc(X55,X54)
        | X55 = k1_xboole_0
        | X55 = u1_struct_0(X54)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) )
      & ( m1_subset_1(esk7_1(X54),k1_zfmisc_1(u1_struct_0(X54)))
        | v2_tdlat_3(X54)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) )
      & ( v4_pre_topc(esk7_1(X54),X54)
        | v2_tdlat_3(X54)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) )
      & ( esk7_1(X54) != k1_xboole_0
        | v2_tdlat_3(X54)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) )
      & ( esk7_1(X54) != u1_struct_0(X54)
        | v2_tdlat_3(X54)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_tdlat_3])])])])])).

fof(c_0_59,plain,(
    ! [X36] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | ~ v1_xboole_0(u1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_60,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_61,plain,(
    ! [X39] :
      ( v1_xboole_0(X39)
      | ~ v2_struct_0(k2_tex_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_tex_1])])])).

cnf(c_0_62,negated_conjecture,
    ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),k1_tex_1(u1_struct_0(esk1_0))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(esk1_0),k1_tex_1(u1_struct_0(esk1_0))))
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_45]),c_0_52]),c_0_47])])).

cnf(c_0_63,plain,
    ( m1_subset_1(esk7_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_66,plain,
    ( v2_tdlat_3(k2_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( X2 = k1_xboole_0
    | X2 = u1_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( v4_pre_topc(esk7_1(esk1_0),g1_pre_topc(u1_struct_0(esk1_0),k1_tex_1(u1_struct_0(esk1_0))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(esk1_0),k1_tex_1(u1_struct_0(esk1_0))))
    | ~ v4_pre_topc(esk7_1(esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_57]),c_0_64])]),c_0_65])).

cnf(c_0_72,plain,
    ( v2_tdlat_3(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(rw,[status(thm)],[c_0_66,c_0_28])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_28])).

cnf(c_0_76,negated_conjecture,
    ( esk7_1(esk1_0) = u1_struct_0(esk1_0)
    | esk7_1(esk1_0) = k1_xboole_0
    | v2_struct_0(g1_pre_topc(u1_struct_0(esk1_0),k1_tex_1(u1_struct_0(esk1_0))))
    | ~ v4_pre_topc(esk7_1(esk1_0),esk1_0)
    | ~ m1_subset_1(esk7_1(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_42]),c_0_72]),c_0_42]),c_0_35]),c_0_54])])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_57])])).

cnf(c_0_78,negated_conjecture,
    ( esk7_1(esk1_0) = u1_struct_0(esk1_0)
    | esk7_1(esk1_0) = k1_xboole_0
    | ~ v4_pre_topc(esk7_1(esk1_0),esk1_0)
    | ~ m1_subset_1(esk7_1(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_79,plain,
    ( v4_pre_topc(esk7_1(X1),X1)
    | v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( esk7_1(esk1_0) = u1_struct_0(esk1_0)
    | esk7_1(esk1_0) = k1_xboole_0
    | ~ m1_subset_1(esk7_1(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_57]),c_0_64])]),c_0_65])).

cnf(c_0_81,plain,
    ( v2_tdlat_3(X1)
    | esk7_1(X1) != u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_82,negated_conjecture,
    ( esk7_1(esk1_0) = u1_struct_0(esk1_0)
    | esk7_1(esk1_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_63]),c_0_57]),c_0_64])]),c_0_65])).

cnf(c_0_83,plain,
    ( v2_tdlat_3(X1)
    | esk7_1(X1) != k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_84,negated_conjecture,
    ( esk7_1(esk1_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_57]),c_0_64])]),c_0_65])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_57]),c_0_64])]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
