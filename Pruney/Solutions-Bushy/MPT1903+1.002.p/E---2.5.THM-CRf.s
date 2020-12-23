%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1903+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:01 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 284 expanded)
%              Number of clauses        :   52 ( 116 expanded)
%              Number of leaves         :   17 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  304 (1147 expanded)
%              Number of equality atoms :   49 ( 148 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_k1_tex_1,axiom,(
    ! [X1] : m1_subset_1(k1_tex_1(X1),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_1)).

fof(fc2_tex_1,axiom,(
    ! [X1] :
      ( v1_pre_topc(k2_tex_1(X1))
      & v2_pre_topc(k2_tex_1(X1))
      & v2_tdlat_3(k2_tex_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_1)).

fof(d3_tex_1,axiom,(
    ! [X1] : k2_tex_1(X1) = g1_pre_topc(X1,k1_tex_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_1)).

fof(dt_k2_tex_1,axiom,(
    ! [X1] : l1_pre_topc(k2_tex_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tex_1)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tdlat_3)).

fof(t171_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(fc3_tex_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ~ v2_struct_0(k2_tex_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_tex_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_17,plain,(
    ! [X23,X24,X25,X26] :
      ( ( X23 = X25
        | g1_pre_topc(X23,X24) != g1_pre_topc(X25,X26)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23))) )
      & ( X24 = X26
        | g1_pre_topc(X23,X24) != g1_pre_topc(X25,X26)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_18,plain,(
    ! [X15] : m1_subset_1(k1_tex_1(X15),k1_zfmisc_1(k1_zfmisc_1(X15))) ),
    inference(variable_rename,[status(thm)],[dt_k1_tex_1])).

fof(c_0_19,plain,(
    ! [X20] :
      ( v1_pre_topc(k2_tex_1(X20))
      & v2_pre_topc(k2_tex_1(X20))
      & v2_tdlat_3(k2_tex_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[fc2_tex_1])).

fof(c_0_20,plain,(
    ! [X14] : k2_tex_1(X14) = g1_pre_topc(X14,k1_tex_1(X14)) ),
    inference(variable_rename,[status(thm)],[d3_tex_1])).

fof(c_0_21,plain,(
    ! [X16] : l1_pre_topc(k2_tex_1(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k2_tex_1])).

cnf(c_0_22,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_tex_1(X1),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_25,plain,
    ( v1_pre_topc(k2_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_tex_1(X1) = g1_pre_topc(X1,k1_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( l1_pre_topc(k2_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X21] :
      ( v1_relat_1(k6_relat_1(X21))
      & v1_funct_1(k6_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_29,plain,(
    ! [X27] : k6_partfun1(X27) = k6_relat_1(X27) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_30,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v5_pre_topc(X11,X9,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v4_pre_topc(X12,X10)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,X12),X9)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(u1_struct_0(X10)))
        | v5_pre_topc(X11,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) )
      & ( v4_pre_topc(esk1_3(X9,X10,X11),X10)
        | v5_pre_topc(X11,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,esk1_3(X9,X10,X11)),X9)
        | v5_pre_topc(X11,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | g1_pre_topc(X1,k1_tex_1(X1)) != g1_pre_topc(X2,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( l1_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

fof(c_0_35,plain,(
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

fof(c_0_36,plain,(
    ! [X17] :
      ( v1_partfun1(k6_partfun1(X17),X17)
      & m1_subset_1(k6_partfun1(X17),k1_zfmisc_1(k2_zfmisc_1(X17,X17))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_37,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,negated_conjecture,(
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

fof(c_0_40,plain,(
    ! [X30,X31] :
      ( ( ~ v2_tdlat_3(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ v4_pre_topc(X31,X30)
        | X31 = k1_xboole_0
        | X31 = u1_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( m1_subset_1(esk2_1(X30),k1_zfmisc_1(u1_struct_0(X30)))
        | v2_tdlat_3(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( v4_pre_topc(esk2_1(X30),X30)
        | v2_tdlat_3(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( esk2_1(X30) != k1_xboole_0
        | v2_tdlat_3(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( esk2_1(X30) != u1_struct_0(X30)
        | v2_tdlat_3(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_tdlat_3])])])])])).

cnf(c_0_41,plain,
    ( v2_tdlat_3(k2_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,plain,
    ( v2_pre_topc(k2_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32])]),c_0_33]),c_0_34])])).

fof(c_0_45,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | k8_relset_1(X28,X28,k6_partfun1(X28),X29) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).

cnf(c_0_46,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( v1_funct_1(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_50,negated_conjecture,(
    ! [X34,X35] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ( v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X34),u1_struct_0(esk3_0))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(esk3_0))))
        | v5_pre_topc(X35,X34,esk3_0) )
      & ~ v2_tdlat_3(esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_39])])])])])).

cnf(c_0_51,plain,
    ( X2 = k1_xboole_0
    | X2 = u1_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( v2_tdlat_3(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_26])).

cnf(c_0_53,plain,
    ( v2_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_54,plain,
    ( v4_pre_topc(k8_relset_1(X1,u1_struct_0(X2),X3,X4),g1_pre_topc(X1,k1_tex_1(X1)))
    | ~ v4_pre_topc(X4,X2)
    | ~ v5_pre_topc(X3,g1_pre_topc(X1,k1_tex_1(X1)),X2)
    | ~ v1_funct_2(X3,X1,u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34])])).

cnf(c_0_55,plain,
    ( k8_relset_1(X2,X2,k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( v1_funct_2(k6_partfun1(X1),X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(X1)
    | v5_pre_topc(X2,X1,esk3_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | X1 = X2
    | ~ v4_pre_topc(X1,g1_pre_topc(X2,k1_tex_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_52]),c_0_53]),c_0_34])])).

cnf(c_0_59,plain,
    ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),k1_tex_1(u1_struct_0(X2))))
    | ~ v4_pre_topc(X1,X2)
    | ~ v5_pre_topc(k6_partfun1(u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X2),k1_tex_1(u1_struct_0(X2))),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_49]),c_0_47])])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(g1_pre_topc(X1,k1_tex_1(X1)))
    | v5_pre_topc(X2,g1_pre_topc(X1,k1_tex_1(X1)),esk3_0)
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_44]),c_0_53]),c_0_34])])).

fof(c_0_61,plain,(
    ! [X22] :
      ( v1_xboole_0(X22)
      | ~ v2_struct_0(k2_tex_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_tex_1])])])).

cnf(c_0_62,plain,
    ( X1 = u1_struct_0(X2)
    | X1 = k1_xboole_0
    | ~ v4_pre_topc(X1,X2)
    | ~ v5_pre_topc(k6_partfun1(u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X2),k1_tex_1(u1_struct_0(X2))),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),k1_tex_1(u1_struct_0(esk3_0))))
    | v5_pre_topc(k6_partfun1(u1_struct_0(esk3_0)),g1_pre_topc(u1_struct_0(esk3_0),k1_tex_1(u1_struct_0(esk3_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_47]),c_0_56]),c_0_49])])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_66,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( ~ v2_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_68,plain,
    ( v4_pre_topc(esk2_1(X1),X1)
    | v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_tex_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( X1 = u1_struct_0(esk3_0)
    | X1 = k1_xboole_0
    | v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),k1_tex_1(u1_struct_0(esk3_0))))
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk2_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_64])]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( v4_pre_topc(esk2_1(esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_66]),c_0_64])]),c_0_67])).

fof(c_0_73,plain,(
    ! [X19] :
      ( v2_struct_0(X19)
      | ~ l1_struct_0(X19)
      | ~ v1_xboole_0(u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_26])).

cnf(c_0_75,negated_conjecture,
    ( esk2_1(esk3_0) = u1_struct_0(esk3_0)
    | esk2_1(esk3_0) = k1_xboole_0
    | v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),k1_tex_1(u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( esk2_1(esk3_0) = u1_struct_0(esk3_0)
    | esk2_1(esk3_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_79,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_80,negated_conjecture,
    ( esk2_1(esk3_0) = u1_struct_0(esk3_0)
    | esk2_1(esk3_0) = k1_xboole_0
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_81,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_82,plain,
    ( v2_tdlat_3(X1)
    | esk2_1(X1) != u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_83,negated_conjecture,
    ( esk2_1(esk3_0) = u1_struct_0(esk3_0)
    | esk2_1(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_64])])).

cnf(c_0_84,plain,
    ( v2_tdlat_3(X1)
    | esk2_1(X1) != k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_85,negated_conjecture,
    ( esk2_1(esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_66]),c_0_64])]),c_0_67])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_66]),c_0_64])]),c_0_67]),
    [proof]).

%------------------------------------------------------------------------------
