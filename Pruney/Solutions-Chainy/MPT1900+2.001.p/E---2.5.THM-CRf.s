%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  146 (1560 expanded)
%              Number of clauses        :   90 ( 639 expanded)
%              Number of leaves         :   28 ( 396 expanded)
%              Depth                    :   16
%              Number of atoms          :  518 (7913 expanded)
%              Number of equality atoms :   83 ( 707 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t68_tex_2,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => v5_pre_topc(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(t56_tops_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t55_tops_2,axiom,(
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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t18_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_28,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | ~ r1_tarski(esk1_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk1_2(X14,X15),X15)
        | r1_tarski(esk1_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_29,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_30,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | m1_subset_1(k8_relset_1(X39,X40,X41,X42),k1_zfmisc_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_31,plain,(
    ! [X21] : ~ v1_xboole_0(k1_zfmisc_1(X21)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

fof(c_0_38,plain,(
    ! [X46,X47,X48] :
      ( ( k7_relset_1(X46,X47,X48,X46) = k2_relset_1(X46,X47,X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( k8_relset_1(X46,X47,X48,X47) = k1_relset_1(X46,X47,X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_39,plain,
    ( r1_tarski(k8_relset_1(X1,X2,X3,X4),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_41,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k1_relset_1(X43,X44,X45) = k1_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_42,plain,(
    ! [X17,X18] :
      ( ( k2_zfmisc_1(X17,X18) != k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_relset_1(X1,X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_46,plain,(
    ! [X33,X34,X35] :
      ( ( v4_relat_1(X35,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v5_relat_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_47,plain,(
    ! [X51] :
      ( v1_partfun1(k6_partfun1(X51),X51)
      & m1_subset_1(k6_partfun1(X51),k1_zfmisc_1(k2_zfmisc_1(X51,X51))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_48,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | v1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_49,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_45])).

fof(c_0_52,plain,(
    ! [X49,X50] :
      ( ( ~ v1_partfun1(X50,X49)
        | k1_relat_1(X50) = X49
        | ~ v1_relat_1(X50)
        | ~ v4_relat_1(X50,X49) )
      & ( k1_relat_1(X50) != X49
        | v1_partfun1(X50,X49)
        | ~ v1_relat_1(X50)
        | ~ v4_relat_1(X50,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_53,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_56,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | X8 = X9
      | ~ v1_xboole_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_57,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_xboole_0(X36)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X37,X36)))
      | v1_xboole_0(X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_58,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => v5_pre_topc(X3,X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_tex_2])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( v4_relat_1(k6_partfun1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_64,plain,
    ( v1_relat_1(k6_partfun1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_54])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_68,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    & v1_tdlat_3(esk6_0)
    & l1_pre_topc(esk6_0)
    & v2_pre_topc(esk7_0)
    & l1_pre_topc(esk7_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))))
    & ~ v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).

fof(c_0_69,plain,(
    ! [X67,X68] :
      ( ( ~ v1_tdlat_3(X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
        | v3_pre_topc(X68,X67)
        | ~ v2_pre_topc(X67)
        | ~ l1_pre_topc(X67) )
      & ( m1_subset_1(esk4_1(X67),k1_zfmisc_1(u1_struct_0(X67)))
        | v1_tdlat_3(X67)
        | ~ v2_pre_topc(X67)
        | ~ l1_pre_topc(X67) )
      & ( ~ v3_pre_topc(esk4_1(X67),X67)
        | v1_tdlat_3(X67)
        | ~ v2_pre_topc(X67)
        | ~ l1_pre_topc(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_70,plain,(
    ! [X66] :
      ( ~ l1_pre_topc(X66)
      | ~ v1_tdlat_3(X66)
      | v2_pre_topc(X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_71,plain,(
    ! [X61,X62,X63,X64] :
      ( ( ~ v5_pre_topc(X63,X61,X62)
        | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X62)))
        | r1_tarski(k2_pre_topc(X61,k8_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63,X64)),k8_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63,k2_pre_topc(X62,X64)))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,u1_struct_0(X61),u1_struct_0(X62))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X61),u1_struct_0(X62))))
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) )
      & ( m1_subset_1(esk3_3(X61,X62,X63),k1_zfmisc_1(u1_struct_0(X62)))
        | v5_pre_topc(X63,X61,X62)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,u1_struct_0(X61),u1_struct_0(X62))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X61),u1_struct_0(X62))))
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) )
      & ( ~ r1_tarski(k2_pre_topc(X61,k8_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63,esk3_3(X61,X62,X63))),k8_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63,k2_pre_topc(X62,esk3_3(X61,X62,X63))))
        | v5_pre_topc(X63,X61,X62)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,u1_struct_0(X61),u1_struct_0(X62))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X61),u1_struct_0(X62))))
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).

cnf(c_0_72,plain,
    ( X1 = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_73,plain,
    ( k1_relat_1(k6_partfun1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( v1_xboole_0(k6_partfun1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_54])).

fof(c_0_76,plain,(
    ! [X22] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_78,plain,(
    ! [X20] : m1_subset_1(k2_subset_1(X20),k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_79,plain,(
    ! [X19] : k2_subset_1(X19) = X19 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_80,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_82,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_85,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_86,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_87,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_88,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_89,negated_conjecture,
    ( ~ v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_90,plain,
    ( X1 = X2
    | ~ m1_subset_1(k6_partfun1(X2),k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_91,plain,
    ( k6_partfun1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_92,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_77]),c_0_35])).

cnf(c_0_94,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_95,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_96,plain,(
    ! [X56,X57,X58,X59] :
      ( ( ~ v5_pre_topc(X58,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X57)))
        | ~ v3_pre_topc(X59,X57)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X56),u1_struct_0(X57),X58,X59),X56)
        | k2_struct_0(X57) = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
        | ~ l1_pre_topc(X57)
        | ~ l1_pre_topc(X56) )
      & ( m1_subset_1(esk2_3(X56,X57,X58),k1_zfmisc_1(u1_struct_0(X57)))
        | v5_pre_topc(X58,X56,X57)
        | k2_struct_0(X57) = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
        | ~ l1_pre_topc(X57)
        | ~ l1_pre_topc(X56) )
      & ( v3_pre_topc(esk2_3(X56,X57,X58),X57)
        | v5_pre_topc(X58,X56,X57)
        | k2_struct_0(X57) = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
        | ~ l1_pre_topc(X57)
        | ~ l1_pre_topc(X56) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X56),u1_struct_0(X57),X58,esk2_3(X56,X57,X58)),X56)
        | v5_pre_topc(X58,X56,X57)
        | k2_struct_0(X57) = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
        | ~ l1_pre_topc(X57)
        | ~ l1_pre_topc(X56) )
      & ( ~ v5_pre_topc(X58,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X57)))
        | ~ v3_pre_topc(X59,X57)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X56),u1_struct_0(X57),X58,X59),X56)
        | k2_struct_0(X56) != k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
        | ~ l1_pre_topc(X57)
        | ~ l1_pre_topc(X56) )
      & ( m1_subset_1(esk2_3(X56,X57,X58),k1_zfmisc_1(u1_struct_0(X57)))
        | v5_pre_topc(X58,X56,X57)
        | k2_struct_0(X56) != k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
        | ~ l1_pre_topc(X57)
        | ~ l1_pre_topc(X56) )
      & ( v3_pre_topc(esk2_3(X56,X57,X58),X57)
        | v5_pre_topc(X58,X56,X57)
        | k2_struct_0(X56) != k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
        | ~ l1_pre_topc(X57)
        | ~ l1_pre_topc(X56) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X56),u1_struct_0(X57),X58,esk2_3(X56,X57,X58)),X56)
        | v5_pre_topc(X58,X56,X57)
        | k2_struct_0(X56) != k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
        | ~ l1_pre_topc(X57)
        | ~ l1_pre_topc(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

cnf(c_0_97,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(esk3_3(esk6_0,esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_77]),c_0_83]),c_0_84]),c_0_85]),c_0_86]),c_0_87]),c_0_88])]),c_0_89])).

cnf(c_0_99,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_93])).

cnf(c_0_101,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

fof(c_0_102,plain,(
    ! [X52] :
      ( ~ l1_struct_0(X52)
      | k2_struct_0(X52) = u1_struct_0(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_103,plain,(
    ! [X53] :
      ( ~ l1_pre_topc(X53)
      | l1_struct_0(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_104,plain,
    ( v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_105,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X1),X2,X3,X4),X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),X2))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_34])).

fof(c_0_106,plain,(
    ! [X70,X71] :
      ( ( ~ v1_tdlat_3(X70)
        | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))
        | v4_pre_topc(X71,X70)
        | ~ v2_pre_topc(X70)
        | ~ l1_pre_topc(X70) )
      & ( m1_subset_1(esk5_1(X70),k1_zfmisc_1(u1_struct_0(X70)))
        | v1_tdlat_3(X70)
        | ~ v2_pre_topc(X70)
        | ~ l1_pre_topc(X70) )
      & ( ~ v4_pre_topc(esk5_1(X70),X70)
        | v1_tdlat_3(X70)
        | ~ v2_pre_topc(X70)
        | ~ l1_pre_topc(X70) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk3_3(esk6_0,esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_98]),c_0_35])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_73])).

cnf(c_0_109,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)) = esk8_0
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_110,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_101])).

cnf(c_0_111,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_112,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_113,plain,
    ( k2_struct_0(X1) = k1_xboole_0
    | v5_pre_topc(X2,X3,X1)
    | ~ v1_tdlat_3(X3)
    | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_114,negated_conjecture,
    ( v1_tdlat_3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_115,plain,(
    ! [X54,X55] :
      ( ( ~ v4_pre_topc(X55,X54)
        | k2_pre_topc(X54,X55) = X55
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ l1_pre_topc(X54) )
      & ( ~ v2_pre_topc(X54)
        | k2_pre_topc(X54,X55) != X55
        | v4_pre_topc(X55,X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ l1_pre_topc(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_116,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(esk3_3(esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_107])).

cnf(c_0_118,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_91]),c_0_92])])).

cnf(c_0_119,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_51]),c_0_66])])).

cnf(c_0_120,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)) = esk8_0
    | ~ v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_121,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_122,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_77]),c_0_114]),c_0_83]),c_0_84]),c_0_87]),c_0_88])]),c_0_89])).

cnf(c_0_123,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_92])).

fof(c_0_124,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_125,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_126,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_116,c_0_81])).

cnf(c_0_127,negated_conjecture,
    ( esk3_3(esk6_0,esk7_0,esk8_0) = u1_struct_0(esk7_0)
    | ~ r1_tarski(u1_struct_0(esk7_0),esk3_3(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_117])).

cnf(c_0_128,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_129,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)) = esk8_0
    | ~ m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_119])).

cnf(c_0_130,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_87])])).

cnf(c_0_131,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_123])).

cnf(c_0_132,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_133,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk3_3(X1,X2,X3))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_134,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_135,negated_conjecture,
    ( esk3_3(esk6_0,esk7_0,esk8_0) = u1_struct_0(esk7_0)
    | ~ m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_136,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130]),c_0_51]),c_0_130]),c_0_92])])).

cnf(c_0_137,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_138,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relat_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_40])).

cnf(c_0_139,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v1_tdlat_3(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ r1_tarski(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,esk3_3(X2,X3,X1)),k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,k2_pre_topc(X3,esk3_3(X2,X3,X1)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_34]),c_0_81])).

cnf(c_0_140,negated_conjecture,
    ( esk3_3(esk6_0,esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_130]),c_0_130]),c_0_92])]),c_0_136])).

cnf(c_0_141,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk6_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_130]),c_0_136])).

cnf(c_0_142,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_136])).

cnf(c_0_143,plain,
    ( k8_relset_1(X1,X2,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_92])])).

cnf(c_0_144,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_89,c_0_136])).

cnf(c_0_145,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_114]),c_0_130]),c_0_141]),c_0_142]),c_0_85]),c_0_87]),c_0_88]),c_0_130]),c_0_51]),c_0_92]),c_0_130]),c_0_143]),c_0_130]),c_0_132])]),c_0_144]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.55  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.55  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.55  #
% 0.19/0.55  # Preprocessing time       : 0.031 s
% 0.19/0.55  # Presaturation interreduction done
% 0.19/0.55  
% 0.19/0.55  # Proof found!
% 0.19/0.55  # SZS status Theorem
% 0.19/0.55  # SZS output start CNFRefutation
% 0.19/0.55  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.55  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.55  fof(dt_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 0.19/0.55  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.55  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 0.19/0.55  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.55  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.55  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.55  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.19/0.55  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.55  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.55  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.19/0.55  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.19/0.55  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.19/0.55  fof(t68_tex_2, conjecture, ![X1]:(((v2_pre_topc(X1)&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tex_2)).
% 0.19/0.55  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.55  fof(t17_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 0.19/0.55  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.19/0.55  fof(t56_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_2)).
% 0.19/0.55  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.55  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.55  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.55  fof(t55_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X4,X2)=>v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_2)).
% 0.19/0.55  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.55  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.55  fof(t18_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tdlat_3)).
% 0.19/0.55  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.19/0.55  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.55  fof(c_0_28, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|r1_tarski(X12,X10)|X11!=k1_zfmisc_1(X10))&(~r1_tarski(X13,X10)|r2_hidden(X13,X11)|X11!=k1_zfmisc_1(X10)))&((~r2_hidden(esk1_2(X14,X15),X15)|~r1_tarski(esk1_2(X14,X15),X14)|X15=k1_zfmisc_1(X14))&(r2_hidden(esk1_2(X14,X15),X15)|r1_tarski(esk1_2(X14,X15),X14)|X15=k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.55  fof(c_0_29, plain, ![X23, X24]:(~m1_subset_1(X23,X24)|(v1_xboole_0(X24)|r2_hidden(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.55  fof(c_0_30, plain, ![X39, X40, X41, X42]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|m1_subset_1(k8_relset_1(X39,X40,X41,X42),k1_zfmisc_1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).
% 0.19/0.55  fof(c_0_31, plain, ![X21]:~v1_xboole_0(k1_zfmisc_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.55  cnf(c_0_32, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.55  cnf(c_0_33, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.55  cnf(c_0_34, plain, (m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.55  cnf(c_0_35, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.55  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.55  cnf(c_0_37, plain, (r2_hidden(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.19/0.55  fof(c_0_38, plain, ![X46, X47, X48]:((k7_relset_1(X46,X47,X48,X46)=k2_relset_1(X46,X47,X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(k8_relset_1(X46,X47,X48,X47)=k1_relset_1(X46,X47,X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.19/0.55  cnf(c_0_39, plain, (r1_tarski(k8_relset_1(X1,X2,X3,X4),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.55  cnf(c_0_40, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.55  fof(c_0_41, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k1_relset_1(X43,X44,X45)=k1_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.55  fof(c_0_42, plain, ![X17, X18]:((k2_zfmisc_1(X17,X18)!=k1_xboole_0|(X17=k1_xboole_0|X18=k1_xboole_0))&((X17!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0)&(X18!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.55  cnf(c_0_43, plain, (r1_tarski(k1_relset_1(X1,X2,X3),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.55  cnf(c_0_44, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.55  cnf(c_0_45, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.55  fof(c_0_46, plain, ![X33, X34, X35]:((v4_relat_1(X35,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(v5_relat_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.55  fof(c_0_47, plain, ![X51]:(v1_partfun1(k6_partfun1(X51),X51)&m1_subset_1(k6_partfun1(X51),k1_zfmisc_1(k2_zfmisc_1(X51,X51)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.19/0.55  fof(c_0_48, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.55  fof(c_0_49, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.55  cnf(c_0_50, plain, (r1_tarski(k1_relat_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.55  cnf(c_0_51, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.55  fof(c_0_52, plain, ![X49, X50]:((~v1_partfun1(X50,X49)|k1_relat_1(X50)=X49|(~v1_relat_1(X50)|~v4_relat_1(X50,X49)))&(k1_relat_1(X50)!=X49|v1_partfun1(X50,X49)|(~v1_relat_1(X50)|~v4_relat_1(X50,X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.19/0.55  cnf(c_0_53, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.55  cnf(c_0_54, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.55  cnf(c_0_55, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.55  fof(c_0_56, plain, ![X8, X9]:(~v1_xboole_0(X8)|X8=X9|~v1_xboole_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.19/0.55  fof(c_0_57, plain, ![X36, X37, X38]:(~v1_xboole_0(X36)|(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X37,X36)))|v1_xboole_0(X38))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.19/0.55  fof(c_0_58, negated_conjecture, ~(![X1]:(((v2_pre_topc(X1)&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2))))), inference(assume_negation,[status(cth)],[t68_tex_2])).
% 0.19/0.55  cnf(c_0_59, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.55  cnf(c_0_60, plain, (r1_tarski(k1_relat_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.55  cnf(c_0_61, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.55  cnf(c_0_62, plain, (v4_relat_1(k6_partfun1(X1),X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.55  cnf(c_0_63, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.55  cnf(c_0_64, plain, (v1_relat_1(k6_partfun1(X1))), inference(spm,[status(thm)],[c_0_55, c_0_54])).
% 0.19/0.55  cnf(c_0_65, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.55  cnf(c_0_66, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.55  cnf(c_0_67, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.55  fof(c_0_68, negated_conjecture, (((v2_pre_topc(esk6_0)&v1_tdlat_3(esk6_0))&l1_pre_topc(esk6_0))&((v2_pre_topc(esk7_0)&l1_pre_topc(esk7_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))))&~v5_pre_topc(esk8_0,esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).
% 0.19/0.55  fof(c_0_69, plain, ![X67, X68]:((~v1_tdlat_3(X67)|(~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|v3_pre_topc(X68,X67))|(~v2_pre_topc(X67)|~l1_pre_topc(X67)))&((m1_subset_1(esk4_1(X67),k1_zfmisc_1(u1_struct_0(X67)))|v1_tdlat_3(X67)|(~v2_pre_topc(X67)|~l1_pre_topc(X67)))&(~v3_pre_topc(esk4_1(X67),X67)|v1_tdlat_3(X67)|(~v2_pre_topc(X67)|~l1_pre_topc(X67))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).
% 0.19/0.55  fof(c_0_70, plain, ![X66]:(~l1_pre_topc(X66)|(~v1_tdlat_3(X66)|v2_pre_topc(X66))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.19/0.55  fof(c_0_71, plain, ![X61, X62, X63, X64]:((~v5_pre_topc(X63,X61,X62)|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X62)))|r1_tarski(k2_pre_topc(X61,k8_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63,X64)),k8_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63,k2_pre_topc(X62,X64))))|(~v1_funct_1(X63)|~v1_funct_2(X63,u1_struct_0(X61),u1_struct_0(X62))|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X61),u1_struct_0(X62)))))|(~v2_pre_topc(X62)|~l1_pre_topc(X62))|(~v2_pre_topc(X61)|~l1_pre_topc(X61)))&((m1_subset_1(esk3_3(X61,X62,X63),k1_zfmisc_1(u1_struct_0(X62)))|v5_pre_topc(X63,X61,X62)|(~v1_funct_1(X63)|~v1_funct_2(X63,u1_struct_0(X61),u1_struct_0(X62))|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X61),u1_struct_0(X62)))))|(~v2_pre_topc(X62)|~l1_pre_topc(X62))|(~v2_pre_topc(X61)|~l1_pre_topc(X61)))&(~r1_tarski(k2_pre_topc(X61,k8_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63,esk3_3(X61,X62,X63))),k8_relset_1(u1_struct_0(X61),u1_struct_0(X62),X63,k2_pre_topc(X62,esk3_3(X61,X62,X63))))|v5_pre_topc(X63,X61,X62)|(~v1_funct_1(X63)|~v1_funct_2(X63,u1_struct_0(X61),u1_struct_0(X62))|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X61),u1_struct_0(X62)))))|(~v2_pre_topc(X62)|~l1_pre_topc(X62))|(~v2_pre_topc(X61)|~l1_pre_topc(X61))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).
% 0.19/0.55  cnf(c_0_72, plain, (X1=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.55  cnf(c_0_73, plain, (k1_relat_1(k6_partfun1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])])).
% 0.19/0.55  cnf(c_0_74, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.55  cnf(c_0_75, plain, (v1_xboole_0(k6_partfun1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_67, c_0_54])).
% 0.19/0.55  fof(c_0_76, plain, ![X22]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.55  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.55  fof(c_0_78, plain, ![X20]:m1_subset_1(k2_subset_1(X20),k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.55  fof(c_0_79, plain, ![X19]:k2_subset_1(X19)=X19, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.55  cnf(c_0_80, plain, (v3_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.55  cnf(c_0_81, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.55  cnf(c_0_82, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.55  cnf(c_0_83, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.55  cnf(c_0_84, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.55  cnf(c_0_85, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.55  cnf(c_0_86, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.55  cnf(c_0_87, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.55  cnf(c_0_88, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.55  cnf(c_0_89, negated_conjecture, (~v5_pre_topc(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.55  cnf(c_0_90, plain, (X1=X2|~m1_subset_1(k6_partfun1(X2),k1_zfmisc_1(k1_xboole_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.55  cnf(c_0_91, plain, (k6_partfun1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.55  cnf(c_0_92, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.55  cnf(c_0_93, negated_conjecture, (r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_77]), c_0_35])).
% 0.19/0.55  cnf(c_0_94, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.19/0.55  cnf(c_0_95, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.55  fof(c_0_96, plain, ![X56, X57, X58, X59]:(((~v5_pre_topc(X58,X56,X57)|(~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X57)))|(~v3_pre_topc(X59,X57)|v3_pre_topc(k8_relset_1(u1_struct_0(X56),u1_struct_0(X57),X58,X59),X56)))|k2_struct_0(X57)=k1_xboole_0|(~v1_funct_1(X58)|~v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57)))))|~l1_pre_topc(X57)|~l1_pre_topc(X56))&((m1_subset_1(esk2_3(X56,X57,X58),k1_zfmisc_1(u1_struct_0(X57)))|v5_pre_topc(X58,X56,X57)|k2_struct_0(X57)=k1_xboole_0|(~v1_funct_1(X58)|~v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57)))))|~l1_pre_topc(X57)|~l1_pre_topc(X56))&((v3_pre_topc(esk2_3(X56,X57,X58),X57)|v5_pre_topc(X58,X56,X57)|k2_struct_0(X57)=k1_xboole_0|(~v1_funct_1(X58)|~v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57)))))|~l1_pre_topc(X57)|~l1_pre_topc(X56))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X56),u1_struct_0(X57),X58,esk2_3(X56,X57,X58)),X56)|v5_pre_topc(X58,X56,X57)|k2_struct_0(X57)=k1_xboole_0|(~v1_funct_1(X58)|~v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57)))))|~l1_pre_topc(X57)|~l1_pre_topc(X56)))))&((~v5_pre_topc(X58,X56,X57)|(~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X57)))|(~v3_pre_topc(X59,X57)|v3_pre_topc(k8_relset_1(u1_struct_0(X56),u1_struct_0(X57),X58,X59),X56)))|k2_struct_0(X56)!=k1_xboole_0|(~v1_funct_1(X58)|~v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57)))))|~l1_pre_topc(X57)|~l1_pre_topc(X56))&((m1_subset_1(esk2_3(X56,X57,X58),k1_zfmisc_1(u1_struct_0(X57)))|v5_pre_topc(X58,X56,X57)|k2_struct_0(X56)!=k1_xboole_0|(~v1_funct_1(X58)|~v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57)))))|~l1_pre_topc(X57)|~l1_pre_topc(X56))&((v3_pre_topc(esk2_3(X56,X57,X58),X57)|v5_pre_topc(X58,X56,X57)|k2_struct_0(X56)!=k1_xboole_0|(~v1_funct_1(X58)|~v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57)))))|~l1_pre_topc(X57)|~l1_pre_topc(X56))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X56),u1_struct_0(X57),X58,esk2_3(X56,X57,X58)),X56)|v5_pre_topc(X58,X56,X57)|k2_struct_0(X56)!=k1_xboole_0|(~v1_funct_1(X58)|~v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57)))))|~l1_pre_topc(X57)|~l1_pre_topc(X56)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).
% 0.19/0.55  cnf(c_0_97, plain, (v3_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.55  cnf(c_0_98, negated_conjecture, (m1_subset_1(esk3_3(esk6_0,esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_77]), c_0_83]), c_0_84]), c_0_85]), c_0_86]), c_0_87]), c_0_88])]), c_0_89])).
% 0.19/0.55  cnf(c_0_99, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])])).
% 0.19/0.55  cnf(c_0_100, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_36, c_0_93])).
% 0.19/0.55  cnf(c_0_101, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.55  fof(c_0_102, plain, ![X52]:(~l1_struct_0(X52)|k2_struct_0(X52)=u1_struct_0(X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.55  fof(c_0_103, plain, ![X53]:(~l1_pre_topc(X53)|l1_struct_0(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.55  cnf(c_0_104, plain, (v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.19/0.55  cnf(c_0_105, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X1),X2,X3,X4),X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),X2)))), inference(spm,[status(thm)],[c_0_97, c_0_34])).
% 0.19/0.55  fof(c_0_106, plain, ![X70, X71]:((~v1_tdlat_3(X70)|(~m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))|v4_pre_topc(X71,X70))|(~v2_pre_topc(X70)|~l1_pre_topc(X70)))&((m1_subset_1(esk5_1(X70),k1_zfmisc_1(u1_struct_0(X70)))|v1_tdlat_3(X70)|(~v2_pre_topc(X70)|~l1_pre_topc(X70)))&(~v4_pre_topc(esk5_1(X70),X70)|v1_tdlat_3(X70)|(~v2_pre_topc(X70)|~l1_pre_topc(X70))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).
% 0.19/0.55  cnf(c_0_107, negated_conjecture, (r2_hidden(esk3_3(esk6_0,esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_98]), c_0_35])).
% 0.19/0.55  cnf(c_0_108, plain, (r1_tarski(X1,X2)|~m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_50, c_0_73])).
% 0.19/0.55  cnf(c_0_109, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))=esk8_0|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.19/0.55  cnf(c_0_110, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_67, c_0_101])).
% 0.19/0.55  cnf(c_0_111, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.19/0.55  cnf(c_0_112, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.19/0.55  cnf(c_0_113, plain, (k2_struct_0(X1)=k1_xboole_0|v5_pre_topc(X2,X3,X1)|~v1_tdlat_3(X3)|~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.19/0.55  cnf(c_0_114, negated_conjecture, (v1_tdlat_3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.55  fof(c_0_115, plain, ![X54, X55]:((~v4_pre_topc(X55,X54)|k2_pre_topc(X54,X55)=X55|~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|~l1_pre_topc(X54))&(~v2_pre_topc(X54)|k2_pre_topc(X54,X55)!=X55|v4_pre_topc(X55,X54)|~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|~l1_pre_topc(X54))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.19/0.55  cnf(c_0_116, plain, (v4_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.19/0.55  cnf(c_0_117, negated_conjecture, (r1_tarski(esk3_3(esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_36, c_0_107])).
% 0.19/0.55  cnf(c_0_118, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_91]), c_0_92])])).
% 0.19/0.55  cnf(c_0_119, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_51]), c_0_66])])).
% 0.19/0.55  cnf(c_0_120, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))=esk8_0|~v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.19/0.55  cnf(c_0_121, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 0.19/0.55  cnf(c_0_122, negated_conjecture, (k2_struct_0(esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_77]), c_0_114]), c_0_83]), c_0_84]), c_0_87]), c_0_88])]), c_0_89])).
% 0.19/0.55  cnf(c_0_123, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_50, c_0_92])).
% 0.19/0.55  fof(c_0_124, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.55  cnf(c_0_125, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.19/0.55  cnf(c_0_126, plain, (v4_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_116, c_0_81])).
% 0.19/0.55  cnf(c_0_127, negated_conjecture, (esk3_3(esk6_0,esk7_0,esk8_0)=u1_struct_0(esk7_0)|~r1_tarski(u1_struct_0(esk7_0),esk3_3(esk6_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_59, c_0_117])).
% 0.19/0.55  cnf(c_0_128, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 0.19/0.55  cnf(c_0_129, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))=esk8_0|~m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_120, c_0_119])).
% 0.19/0.55  cnf(c_0_130, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_87])])).
% 0.19/0.55  cnf(c_0_131, plain, (X1=k1_relat_1(k1_xboole_0)|~r1_tarski(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_59, c_0_123])).
% 0.19/0.55  cnf(c_0_132, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_124])).
% 0.19/0.55  cnf(c_0_133, plain, (v5_pre_topc(X3,X1,X2)|~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk3_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.55  cnf(c_0_134, plain, (k2_pre_topc(X1,X2)=X2|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 0.19/0.55  cnf(c_0_135, negated_conjecture, (esk3_3(esk6_0,esk7_0,esk8_0)=u1_struct_0(esk7_0)|~m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 0.19/0.55  cnf(c_0_136, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130]), c_0_51]), c_0_130]), c_0_92])])).
% 0.19/0.55  cnf(c_0_137, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 0.19/0.55  cnf(c_0_138, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relat_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_44, c_0_40])).
% 0.19/0.55  cnf(c_0_139, plain, (v5_pre_topc(X1,X2,X3)|~v1_tdlat_3(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~r1_tarski(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,esk3_3(X2,X3,X1)),k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,k2_pre_topc(X3,esk3_3(X2,X3,X1))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_34]), c_0_81])).
% 0.19/0.55  cnf(c_0_140, negated_conjecture, (esk3_3(esk6_0,esk7_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_130]), c_0_130]), c_0_92])]), c_0_136])).
% 0.19/0.55  cnf(c_0_141, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk6_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_130]), c_0_136])).
% 0.19/0.55  cnf(c_0_142, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_84, c_0_136])).
% 0.19/0.55  cnf(c_0_143, plain, (k8_relset_1(X1,X2,k1_xboole_0,X2)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_92])])).
% 0.19/0.55  cnf(c_0_144, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_89, c_0_136])).
% 0.19/0.55  cnf(c_0_145, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_114]), c_0_130]), c_0_141]), c_0_142]), c_0_85]), c_0_87]), c_0_88]), c_0_130]), c_0_51]), c_0_92]), c_0_130]), c_0_143]), c_0_130]), c_0_132])]), c_0_144]), ['proof']).
% 0.19/0.55  # SZS output end CNFRefutation
% 0.19/0.55  # Proof object total steps             : 146
% 0.19/0.55  # Proof object clause steps            : 90
% 0.19/0.55  # Proof object formula steps           : 56
% 0.19/0.55  # Proof object conjectures             : 30
% 0.19/0.55  # Proof object clause conjectures      : 27
% 0.19/0.55  # Proof object formula conjectures     : 3
% 0.19/0.55  # Proof object initial clauses used    : 38
% 0.19/0.55  # Proof object initial formulas used   : 28
% 0.19/0.55  # Proof object generating inferences   : 42
% 0.19/0.55  # Proof object simplifying inferences  : 68
% 0.19/0.55  # Training examples: 0 positive, 0 negative
% 0.19/0.55  # Parsed axioms                        : 30
% 0.19/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.55  # Initial clauses                      : 64
% 0.19/0.55  # Removed in clause preprocessing      : 1
% 0.19/0.55  # Initial clauses in saturation        : 63
% 0.19/0.55  # Processed clauses                    : 2589
% 0.19/0.55  # ...of these trivial                  : 36
% 0.19/0.55  # ...subsumed                          : 1808
% 0.19/0.55  # ...remaining for further processing  : 745
% 0.19/0.55  # Other redundant clauses eliminated   : 9
% 0.19/0.55  # Clauses deleted for lack of memory   : 0
% 0.19/0.55  # Backward-subsumed                    : 61
% 0.19/0.55  # Backward-rewritten                   : 224
% 0.19/0.55  # Generated clauses                    : 8439
% 0.19/0.55  # ...of the previous two non-trivial   : 7116
% 0.19/0.55  # Contextual simplify-reflections      : 39
% 0.19/0.55  # Paramodulations                      : 8420
% 0.19/0.55  # Factorizations                       : 10
% 0.19/0.55  # Equation resolutions                 : 9
% 0.19/0.55  # Propositional unsat checks           : 0
% 0.19/0.55  #    Propositional check models        : 0
% 0.19/0.55  #    Propositional check unsatisfiable : 0
% 0.19/0.55  #    Propositional clauses             : 0
% 0.19/0.55  #    Propositional clauses after purity: 0
% 0.19/0.55  #    Propositional unsat core size     : 0
% 0.19/0.55  #    Propositional preprocessing time  : 0.000
% 0.19/0.55  #    Propositional encoding time       : 0.000
% 0.19/0.55  #    Propositional solver time         : 0.000
% 0.19/0.55  #    Success case prop preproc time    : 0.000
% 0.19/0.55  #    Success case prop encoding time   : 0.000
% 0.19/0.55  #    Success case prop solver time     : 0.000
% 0.19/0.55  # Current number of processed clauses  : 391
% 0.19/0.55  #    Positive orientable unit clauses  : 48
% 0.19/0.55  #    Positive unorientable unit clauses: 0
% 0.19/0.55  #    Negative unit clauses             : 9
% 0.19/0.55  #    Non-unit-clauses                  : 334
% 0.19/0.55  # Current number of unprocessed clauses: 4599
% 0.19/0.55  # ...number of literals in the above   : 20969
% 0.19/0.55  # Current number of archived formulas  : 0
% 0.19/0.55  # Current number of archived clauses   : 348
% 0.19/0.55  # Clause-clause subsumption calls (NU) : 144439
% 0.19/0.55  # Rec. Clause-clause subsumption calls : 69796
% 0.19/0.55  # Non-unit clause-clause subsumptions  : 1825
% 0.19/0.55  # Unit Clause-clause subsumption calls : 1675
% 0.19/0.55  # Rewrite failures with RHS unbound    : 0
% 0.19/0.55  # BW rewrite match attempts            : 30
% 0.19/0.55  # BW rewrite match successes           : 8
% 0.19/0.55  # Condensation attempts                : 0
% 0.19/0.55  # Condensation successes               : 0
% 0.19/0.55  # Termbank termtop insertions          : 124262
% 0.19/0.55  
% 0.19/0.55  # -------------------------------------------------
% 0.19/0.55  # User time                : 0.201 s
% 0.19/0.55  # System time              : 0.011 s
% 0.19/0.55  # Total time               : 0.212 s
% 0.19/0.55  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
