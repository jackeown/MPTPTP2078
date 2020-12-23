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
% DateTime   : Thu Dec  3 11:21:00 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 (1797 expanded)
%              Number of clauses        :   83 ( 673 expanded)
%              Number of leaves         :   27 ( 454 expanded)
%              Depth                    :   15
%              Number of atoms          :  475 (10284 expanded)
%              Number of equality atoms :   75 ( 730 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tex_2)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t18_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(c_0_27,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X27))
      | ~ v1_xboole_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_28,plain,(
    ! [X46,X47] :
      ( m1_subset_1(esk2_2(X46,X47),k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      & v1_relat_1(esk2_2(X46,X47))
      & v4_relat_1(esk2_2(X46,X47),X46)
      & v5_relat_1(esk2_2(X46,X47),X47)
      & v1_funct_1(esk2_2(X46,X47))
      & v1_funct_2(esk2_2(X46,X47),X46,X47) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_xboole_0(X30)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30)))
      | v1_xboole_0(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_34,plain,(
    ! [X45] :
      ( v1_partfun1(k6_partfun1(X45),X45)
      & m1_subset_1(k6_partfun1(X45),k1_zfmisc_1(k2_zfmisc_1(X45,X45))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,esk2_2(X2,X3))
    | ~ v1_xboole_0(k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_38,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_39,negated_conjecture,(
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

cnf(c_0_40,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_41,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,esk2_2(X2,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X64,X65] :
      ( ( ~ v1_tdlat_3(X64)
        | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
        | v3_pre_topc(X65,X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) )
      & ( m1_subset_1(esk5_1(X64),k1_zfmisc_1(u1_struct_0(X64)))
        | v1_tdlat_3(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) )
      & ( ~ v3_pre_topc(esk5_1(X64),X64)
        | v1_tdlat_3(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_47,plain,(
    ! [X63] :
      ( ~ l1_pre_topc(X63)
      | ~ v1_tdlat_3(X63)
      | v2_pre_topc(X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_48,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | m1_subset_1(k8_relset_1(X33,X34,X35,X36),k1_zfmisc_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk7_0)
    & v1_tdlat_3(esk7_0)
    & l1_pre_topc(esk7_0)
    & v2_pre_topc(esk8_0)
    & l1_pre_topc(esk8_0)
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))
    & ~ v5_pre_topc(esk9_0,esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k6_partfun1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( v1_xboole_0(esk2_2(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_54,plain,(
    ! [X28,X29] : v1_relat_1(k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_55,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_50])).

fof(c_0_60,plain,(
    ! [X43,X44] :
      ( ( ~ v1_partfun1(X44,X43)
        | k1_relat_1(X44) = X43
        | ~ v1_relat_1(X44)
        | ~ v4_relat_1(X44,X43) )
      & ( k1_relat_1(X44) != X43
        | v1_partfun1(X44,X43)
        | ~ v1_relat_1(X44)
        | ~ v4_relat_1(X44,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_61,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_62,plain,
    ( k6_partfun1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( v4_relat_1(esk2_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_64,plain,
    ( esk2_2(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_53])).

cnf(c_0_65,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_66,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_67,plain,(
    ! [X49] :
      ( ~ l1_struct_0(X49)
      | k2_struct_0(X49) = u1_struct_0(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_68,plain,(
    ! [X50] :
      ( ~ l1_pre_topc(X50)
      | l1_struct_0(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_69,plain,(
    ! [X53,X54,X55,X56] :
      ( ( ~ v5_pre_topc(X55,X53,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ v3_pre_topc(X56,X54)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X53),u1_struct_0(X54),X55,X56),X53)
        | k2_struct_0(X54) = k1_xboole_0
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
        | ~ l1_pre_topc(X54)
        | ~ l1_pre_topc(X53) )
      & ( m1_subset_1(esk3_3(X53,X54,X55),k1_zfmisc_1(u1_struct_0(X54)))
        | v5_pre_topc(X55,X53,X54)
        | k2_struct_0(X54) = k1_xboole_0
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
        | ~ l1_pre_topc(X54)
        | ~ l1_pre_topc(X53) )
      & ( v3_pre_topc(esk3_3(X53,X54,X55),X54)
        | v5_pre_topc(X55,X53,X54)
        | k2_struct_0(X54) = k1_xboole_0
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
        | ~ l1_pre_topc(X54)
        | ~ l1_pre_topc(X53) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X53),u1_struct_0(X54),X55,esk3_3(X53,X54,X55)),X53)
        | v5_pre_topc(X55,X53,X54)
        | k2_struct_0(X54) = k1_xboole_0
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
        | ~ l1_pre_topc(X54)
        | ~ l1_pre_topc(X53) )
      & ( ~ v5_pre_topc(X55,X53,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ v3_pre_topc(X56,X54)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X53),u1_struct_0(X54),X55,X56),X53)
        | k2_struct_0(X53) != k1_xboole_0
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
        | ~ l1_pre_topc(X54)
        | ~ l1_pre_topc(X53) )
      & ( m1_subset_1(esk3_3(X53,X54,X55),k1_zfmisc_1(u1_struct_0(X54)))
        | v5_pre_topc(X55,X53,X54)
        | k2_struct_0(X53) != k1_xboole_0
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
        | ~ l1_pre_topc(X54)
        | ~ l1_pre_topc(X53) )
      & ( v3_pre_topc(esk3_3(X53,X54,X55),X54)
        | v5_pre_topc(X55,X53,X54)
        | k2_struct_0(X53) != k1_xboole_0
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
        | ~ l1_pre_topc(X54)
        | ~ l1_pre_topc(X53) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X53),u1_struct_0(X54),X55,esk3_3(X53,X54,X55)),X53)
        | v5_pre_topc(X55,X53,X54)
        | k2_struct_0(X53) != k1_xboole_0
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
        | ~ l1_pre_topc(X54)
        | ~ l1_pre_topc(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

cnf(c_0_70,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( v1_tdlat_3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_73,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,k6_partfun1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_59]),c_0_37])])).

cnf(c_0_75,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_76,plain,
    ( v1_partfun1(k1_xboole_0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_77,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_78,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_50])).

fof(c_0_79,plain,(
    ! [X58,X59,X60,X61] :
      ( ( ~ v5_pre_topc(X60,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X59)))
        | r1_tarski(k2_pre_topc(X58,k8_relset_1(u1_struct_0(X58),u1_struct_0(X59),X60,X61)),k8_relset_1(u1_struct_0(X58),u1_struct_0(X59),X60,k2_pre_topc(X59,X61)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59))))
        | ~ v2_pre_topc(X59)
        | ~ l1_pre_topc(X59)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) )
      & ( m1_subset_1(esk4_3(X58,X59,X60),k1_zfmisc_1(u1_struct_0(X59)))
        | v5_pre_topc(X60,X58,X59)
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59))))
        | ~ v2_pre_topc(X59)
        | ~ l1_pre_topc(X59)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) )
      & ( ~ r1_tarski(k2_pre_topc(X58,k8_relset_1(u1_struct_0(X58),u1_struct_0(X59),X60,esk4_3(X58,X59,X60))),k8_relset_1(u1_struct_0(X58),u1_struct_0(X59),X60,k2_pre_topc(X59,esk4_3(X58,X59,X60))))
        | v5_pre_topc(X60,X58,X59)
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59))))
        | ~ v2_pre_topc(X59)
        | ~ l1_pre_topc(X59)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).

fof(c_0_80,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_82,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_83,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_84,plain,
    ( v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_86,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_88,negated_conjecture,
    ( ~ v5_pre_topc(esk9_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_89,negated_conjecture,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73])])).

fof(c_0_90,plain,(
    ! [X67,X68] :
      ( ( ~ v1_tdlat_3(X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
        | v4_pre_topc(X68,X67)
        | ~ v2_pre_topc(X67)
        | ~ l1_pre_topc(X67) )
      & ( m1_subset_1(esk6_1(X67),k1_zfmisc_1(u1_struct_0(X67)))
        | v1_tdlat_3(X67)
        | ~ v2_pre_topc(X67)
        | ~ l1_pre_topc(X67) )
      & ( ~ v4_pre_topc(esk6_1(X67),X67)
        | v1_tdlat_3(X67)
        | ~ v2_pre_topc(X67)
        | ~ l1_pre_topc(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).

cnf(c_0_91,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_45])).

cnf(c_0_92,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78])])).

cnf(c_0_93,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_94,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_95,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_96,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_58])).

cnf(c_0_98,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_99,negated_conjecture,
    ( k2_struct_0(esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_73]),c_0_87]),c_0_58])]),c_0_88]),c_0_89])])).

fof(c_0_100,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_101,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

fof(c_0_102,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k1_relset_1(X37,X38,X39) = k1_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_103,plain,(
    ! [X19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_104,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_91])).

cnf(c_0_105,plain,
    ( k6_partfun1(X1) = k1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_52])).

fof(c_0_106,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | X13 = X14
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_85]),c_0_94]),c_0_95]),c_0_86]),c_0_73]),c_0_87]),c_0_58])]),c_0_88])).

cnf(c_0_108,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)) = esk9_0
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_109,negated_conjecture,
    ( u1_struct_0(esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_86])])).

cnf(c_0_110,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_111,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_101,c_0_56])).

fof(c_0_112,plain,(
    ! [X40,X41,X42] :
      ( ( k7_relset_1(X40,X41,X42,X40) = k2_relset_1(X40,X41,X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( k8_relset_1(X40,X41,X42,X41) = k1_relset_1(X40,X41,X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_113,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_114,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_115,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_37])])).

cnf(c_0_116,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk4_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk4_3(X1,X2,X3))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_117,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(esk4_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_107])).

cnf(c_0_119,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109]),c_0_36]),c_0_109]),c_0_36]),c_0_110])])).

fof(c_0_120,plain,(
    ! [X51,X52] :
      ( ( ~ v4_pre_topc(X52,X51)
        | k2_pre_topc(X51,X52) = X52
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ l1_pre_topc(X51) )
      & ( ~ v2_pre_topc(X51)
        | k2_pre_topc(X51,X52) != X52
        | v4_pre_topc(X52,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ l1_pre_topc(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_121,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_71]),c_0_72]),c_0_73])])).

cnf(c_0_122,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_123,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0))),k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,k2_pre_topc(esk8_0,esk4_3(esk7_0,esk8_0,esk9_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_85]),c_0_94]),c_0_95]),c_0_86]),c_0_73]),c_0_87]),c_0_58])]),c_0_88])).

cnf(c_0_125,plain,
    ( k6_partfun1(X1) = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_117,c_0_52])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(esk4_3(esk7_0,esk8_0,k1_xboole_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_109]),c_0_119])).

cnf(c_0_127,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_128,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk7_0),k1_xboole_0,k1_xboole_0,X1),esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_109]),c_0_119])).

cnf(c_0_129,plain,
    ( k8_relset_1(X1,X2,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_114]),c_0_123])).

cnf(c_0_130,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk7_0,k6_partfun1(X1)),k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,k2_pre_topc(esk8_0,esk4_3(esk7_0,esk8_0,esk9_0))))
    | ~ v1_xboole_0(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_131,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_126]),c_0_110])])).

cnf(c_0_132,plain,
    ( k2_pre_topc(X1,k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_114])).

cnf(c_0_133,negated_conjecture,
    ( v4_pre_topc(k1_xboole_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_134,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk7_0,k6_partfun1(X1)),k8_relset_1(u1_struct_0(esk7_0),k1_xboole_0,k1_xboole_0,k2_pre_topc(esk8_0,k1_xboole_0)))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_109]),c_0_109]),c_0_119]),c_0_119]),c_0_131]),c_0_119]),c_0_119]),c_0_131]),c_0_129]),c_0_37])])).

cnf(c_0_135,negated_conjecture,
    ( k2_pre_topc(esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_73])])).

cnf(c_0_136,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_104]),c_0_135]),c_0_110]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.35  # Version: 2.5pre002
% 0.21/0.35  # No SInE strategy applied
% 0.21/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.53  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.21/0.53  # and selection function SelectNewComplexAHPNS.
% 0.21/0.53  #
% 0.21/0.53  # Preprocessing time       : 0.031 s
% 0.21/0.53  # Presaturation interreduction done
% 0.21/0.53  
% 0.21/0.53  # Proof found!
% 0.21/0.53  # SZS status Theorem
% 0.21/0.53  # SZS output start CNFRefutation
% 0.21/0.53  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.21/0.53  fof(rc1_funct_2, axiom, ![X1, X2]:?[X3]:(((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 0.21/0.53  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.53  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.21/0.53  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.21/0.53  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.53  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.53  fof(t68_tex_2, conjecture, ![X1]:(((v2_pre_topc(X1)&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_tex_2)).
% 0.21/0.53  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.21/0.53  fof(t17_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 0.21/0.53  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.21/0.53  fof(dt_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 0.21/0.53  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.53  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.21/0.53  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.53  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.21/0.53  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.53  fof(t55_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X4,X2)=>v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_2)).
% 0.21/0.53  fof(t56_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_2)).
% 0.21/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.53  fof(t18_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tdlat_3)).
% 0.21/0.53  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.53  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.53  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.53  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.21/0.53  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 0.21/0.53  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.21/0.53  fof(c_0_27, plain, ![X25, X26, X27]:(~r2_hidden(X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(X27))|~v1_xboole_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.21/0.53  fof(c_0_28, plain, ![X46, X47]:(((((m1_subset_1(esk2_2(X46,X47),k1_zfmisc_1(k2_zfmisc_1(X46,X47)))&v1_relat_1(esk2_2(X46,X47)))&v4_relat_1(esk2_2(X46,X47),X46))&v5_relat_1(esk2_2(X46,X47),X47))&v1_funct_1(esk2_2(X46,X47)))&v1_funct_2(esk2_2(X46,X47),X46,X47)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).
% 0.21/0.53  fof(c_0_29, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.53  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.53  cnf(c_0_31, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.53  cnf(c_0_32, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.53  fof(c_0_33, plain, ![X30, X31, X32]:(~v1_xboole_0(X30)|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30)))|v1_xboole_0(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.21/0.53  fof(c_0_34, plain, ![X45]:(v1_partfun1(k6_partfun1(X45),X45)&m1_subset_1(k6_partfun1(X45),k1_zfmisc_1(k2_zfmisc_1(X45,X45)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.21/0.53  cnf(c_0_35, plain, (~r2_hidden(X1,esk2_2(X2,X3))|~v1_xboole_0(k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.53  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_32])).
% 0.21/0.53  cnf(c_0_37, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.53  fof(c_0_38, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.53  fof(c_0_39, negated_conjecture, ~(![X1]:(((v2_pre_topc(X1)&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>v5_pre_topc(X3,X1,X2))))), inference(assume_negation,[status(cth)],[t68_tex_2])).
% 0.21/0.53  cnf(c_0_40, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.53  fof(c_0_41, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.21/0.53  cnf(c_0_42, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.53  cnf(c_0_43, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.53  cnf(c_0_44, plain, (~r2_hidden(X1,esk2_2(X2,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.21/0.53  cnf(c_0_45, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.53  fof(c_0_46, plain, ![X64, X65]:((~v1_tdlat_3(X64)|(~m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))|v3_pre_topc(X65,X64))|(~v2_pre_topc(X64)|~l1_pre_topc(X64)))&((m1_subset_1(esk5_1(X64),k1_zfmisc_1(u1_struct_0(X64)))|v1_tdlat_3(X64)|(~v2_pre_topc(X64)|~l1_pre_topc(X64)))&(~v3_pre_topc(esk5_1(X64),X64)|v1_tdlat_3(X64)|(~v2_pre_topc(X64)|~l1_pre_topc(X64))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).
% 0.21/0.53  fof(c_0_47, plain, ![X63]:(~l1_pre_topc(X63)|(~v1_tdlat_3(X63)|v2_pre_topc(X63))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.21/0.53  fof(c_0_48, plain, ![X33, X34, X35, X36]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|m1_subset_1(k8_relset_1(X33,X34,X35,X36),k1_zfmisc_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).
% 0.21/0.53  fof(c_0_49, negated_conjecture, (((v2_pre_topc(esk7_0)&v1_tdlat_3(esk7_0))&l1_pre_topc(esk7_0))&((v2_pre_topc(esk8_0)&l1_pre_topc(esk8_0))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))))&~v5_pre_topc(esk9_0,esk7_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.21/0.53  cnf(c_0_50, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_40])).
% 0.21/0.53  cnf(c_0_51, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.53  cnf(c_0_52, plain, (v1_xboole_0(k6_partfun1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.53  cnf(c_0_53, plain, (v1_xboole_0(esk2_2(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.53  fof(c_0_54, plain, ![X28, X29]:v1_relat_1(k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.53  cnf(c_0_55, plain, (v3_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.53  cnf(c_0_56, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.53  cnf(c_0_57, plain, (m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.53  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.53  cnf(c_0_59, plain, (m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_43, c_0_50])).
% 0.21/0.53  fof(c_0_60, plain, ![X43, X44]:((~v1_partfun1(X44,X43)|k1_relat_1(X44)=X43|(~v1_relat_1(X44)|~v4_relat_1(X44,X43)))&(k1_relat_1(X44)!=X43|v1_partfun1(X44,X43)|(~v1_relat_1(X44)|~v4_relat_1(X44,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.21/0.53  cnf(c_0_61, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.53  cnf(c_0_62, plain, (k6_partfun1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.53  cnf(c_0_63, plain, (v4_relat_1(esk2_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.53  cnf(c_0_64, plain, (esk2_2(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_53])).
% 0.21/0.53  cnf(c_0_65, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.53  fof(c_0_66, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.53  fof(c_0_67, plain, ![X49]:(~l1_struct_0(X49)|k2_struct_0(X49)=u1_struct_0(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.21/0.53  fof(c_0_68, plain, ![X50]:(~l1_pre_topc(X50)|l1_struct_0(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.53  fof(c_0_69, plain, ![X53, X54, X55, X56]:(((~v5_pre_topc(X55,X53,X54)|(~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))|(~v3_pre_topc(X56,X54)|v3_pre_topc(k8_relset_1(u1_struct_0(X53),u1_struct_0(X54),X55,X56),X53)))|k2_struct_0(X54)=k1_xboole_0|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54)))))|~l1_pre_topc(X54)|~l1_pre_topc(X53))&((m1_subset_1(esk3_3(X53,X54,X55),k1_zfmisc_1(u1_struct_0(X54)))|v5_pre_topc(X55,X53,X54)|k2_struct_0(X54)=k1_xboole_0|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54)))))|~l1_pre_topc(X54)|~l1_pre_topc(X53))&((v3_pre_topc(esk3_3(X53,X54,X55),X54)|v5_pre_topc(X55,X53,X54)|k2_struct_0(X54)=k1_xboole_0|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54)))))|~l1_pre_topc(X54)|~l1_pre_topc(X53))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X53),u1_struct_0(X54),X55,esk3_3(X53,X54,X55)),X53)|v5_pre_topc(X55,X53,X54)|k2_struct_0(X54)=k1_xboole_0|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54)))))|~l1_pre_topc(X54)|~l1_pre_topc(X53)))))&((~v5_pre_topc(X55,X53,X54)|(~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))|(~v3_pre_topc(X56,X54)|v3_pre_topc(k8_relset_1(u1_struct_0(X53),u1_struct_0(X54),X55,X56),X53)))|k2_struct_0(X53)!=k1_xboole_0|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54)))))|~l1_pre_topc(X54)|~l1_pre_topc(X53))&((m1_subset_1(esk3_3(X53,X54,X55),k1_zfmisc_1(u1_struct_0(X54)))|v5_pre_topc(X55,X53,X54)|k2_struct_0(X53)!=k1_xboole_0|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54)))))|~l1_pre_topc(X54)|~l1_pre_topc(X53))&((v3_pre_topc(esk3_3(X53,X54,X55),X54)|v5_pre_topc(X55,X53,X54)|k2_struct_0(X53)!=k1_xboole_0|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54)))))|~l1_pre_topc(X54)|~l1_pre_topc(X53))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X53),u1_struct_0(X54),X55,esk3_3(X53,X54,X55)),X53)|v5_pre_topc(X55,X53,X54)|k2_struct_0(X53)!=k1_xboole_0|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54)))))|~l1_pre_topc(X54)|~l1_pre_topc(X53)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).
% 0.21/0.53  cnf(c_0_70, plain, (v3_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.53  cnf(c_0_71, negated_conjecture, (m1_subset_1(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.53  cnf(c_0_72, negated_conjecture, (v1_tdlat_3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.53  cnf(c_0_73, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.53  cnf(c_0_74, plain, (~r2_hidden(X1,k6_partfun1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_59]), c_0_37])])).
% 0.21/0.53  cnf(c_0_75, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.53  cnf(c_0_76, plain, (v1_partfun1(k1_xboole_0,X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.53  cnf(c_0_77, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.53  cnf(c_0_78, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_50])).
% 0.21/0.53  fof(c_0_79, plain, ![X58, X59, X60, X61]:((~v5_pre_topc(X60,X58,X59)|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X59)))|r1_tarski(k2_pre_topc(X58,k8_relset_1(u1_struct_0(X58),u1_struct_0(X59),X60,X61)),k8_relset_1(u1_struct_0(X58),u1_struct_0(X59),X60,k2_pre_topc(X59,X61))))|(~v1_funct_1(X60)|~v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59)))))|(~v2_pre_topc(X59)|~l1_pre_topc(X59))|(~v2_pre_topc(X58)|~l1_pre_topc(X58)))&((m1_subset_1(esk4_3(X58,X59,X60),k1_zfmisc_1(u1_struct_0(X59)))|v5_pre_topc(X60,X58,X59)|(~v1_funct_1(X60)|~v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59)))))|(~v2_pre_topc(X59)|~l1_pre_topc(X59))|(~v2_pre_topc(X58)|~l1_pre_topc(X58)))&(~r1_tarski(k2_pre_topc(X58,k8_relset_1(u1_struct_0(X58),u1_struct_0(X59),X60,esk4_3(X58,X59,X60))),k8_relset_1(u1_struct_0(X58),u1_struct_0(X59),X60,k2_pre_topc(X59,esk4_3(X58,X59,X60))))|v5_pre_topc(X60,X58,X59)|(~v1_funct_1(X60)|~v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59)))))|(~v2_pre_topc(X59)|~l1_pre_topc(X59))|(~v2_pre_topc(X58)|~l1_pre_topc(X58))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_2])])])])])).
% 0.21/0.53  fof(c_0_80, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.53  cnf(c_0_81, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.53  cnf(c_0_82, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.53  cnf(c_0_83, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.53  cnf(c_0_84, plain, (v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.21/0.53  cnf(c_0_85, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.53  cnf(c_0_86, negated_conjecture, (l1_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.53  cnf(c_0_87, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.53  cnf(c_0_88, negated_conjecture, (~v5_pre_topc(esk9_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.53  cnf(c_0_89, negated_conjecture, (v3_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_73])])).
% 0.21/0.53  fof(c_0_90, plain, ![X67, X68]:((~v1_tdlat_3(X67)|(~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|v4_pre_topc(X68,X67))|(~v2_pre_topc(X67)|~l1_pre_topc(X67)))&((m1_subset_1(esk6_1(X67),k1_zfmisc_1(u1_struct_0(X67)))|v1_tdlat_3(X67)|(~v2_pre_topc(X67)|~l1_pre_topc(X67)))&(~v4_pre_topc(esk6_1(X67),X67)|v1_tdlat_3(X67)|(~v2_pre_topc(X67)|~l1_pre_topc(X67))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tdlat_3])])])])])).
% 0.21/0.53  cnf(c_0_91, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_74, c_0_45])).
% 0.21/0.53  cnf(c_0_92, plain, (k1_relat_1(k1_xboole_0)=X1|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78])])).
% 0.21/0.53  cnf(c_0_93, plain, (m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.21/0.53  cnf(c_0_94, negated_conjecture, (v2_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.53  cnf(c_0_95, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.53  cnf(c_0_96, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.21/0.53  cnf(c_0_97, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))), inference(spm,[status(thm)],[c_0_81, c_0_58])).
% 0.21/0.53  cnf(c_0_98, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.21/0.53  cnf(c_0_99, negated_conjecture, (k2_struct_0(esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_73]), c_0_87]), c_0_58])]), c_0_88]), c_0_89])])).
% 0.21/0.53  fof(c_0_100, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.53  cnf(c_0_101, plain, (v4_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.21/0.53  fof(c_0_102, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k1_relset_1(X37,X38,X39)=k1_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.53  fof(c_0_103, plain, ![X19]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.53  cnf(c_0_104, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_91])).
% 0.21/0.53  cnf(c_0_105, plain, (k6_partfun1(X1)=k1_relat_1(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_92, c_0_52])).
% 0.21/0.53  fof(c_0_106, plain, ![X13, X14]:(~v1_xboole_0(X13)|X13=X14|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.21/0.53  cnf(c_0_107, negated_conjecture, (m1_subset_1(esk4_3(esk7_0,esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_85]), c_0_94]), c_0_95]), c_0_86]), c_0_73]), c_0_87]), c_0_58])]), c_0_88])).
% 0.21/0.53  cnf(c_0_108, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))=esk9_0|~r1_tarski(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)),esk9_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.21/0.53  cnf(c_0_109, negated_conjecture, (u1_struct_0(esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_86])])).
% 0.21/0.53  cnf(c_0_110, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.21/0.53  cnf(c_0_111, plain, (v4_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_101, c_0_56])).
% 0.21/0.53  fof(c_0_112, plain, ![X40, X41, X42]:((k7_relset_1(X40,X41,X42,X40)=k2_relset_1(X40,X41,X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(k8_relset_1(X40,X41,X42,X41)=k1_relset_1(X40,X41,X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.21/0.53  cnf(c_0_113, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.21/0.53  cnf(c_0_114, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.21/0.53  cnf(c_0_115, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_37])])).
% 0.21/0.53  cnf(c_0_116, plain, (v5_pre_topc(X3,X1,X2)|~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk4_3(X1,X2,X3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_pre_topc(X2,esk4_3(X1,X2,X3))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.21/0.53  cnf(c_0_117, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.21/0.53  cnf(c_0_118, negated_conjecture, (r1_tarski(esk4_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_81, c_0_107])).
% 0.21/0.53  cnf(c_0_119, negated_conjecture, (esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_109]), c_0_36]), c_0_109]), c_0_36]), c_0_110])])).
% 0.21/0.53  fof(c_0_120, plain, ![X51, X52]:((~v4_pre_topc(X52,X51)|k2_pre_topc(X51,X52)=X52|~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))|~l1_pre_topc(X51))&(~v2_pre_topc(X51)|k2_pre_topc(X51,X52)!=X52|v4_pre_topc(X52,X51)|~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))|~l1_pre_topc(X51))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.21/0.53  cnf(c_0_121, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,X1),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_71]), c_0_72]), c_0_73])])).
% 0.21/0.53  cnf(c_0_122, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 0.21/0.53  cnf(c_0_123, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])).
% 0.21/0.53  cnf(c_0_124, negated_conjecture, (~r1_tarski(k2_pre_topc(esk7_0,k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0))),k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,k2_pre_topc(esk8_0,esk4_3(esk7_0,esk8_0,esk9_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_85]), c_0_94]), c_0_95]), c_0_86]), c_0_73]), c_0_87]), c_0_58])]), c_0_88])).
% 0.21/0.53  cnf(c_0_125, plain, (k6_partfun1(X1)=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_117, c_0_52])).
% 0.21/0.53  cnf(c_0_126, negated_conjecture, (r1_tarski(esk4_3(esk7_0,esk8_0,k1_xboole_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_109]), c_0_119])).
% 0.21/0.53  cnf(c_0_127, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.21/0.53  cnf(c_0_128, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk7_0),k1_xboole_0,k1_xboole_0,X1),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_109]), c_0_119])).
% 0.21/0.53  cnf(c_0_129, plain, (k8_relset_1(X1,X2,k1_xboole_0,X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_114]), c_0_123])).
% 0.21/0.53  cnf(c_0_130, negated_conjecture, (~r1_tarski(k2_pre_topc(esk7_0,k6_partfun1(X1)),k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,k2_pre_topc(esk8_0,esk4_3(esk7_0,esk8_0,esk9_0))))|~v1_xboole_0(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0),esk9_0,esk4_3(esk7_0,esk8_0,esk9_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 0.21/0.53  cnf(c_0_131, negated_conjecture, (esk4_3(esk7_0,esk8_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_126]), c_0_110])])).
% 0.21/0.53  cnf(c_0_132, plain, (k2_pre_topc(X1,k1_xboole_0)=k1_xboole_0|~v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_127, c_0_114])).
% 0.21/0.53  cnf(c_0_133, negated_conjecture, (v4_pre_topc(k1_xboole_0,esk7_0)), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 0.21/0.53  cnf(c_0_134, negated_conjecture, (~r1_tarski(k2_pre_topc(esk7_0,k6_partfun1(X1)),k8_relset_1(u1_struct_0(esk7_0),k1_xboole_0,k1_xboole_0,k2_pre_topc(esk8_0,k1_xboole_0)))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_109]), c_0_109]), c_0_119]), c_0_119]), c_0_131]), c_0_119]), c_0_119]), c_0_131]), c_0_129]), c_0_37])])).
% 0.21/0.53  cnf(c_0_135, negated_conjecture, (k2_pre_topc(esk7_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_73])])).
% 0.21/0.53  cnf(c_0_136, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_104]), c_0_135]), c_0_110]), c_0_37])]), ['proof']).
% 0.21/0.53  # SZS output end CNFRefutation
% 0.21/0.53  # Proof object total steps             : 137
% 0.21/0.53  # Proof object clause steps            : 83
% 0.21/0.53  # Proof object formula steps           : 54
% 0.21/0.53  # Proof object conjectures             : 31
% 0.21/0.53  # Proof object clause conjectures      : 28
% 0.21/0.53  # Proof object formula conjectures     : 3
% 0.21/0.53  # Proof object initial clauses used    : 39
% 0.21/0.53  # Proof object initial formulas used   : 27
% 0.21/0.53  # Proof object generating inferences   : 36
% 0.21/0.53  # Proof object simplifying inferences  : 76
% 0.21/0.53  # Training examples: 0 positive, 0 negative
% 0.21/0.53  # Parsed axioms                        : 30
% 0.21/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.53  # Initial clauses                      : 66
% 0.21/0.53  # Removed in clause preprocessing      : 1
% 0.21/0.53  # Initial clauses in saturation        : 65
% 0.21/0.53  # Processed clauses                    : 1539
% 0.21/0.53  # ...of these trivial                  : 29
% 0.21/0.53  # ...subsumed                          : 956
% 0.21/0.53  # ...remaining for further processing  : 554
% 0.21/0.53  # Other redundant clauses eliminated   : 24
% 0.21/0.53  # Clauses deleted for lack of memory   : 0
% 0.21/0.53  # Backward-subsumed                    : 15
% 0.21/0.53  # Backward-rewritten                   : 73
% 0.21/0.53  # Generated clauses                    : 8240
% 0.21/0.53  # ...of the previous two non-trivial   : 6836
% 0.21/0.53  # Contextual simplify-reflections      : 9
% 0.21/0.53  # Paramodulations                      : 8216
% 0.21/0.53  # Factorizations                       : 0
% 0.21/0.53  # Equation resolutions                 : 24
% 0.21/0.53  # Propositional unsat checks           : 0
% 0.21/0.53  #    Propositional check models        : 0
% 0.21/0.53  #    Propositional check unsatisfiable : 0
% 0.21/0.53  #    Propositional clauses             : 0
% 0.21/0.53  #    Propositional clauses after purity: 0
% 0.21/0.53  #    Propositional unsat core size     : 0
% 0.21/0.53  #    Propositional preprocessing time  : 0.000
% 0.21/0.53  #    Propositional encoding time       : 0.000
% 0.21/0.53  #    Propositional solver time         : 0.000
% 0.21/0.53  #    Success case prop preproc time    : 0.000
% 0.21/0.53  #    Success case prop encoding time   : 0.000
% 0.21/0.53  #    Success case prop solver time     : 0.000
% 0.21/0.53  # Current number of processed clauses  : 397
% 0.21/0.53  #    Positive orientable unit clauses  : 67
% 0.21/0.53  #    Positive unorientable unit clauses: 3
% 0.21/0.53  #    Negative unit clauses             : 2
% 0.21/0.53  #    Non-unit-clauses                  : 325
% 0.21/0.53  # Current number of unprocessed clauses: 5316
% 0.21/0.53  # ...number of literals in the above   : 23591
% 0.21/0.53  # Current number of archived formulas  : 0
% 0.21/0.53  # Current number of archived clauses   : 153
% 0.21/0.53  # Clause-clause subsumption calls (NU) : 41885
% 0.21/0.53  # Rec. Clause-clause subsumption calls : 11889
% 0.21/0.53  # Non-unit clause-clause subsumptions  : 632
% 0.21/0.53  # Unit Clause-clause subsumption calls : 1114
% 0.21/0.53  # Rewrite failures with RHS unbound    : 0
% 0.21/0.53  # BW rewrite match attempts            : 273
% 0.21/0.53  # BW rewrite match successes           : 18
% 0.21/0.53  # Condensation attempts                : 0
% 0.21/0.53  # Condensation successes               : 0
% 0.21/0.53  # Termbank termtop insertions          : 101377
% 0.21/0.53  
% 0.21/0.53  # -------------------------------------------------
% 0.21/0.53  # User time                : 0.172 s
% 0.21/0.53  # System time              : 0.009 s
% 0.21/0.53  # Total time               : 0.181 s
% 0.21/0.53  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
