%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1782+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:44 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 371 expanded)
%              Number of clauses        :   69 ( 142 expanded)
%              Number of leaves         :   14 (  95 expanded)
%              Depth                    :   22
%              Number of atoms          :  398 (2196 expanded)
%              Number of equality atoms :   27 (  58 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(t97_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                 => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X4,X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k4_tmap_1(X1,X3),X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tmap_1)).

fof(fc8_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v1_xboole_0(X2)
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X5)
        & v1_funct_2(X5,X2,X3)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ( v1_funct_1(k5_relat_1(X4,X5))
        & v1_funct_2(k5_relat_1(X4,X5),X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_2)).

fof(t69_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X2),u1_struct_0(X3))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                         => r2_funct_2(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X5,X6),X4),k1_partfun1(u1_struct_0(X4),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),k2_tmap_1(X1,X2,X5,X4),X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tmap_1)).

fof(d4_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k3_struct_0(X1) = k6_partfun1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_struct_0)).

fof(dt_k3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ( v1_funct_1(k3_struct_0(X1))
        & v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
        & m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d7_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => k4_tmap_1(X1,X2) = k2_tmap_1(X1,X1,k3_struct_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tmap_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t23_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
        & r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_14,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | m1_subset_1(k4_relset_1(X11,X12,X13,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(X11,X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

fof(c_0_15,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k4_relset_1(X31,X32,X33,X34,X35,X36) = k5_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X17] :
      ( v1_partfun1(k6_partfun1(X17),X17)
      & m1_subset_1(k6_partfun1(X17),k1_zfmisc_1(k2_zfmisc_1(X17,X17))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                   => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X4,X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k4_tmap_1(X1,X3),X4)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t97_tmap_1])).

fof(c_0_20,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( v1_funct_1(k5_relat_1(X23,X24))
        | v1_xboole_0(X21)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( v1_funct_2(k5_relat_1(X23,X24),X20,X22)
        | v1_xboole_0(X21)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_funct_2])])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_24,plain,
    ( v1_funct_2(k5_relat_1(X1,X2),X3,X4)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X5,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | v2_struct_0(X46)
      | ~ v2_pre_topc(X46)
      | ~ l1_pre_topc(X46)
      | v2_struct_0(X47)
      | ~ m1_pre_topc(X47,X44)
      | ~ v1_funct_1(X48)
      | ~ v1_funct_2(X48,u1_struct_0(X44),u1_struct_0(X45))
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
      | ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,u1_struct_0(X45),u1_struct_0(X46))
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X46))))
      | r2_funct_2(u1_struct_0(X47),u1_struct_0(X46),k2_tmap_1(X44,X46,k1_partfun1(u1_struct_0(X44),u1_struct_0(X45),u1_struct_0(X45),u1_struct_0(X46),X48,X49),X47),k1_partfun1(u1_struct_0(X47),u1_struct_0(X45),u1_struct_0(X45),u1_struct_0(X46),k2_tmap_1(X44,X45,X48,X47),X49)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_tmap_1])])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(k5_relat_1(X1,k6_partfun1(X2)),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | v1_funct_2(k5_relat_1(X2,k6_partfun1(X1)),X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_2(k6_partfun1(X1),X1,X1)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(k6_partfun1(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X7] :
      ( ~ l1_struct_0(X7)
      | k3_struct_0(X7) = k6_partfun1(u1_struct_0(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_struct_0])])).

fof(c_0_33,plain,(
    ! [X10] :
      ( ( v1_funct_1(k3_struct_0(X10))
        | ~ l1_struct_0(X10) )
      & ( v1_funct_2(k3_struct_0(X10),u1_struct_0(X10),u1_struct_0(X10))
        | ~ l1_struct_0(X10) )
      & ( m1_subset_1(k3_struct_0(X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X10))))
        | ~ l1_struct_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_struct_0])])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | v1_funct_1(k5_relat_1(X2,k6_partfun1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_2(k6_partfun1(X1),X1,X1)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(k6_partfun1(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X5,X6),X4),k1_partfun1(u1_struct_0(X4),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),k2_tmap_1(X1,X2,X5,X4),X6))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,k6_partfun1(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_40,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_funct_2(k5_relat_1(esk4_0,k6_partfun1(u1_struct_0(esk2_0))),u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(esk2_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_30]),c_0_31])])).

cnf(c_0_42,plain,
    ( k3_struct_0(X1) = k6_partfun1(u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( v1_funct_1(k3_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_funct_1(k5_relat_1(esk4_0,k6_partfun1(u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(esk2_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_30]),c_0_31])])).

cnf(c_0_46,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,k1_partfun1(u1_struct_0(X3),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(X2),X4,k5_relat_1(esk4_0,k6_partfun1(u1_struct_0(X2)))),X1),k1_partfun1(u1_struct_0(X1),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(X2),k2_tmap_1(X3,esk1_0,X4,X1),k5_relat_1(esk4_0,k6_partfun1(u1_struct_0(X2)))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk1_0))))
    | ~ v1_funct_2(k5_relat_1(esk4_0,k6_partfun1(u1_struct_0(X2))),u1_struct_0(esk1_0),u1_struct_0(X2))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k5_relat_1(esk4_0,k6_partfun1(u1_struct_0(X2))))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_funct_2(k5_relat_1(esk4_0,k3_struct_0(esk2_0)),u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_funct_1(k5_relat_1(esk4_0,k3_struct_0(esk2_0)))
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,k1_partfun1(u1_struct_0(X3),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(X2),X4,k5_relat_1(esk4_0,k3_struct_0(X2))),X1),k1_partfun1(u1_struct_0(X1),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(X2),k2_tmap_1(X3,esk1_0,X4,X1),k5_relat_1(esk4_0,k3_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk1_0))))
    | ~ v1_funct_2(k5_relat_1(esk4_0,k3_struct_0(X2)),u1_struct_0(esk1_0),u1_struct_0(X2))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k5_relat_1(esk4_0,k3_struct_0(X2)))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_42]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_funct_2(k5_relat_1(esk4_0,k3_struct_0(esk2_0)),u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_47]),c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_funct_1(k5_relat_1(esk4_0,k3_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_47]),c_0_49])])).

cnf(c_0_56,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(X2,esk2_0,k1_partfun1(u1_struct_0(X2),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),X3,k5_relat_1(esk4_0,k3_struct_0(esk2_0))),X1),k1_partfun1(u1_struct_0(X1),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tmap_1(X2,esk1_0,X3,X1),k5_relat_1(esk4_0,k3_struct_0(esk2_0))))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk1_0))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_49]),c_0_53])]),c_0_54]),c_0_55])).

cnf(c_0_57,plain,
    ( m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_58,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | k4_tmap_1(X8,X9) = k2_tmap_1(X8,X8,k3_struct_0(X8),X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_tmap_1])])])])).

cnf(c_0_59,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k3_struct_0(esk1_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))),X1),k1_partfun1(u1_struct_0(X1),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),X1),k5_relat_1(esk4_0,k3_struct_0(esk2_0))))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_37]),c_0_38])]),c_0_39]),c_0_43]),c_0_44])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | k4_tmap_1(X1,X2) = k2_tmap_1(X1,X1,k3_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k3_struct_0(esk1_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))),X1),k1_partfun1(u1_struct_0(X1),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),X1),k5_relat_1(esk4_0,k3_struct_0(esk2_0))))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_47]),c_0_37])])).

cnf(c_0_63,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),esk3_0) = k4_tmap_1(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_65,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ~ v1_funct_1(X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ v1_funct_1(X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k1_partfun1(X25,X26,X27,X28,X29,X30) = k5_relat_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_66,plain,(
    ! [X37,X38,X39,X40] :
      ( ( ~ r2_relset_1(X37,X38,X39,X40)
        | X39 = X40
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X39 != X40
        | r2_relset_1(X37,X38,X39,X40)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_67,plain,(
    ! [X41,X42,X43] :
      ( ( r2_relset_1(X41,X42,k4_relset_1(X41,X41,X41,X42,k6_partfun1(X41),X43),X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( r2_relset_1(X41,X42,k4_relset_1(X41,X42,X42,X42,X43,k6_partfun1(X42)),X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).

cnf(c_0_68,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k3_struct_0(esk1_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))),esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_63]),c_0_64])).

cnf(c_0_69,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,k5_relat_1(k3_struct_0(esk1_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))),esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,k3_struct_0(esk2_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k3_struct_0(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))
    | ~ v1_funct_1(k3_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_55])).

cnf(c_0_73,plain,
    ( k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)) = X3
    | ~ m1_subset_1(k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,k5_relat_1(k3_struct_0(esk1_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))),esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,k3_struct_0(esk2_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_43]),c_0_57])).

cnf(c_0_75,plain,
    ( k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_16]),c_0_22])])).

cnf(c_0_76,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,k5_relat_1(k3_struct_0(esk1_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))),esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,k3_struct_0(esk2_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_47]),c_0_37])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,k3_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_42])).

cnf(c_0_79,plain,
    ( k5_relat_1(X1,k6_partfun1(X2)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_75]),c_0_22])])).

cnf(c_0_80,plain,
    ( k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3) = X3
    | ~ m1_subset_1(k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,k5_relat_1(k3_struct_0(esk1_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))),esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_partfun1(u1_struct_0(esk2_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_28])).

cnf(c_0_83,plain,
    ( k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_16]),c_0_22])])).

cnf(c_0_84,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,k5_relat_1(k3_struct_0(esk1_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))),esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),k5_relat_1(esk4_0,k3_struct_0(esk2_0))))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_47]),c_0_49])])).

cnf(c_0_85,negated_conjecture,
    ( k5_relat_1(esk4_0,k3_struct_0(esk2_0)) = esk4_0
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_42])).

cnf(c_0_86,plain,
    ( k5_relat_1(k6_partfun1(X1),X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_83]),c_0_22])])).

cnf(c_0_87,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,k5_relat_1(k3_struct_0(esk1_0),esk4_0),esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( k5_relat_1(k6_partfun1(u1_struct_0(esk1_0)),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_28])).

fof(c_0_89,plain,(
    ! [X19] :
      ( v2_struct_0(X19)
      | ~ l1_struct_0(X19)
      | ~ v1_xboole_0(u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_90,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,k5_relat_1(k3_struct_0(esk1_0),esk4_0),esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_47]),c_0_49])])).

cnf(c_0_91,negated_conjecture,
    ( k5_relat_1(k3_struct_0(esk1_0),esk4_0) = esk4_0
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_42])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_93,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_54])).

cnf(c_0_96,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_47]),c_0_49])])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_47]),c_0_37])]),
    [proof]).

%------------------------------------------------------------------------------
