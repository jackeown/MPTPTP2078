%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:18 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 223 expanded)
%              Number of clauses        :   47 (  83 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  277 (1662 expanded)
%              Number of equality atoms :   47 ( 185 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t60_tmap_1,conjecture,(
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
                & m1_pre_topc(X3,X2) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,k2_tmap_1(X2,X1,X4,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

fof(d4_tmap_1,axiom,(
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
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

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

fof(c_0_13,plain,(
    ! [X26,X27,X28,X29] :
      ( ( X26 = X28
        | g1_pre_topc(X26,X27) != g1_pre_topc(X28,X29)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) )
      & ( X27 = X29
        | g1_pre_topc(X26,X27) != g1_pre_topc(X28,X29)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_14,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | m1_subset_1(u1_pre_topc(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_15,negated_conjecture,(
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
                  & m1_pre_topc(X3,X2) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                   => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,k2_tmap_1(X2,X1,X4,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t60_tmap_1])).

cnf(c_0_16,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    & g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_19,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X36,X37,X38,X39] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
      | ~ m1_pre_topc(X39,X36)
      | k2_tmap_1(X36,X37,X38,X39) = k2_partfun1(u1_struct_0(X36),u1_struct_0(X37),X38,u1_struct_0(X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_22,negated_conjecture,
    ( u1_pre_topc(X1) = u1_pre_topc(esk3_0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ v1_funct_1(X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k2_partfun1(X19,X20,X21,X22) = k7_relat_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( u1_pre_topc(esk3_0) = u1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23])])).

fof(c_0_36,plain,(
    ! [X14,X15,X16] :
      ( ( v1_funct_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | v1_xboole_0(X15) )
      & ( v1_partfun1(X16,X14)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_37,plain,(
    ! [X11,X12,X13] :
      ( ( v4_relat_1(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( v5_relat_1(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_38,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_relat_1(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_39,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_23]),c_0_30]),c_0_31])]),c_0_32]),c_0_33])).

cnf(c_0_41,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk2_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_35])).

fof(c_0_43,plain,(
    ! [X17,X18] :
      ( ( ~ v1_partfun1(X18,X17)
        | k1_relat_1(X18) = X17
        | ~ v1_relat_1(X18)
        | ~ v4_relat_1(X18,X17) )
      & ( k1_relat_1(X18) != X17
        | v1_partfun1(X18,X17)
        | ~ v1_relat_1(X18)
        | ~ v4_relat_1(X18,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_44,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_47,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r1_funct_2(X30,X31,X32,X33,X34,X35)
        | X34 = X35
        | v1_xboole_0(X31)
        | v1_xboole_0(X33)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X30,X31)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X34 != X35
        | r1_funct_2(X30,X31,X32,X33,X34,X35)
        | v1_xboole_0(X31)
        | v1_xboole_0(X33)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X30,X31)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( k2_tmap_1(esk2_0,esk1_0,esk4_0,X1) = k7_relat_1(esk4_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_31]),c_0_26])])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk3_0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_52,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k7_relat_1(X7,k1_relat_1(X7)) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_53,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v1_partfun1(esk4_0,u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_26]),c_0_30]),c_0_31])])).

cnf(c_0_55,negated_conjecture,
    ( v4_relat_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_26])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_26])).

cnf(c_0_57,plain,
    ( r1_funct_2(X3,X4,X5,X6,X1,X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X6)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X5,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k7_relat_1(esk4_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_23])])).

cnf(c_0_60,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(esk2_0)
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])])).

fof(c_0_62,plain,(
    ! [X25] :
      ( v2_struct_0(X25)
      | ~ l1_struct_0(X25)
      | ~ v1_xboole_0(u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_63,plain,(
    ! [X23] :
      ( ~ l1_pre_topc(X23)
      | l1_struct_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_64,plain,
    ( r1_funct_2(X1,X2,X3,X4,X5,X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X5,X3,X4)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,k7_relat_1(esk4_0,u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k7_relat_1(esk4_0,u1_struct_0(esk2_0)) = esk4_0
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_56])])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | v1_xboole_0(X2)
    | ~ v1_funct_2(esk4_0,X1,X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_26]),c_0_30]),c_0_31])])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_26]),c_0_30])]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_29])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:55:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.20/0.39  # and selection function PSelectComplexExceptRRHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.20/0.39  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.20/0.39  fof(t60_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>r1_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,k2_tmap_1(X2,X1,X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 0.20/0.39  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.39  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.20/0.39  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.39  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.20/0.39  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.20/0.39  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.20/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.39  fof(c_0_13, plain, ![X26, X27, X28, X29]:((X26=X28|g1_pre_topc(X26,X27)!=g1_pre_topc(X28,X29)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))))&(X27=X29|g1_pre_topc(X26,X27)!=g1_pre_topc(X28,X29)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.20/0.39  fof(c_0_14, plain, ![X24]:(~l1_pre_topc(X24)|m1_subset_1(u1_pre_topc(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.20/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>r1_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,k2_tmap_1(X2,X1,X4,X3)))))))), inference(assume_negation,[status(cth)],[t60_tmap_1])).
% 0.20/0.39  cnf(c_0_16, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_17, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  fof(c_0_18, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))))&(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))&~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.39  cnf(c_0_19, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  fof(c_0_21, plain, ![X36, X37, X38, X39]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))|(~m1_pre_topc(X39,X36)|k2_tmap_1(X36,X37,X38,X39)=k2_partfun1(u1_struct_0(X36),u1_struct_0(X37),X38,u1_struct_0(X39)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (u1_pre_topc(X1)=u1_pre_topc(esk3_0)|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  fof(c_0_24, plain, ![X19, X20, X21, X22]:(~v1_funct_1(X21)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k2_partfun1(X19,X20,X21,X22)=k7_relat_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.20/0.39  cnf(c_0_25, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_34, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (u1_pre_topc(esk3_0)=u1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_23])])).
% 0.20/0.39  fof(c_0_36, plain, ![X14, X15, X16]:((v1_funct_1(X16)|(~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|v1_xboole_0(X15))&(v1_partfun1(X16,X14)|(~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|v1_xboole_0(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.39  fof(c_0_37, plain, ![X11, X12, X13]:((v4_relat_1(X13,X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))&(v5_relat_1(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.39  fof(c_0_38, plain, ![X8, X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|v1_relat_1(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.39  cnf(c_0_39, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1))=k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_23]), c_0_30]), c_0_31])]), c_0_32]), c_0_33])).
% 0.20/0.39  cnf(c_0_41, plain, (u1_struct_0(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X2,X3)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_17])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk2_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(rw,[status(thm)],[c_0_20, c_0_35])).
% 0.20/0.39  fof(c_0_43, plain, ![X17, X18]:((~v1_partfun1(X18,X17)|k1_relat_1(X18)=X17|(~v1_relat_1(X18)|~v4_relat_1(X18,X17)))&(k1_relat_1(X18)!=X17|v1_partfun1(X18,X17)|(~v1_relat_1(X18)|~v4_relat_1(X18,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.20/0.39  cnf(c_0_44, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_45, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_46, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  fof(c_0_47, plain, ![X30, X31, X32, X33, X34, X35]:((~r1_funct_2(X30,X31,X32,X33,X34,X35)|X34=X35|(v1_xboole_0(X31)|v1_xboole_0(X33)|~v1_funct_1(X34)|~v1_funct_2(X34,X30,X31)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(X34!=X35|r1_funct_2(X30,X31,X32,X33,X34,X35)|(v1_xboole_0(X31)|v1_xboole_0(X33)|~v1_funct_1(X34)|~v1_funct_2(X34,X30,X31)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)=k7_relat_1(esk4_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_31]), c_0_26])])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(esk3_0)|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.39  fof(c_0_52, plain, ![X7]:(~v1_relat_1(X7)|k7_relat_1(X7,k1_relat_1(X7))=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.20/0.39  cnf(c_0_53, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (v1_partfun1(esk4_0,u1_struct_0(esk2_0))|v1_xboole_0(u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_26]), c_0_30]), c_0_31])])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (v4_relat_1(esk4_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_26])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_26])).
% 0.20/0.39  cnf(c_0_57, plain, (r1_funct_2(X3,X4,X5,X6,X1,X2)|v1_xboole_0(X4)|v1_xboole_0(X6)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X6)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k7_relat_1(esk4_0,u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_51]), c_0_23])])).
% 0.20/0.39  cnf(c_0_60, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(esk2_0)|v1_xboole_0(u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])])).
% 0.20/0.39  fof(c_0_62, plain, ![X25]:(v2_struct_0(X25)|~l1_struct_0(X25)|~v1_xboole_0(u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.39  fof(c_0_63, plain, ![X23]:(~l1_pre_topc(X23)|l1_struct_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.39  cnf(c_0_64, plain, (r1_funct_2(X1,X2,X3,X4,X5,X5)|v1_xboole_0(X4)|v1_xboole_0(X2)|~v1_funct_2(X5,X3,X4)|~v1_funct_2(X5,X1,X2)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_57])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,k7_relat_1(esk4_0,u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (k7_relat_1(esk4_0,u1_struct_0(esk2_0))=esk4_0|v1_xboole_0(u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_56])])).
% 0.20/0.39  cnf(c_0_67, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.39  cnf(c_0_68, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk4_0)|v1_xboole_0(u1_struct_0(esk1_0))|v1_xboole_0(X2)|~v1_funct_2(esk4_0,X1,X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_26]), c_0_30]), c_0_31])])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.39  cnf(c_0_71, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_26]), c_0_30])]), c_0_70])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_29])]), c_0_32]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 74
% 0.20/0.39  # Proof object clause steps            : 47
% 0.20/0.39  # Proof object formula steps           : 27
% 0.20/0.39  # Proof object conjectures             : 33
% 0.20/0.39  # Proof object clause conjectures      : 30
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 25
% 0.20/0.39  # Proof object initial formulas used   : 13
% 0.20/0.39  # Proof object generating inferences   : 19
% 0.20/0.39  # Proof object simplifying inferences  : 39
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 13
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 30
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 29
% 0.20/0.39  # Processed clauses                    : 112
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 18
% 0.20/0.39  # ...remaining for further processing  : 94
% 0.20/0.39  # Other redundant clauses eliminated   : 1
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 15
% 0.20/0.39  # Generated clauses                    : 53
% 0.20/0.39  # ...of the previous two non-trivial   : 57
% 0.20/0.39  # Contextual simplify-reflections      : 1
% 0.20/0.39  # Paramodulations                      : 46
% 0.20/0.39  # Factorizations                       : 2
% 0.20/0.39  # Equation resolutions                 : 5
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 49
% 0.20/0.39  #    Positive orientable unit clauses  : 16
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 4
% 0.20/0.39  #    Non-unit-clauses                  : 29
% 0.20/0.39  # Current number of unprocessed clauses: 3
% 0.20/0.39  # ...number of literals in the above   : 24
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 44
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1226
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 209
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 18
% 0.20/0.39  # Unit Clause-clause subsumption calls : 14
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 8
% 0.20/0.39  # BW rewrite match successes           : 4
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 4235
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.034 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.039 s
% 0.20/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
