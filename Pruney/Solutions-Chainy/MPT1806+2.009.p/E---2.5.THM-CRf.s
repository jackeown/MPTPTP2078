%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:30 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  114 (2537 expanded)
%              Number of clauses        :   85 ( 870 expanded)
%              Number of leaves         :   14 ( 633 expanded)
%              Depth                    :   17
%              Number of atoms          :  641 (25503 expanded)
%              Number of equality atoms :   60 ( 697 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t122_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( v1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X1) )
          <=> ( v1_funct_1(k9_tmap_1(X1,X2))
              & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
              & v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2))
              & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_tmap_1)).

fof(d11_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = k8_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => X3 = k6_tmap_1(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(d1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tsep_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(d12_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) )
             => ( X3 = k9_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).

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

fof(t113_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ( v1_funct_1(k7_tmap_1(X1,X2))
              & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
              & v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
              & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

fof(c_0_14,plain,(
    ! [X36,X37] :
      ( ( u1_struct_0(k6_tmap_1(X36,X37)) = u1_struct_0(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( u1_pre_topc(k6_tmap_1(X36,X37)) = k5_tmap_1(X36,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_15,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_pre_topc(X41,X40)
      | m1_subset_1(u1_struct_0(X41),k1_zfmisc_1(u1_struct_0(X40))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ( ( v1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X1) )
            <=> ( v1_funct_1(k9_tmap_1(X1,X2))
                & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
                & v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2))
                & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t122_tmap_1])).

fof(c_0_17,plain,(
    ! [X16,X17,X18,X19] :
      ( ( X18 != k8_tmap_1(X16,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | X19 != u1_struct_0(X17)
        | X18 = k6_tmap_1(X16,X19)
        | ~ v1_pre_topc(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))
        | X18 = k8_tmap_1(X16,X17)
        | ~ v1_pre_topc(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( esk1_3(X16,X17,X18) = u1_struct_0(X17)
        | X18 = k8_tmap_1(X16,X17)
        | ~ v1_pre_topc(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( X18 != k6_tmap_1(X16,esk1_3(X16,X17,X18))
        | X18 = k8_tmap_1(X16,X17)
        | ~ v1_pre_topc(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_18,plain,(
    ! [X8] :
      ( ~ v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_19,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_20,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & ( ~ v1_tsep_1(esk5_0,esk4_0)
      | ~ m1_pre_topc(esk5_0,esk4_0)
      | ~ v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
      | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
      | ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
      | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) )
    & ( v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
      | v1_tsep_1(esk5_0,esk4_0) )
    & ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
      | v1_tsep_1(esk5_0,esk4_0) )
    & ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
      | v1_tsep_1(esk5_0,esk4_0) )
    & ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))
      | v1_tsep_1(esk5_0,esk4_0) )
    & ( v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
      | m1_pre_topc(esk5_0,esk4_0) )
    & ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
      | m1_pre_topc(esk5_0,esk4_0) )
    & ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
      | m1_pre_topc(esk5_0,esk4_0) )
    & ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))
      | m1_pre_topc(esk5_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

cnf(c_0_23,plain,
    ( X1 = k6_tmap_1(X2,X4)
    | v2_struct_0(X2)
    | X1 != k8_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X32,X33] :
      ( ( v1_pre_topc(k8_tmap_1(X32,X33))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ m1_pre_topc(X33,X32) )
      & ( v2_pre_topc(k8_tmap_1(X32,X33))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ m1_pre_topc(X33,X32) )
      & ( l1_pre_topc(k8_tmap_1(X32,X33))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ m1_pre_topc(X33,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_25,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( X1 = k6_tmap_1(X2,u1_struct_0(X3))
    | v2_struct_0(X2)
    | u1_struct_0(X3) != u1_struct_0(X4)
    | X1 != k8_tmap_1(X2,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_33,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X26,X27,X28] :
      ( ( ~ v1_tsep_1(X27,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | X28 != u1_struct_0(X27)
        | v3_pre_topc(X28,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk3_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v1_tsep_1(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) )
      & ( esk3_2(X26,X27) = u1_struct_0(X27)
        | v1_tsep_1(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ v3_pre_topc(esk3_2(X26,X27),X26)
        | v1_tsep_1(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

fof(c_0_37,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ l1_struct_0(X9)
      | ~ v1_xboole_0(u1_struct_0(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_38,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_40,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X3))
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33]),c_0_34]),c_0_35])).

fof(c_0_41,plain,(
    ! [X34,X35] :
      ( ( v1_funct_1(k9_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X34) )
      & ( v1_funct_2(k9_tmap_1(X34,X35),u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X34) )
      & ( m1_subset_1(k9_tmap_1(X34,X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

fof(c_0_42,plain,(
    ! [X30,X31] :
      ( ( v1_funct_1(k7_tmap_1(X30,X31))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) )
      & ( v1_funct_2(k7_tmap_1(X30,X31),u1_struct_0(X30),u1_struct_0(k6_tmap_1(X30,X31)))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) )
      & ( m1_subset_1(k7_tmap_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(k6_tmap_1(X30,X31)))))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v2_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(X1)) = k8_tmap_1(esk4_0,esk5_0)
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

fof(c_0_48,plain,(
    ! [X21,X22,X23,X24] :
      ( ( X23 != k9_tmap_1(X21,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | X24 != u1_struct_0(X22)
        | r1_funct_2(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)),u1_struct_0(X21),u1_struct_0(k6_tmap_1(X21,X24)),X23,k7_tmap_1(X21,X24))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))))
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk2_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))
        | X23 = k9_tmap_1(X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))))
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( esk2_3(X21,X22,X23) = u1_struct_0(X22)
        | X23 = k9_tmap_1(X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))))
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_funct_2(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)),u1_struct_0(X21),u1_struct_0(k6_tmap_1(X21,esk2_3(X21,X22,X23))),X23,k7_tmap_1(X21,esk2_3(X21,X22,X23)))
        | X23 = k9_tmap_1(X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))))
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

cnf(c_0_49,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_52,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r1_funct_2(X10,X11,X12,X13,X14,X15)
        | X14 = X15
        | v1_xboole_0(X11)
        | v1_xboole_0(X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X10,X11)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X12,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( X14 != X15
        | r1_funct_2(X10,X11,X12,X13,X14,X15)
        | v1_xboole_0(X11)
        | v1_xboole_0(X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X10,X11)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X12,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_53,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_28]),c_0_30])])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v2_struct_0(k8_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_28])])).

cnf(c_0_57,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,plain,
    ( r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))
    | v2_struct_0(X2)
    | X1 != k9_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_62,plain,
    ( X5 = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ r1_funct_2(X1,X2,X3,X4,X5,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | m1_subset_1(k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))) = u1_struct_0(esk4_0)
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_54]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_39])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_30])]),c_0_31])).

cnf(c_0_67,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_68,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | v1_funct_2(k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_54]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_69,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1))
    | X1 != u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_28]),c_0_29]),c_0_60]),c_0_61]),c_0_30])]),c_0_31])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk4_0,esk5_0)) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_46]),c_0_28])])).

cnf(c_0_71,plain,
    ( esk3_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_72,plain,(
    ! [X38,X39] :
      ( ( v1_funct_1(k7_tmap_1(X38,X39))
        | ~ v3_pre_topc(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( v1_funct_2(k7_tmap_1(X38,X39),u1_struct_0(X38),u1_struct_0(k6_tmap_1(X38,X39)))
        | ~ v3_pre_topc(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( v5_pre_topc(k7_tmap_1(X38,X39),X38,k6_tmap_1(X38,X39))
        | ~ v3_pre_topc(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_subset_1(k7_tmap_1(X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(k6_tmap_1(X38,X39)))))
        | ~ v3_pre_topc(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ v1_funct_1(k7_tmap_1(X38,X39))
        | ~ v1_funct_2(k7_tmap_1(X38,X39),u1_struct_0(X38),u1_struct_0(k6_tmap_1(X38,X39)))
        | ~ v5_pre_topc(k7_tmap_1(X38,X39),X38,k6_tmap_1(X38,X39))
        | ~ m1_subset_1(k7_tmap_1(X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(k6_tmap_1(X38,X39)))))
        | v3_pre_topc(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).

cnf(c_0_73,plain,
    ( X1 = X2
    | v1_xboole_0(X3)
    | ~ r1_funct_2(X4,X3,X5,X3,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ v1_funct_2(X2,X5,X3)
    | ~ v1_funct_2(X1,X4,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(ef,[status(thm)],[c_0_62])).

cnf(c_0_74,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | m1_subset_1(k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_46]),c_0_47]),c_0_28])]),c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | v1_funct_1(k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_54]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_77,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | v1_funct_2(k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1))
    | X1 != u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( esk3_2(esk4_0,esk5_0) = u1_struct_0(esk5_0)
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_28]),c_0_30])])).

cnf(c_0_80,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X2))
    | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( X1 = k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))
    | v1_tsep_1(esk5_0,esk4_0)
    | ~ r1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),X1,k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk4_0))))
    | ~ v1_funct_2(X1,X2,u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_64]),c_0_54]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_70])).

cnf(c_0_85,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_80,c_0_67]),c_0_57]),c_0_53])).

cnf(c_0_86,negated_conjecture,
    ( k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)) = k9_tmap_1(esk4_0,esk5_0)
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_84]),c_0_61])])).

cnf(c_0_87,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_88,negated_conjecture,
    ( v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)
    | v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_29]),c_0_30])]),c_0_31]),c_0_54])).

cnf(c_0_89,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_79]),c_0_28]),c_0_30])])).

cnf(c_0_90,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_91,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_79]),c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_93,plain,
    ( m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_21])).

cnf(c_0_94,plain,
    ( v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_21])).

cnf(c_0_95,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_21])).

cnf(c_0_96,negated_conjecture,
    ( ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ m1_pre_topc(esk5_0,esk4_0)
    | ~ v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
    | ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_97,plain,
    ( v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_98,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_21])).

cnf(c_0_99,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_46]),c_0_28])]),c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_28]),c_0_39]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_101,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_28]),c_0_39]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_103,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_28])]),c_0_61])])).

cnf(c_0_104,plain,
    ( v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_21])).

cnf(c_0_105,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk4_0)
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_28]),c_0_30])])).

cnf(c_0_106,negated_conjecture,
    ( X1 = k7_tmap_1(esk4_0,u1_struct_0(esk5_0))
    | ~ r1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),X1,k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk4_0))))
    | ~ v1_funct_2(X1,X2,u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_100]),c_0_101]),c_0_102])]),c_0_75])).

cnf(c_0_107,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_39])).

cnf(c_0_108,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_60])]),c_0_59])])).

cnf(c_0_109,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_46]),c_0_29]),c_0_30])]),c_0_31]),c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_83]),c_0_84]),c_0_61])])).

cnf(c_0_111,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_99])])).

cnf(c_0_112,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_28])]),c_0_111])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_21]),c_0_28]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.44  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.042 s
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.19/0.44  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.44  fof(t122_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t122_tmap_1)).
% 0.19/0.44  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.19/0.44  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.19/0.44  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.44  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.19/0.44  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.19/0.44  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.44  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.19/0.44  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.19/0.44  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.19/0.44  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.19/0.44  fof(t113_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.19/0.44  fof(c_0_14, plain, ![X36, X37]:((u1_struct_0(k6_tmap_1(X36,X37))=u1_struct_0(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(u1_pre_topc(k6_tmap_1(X36,X37))=k5_tmap_1(X36,X37)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.19/0.44  fof(c_0_15, plain, ![X40, X41]:(~l1_pre_topc(X40)|(~m1_pre_topc(X41,X40)|m1_subset_1(u1_struct_0(X41),k1_zfmisc_1(u1_struct_0(X40))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.44  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t122_tmap_1])).
% 0.19/0.44  fof(c_0_17, plain, ![X16, X17, X18, X19]:((X18!=k8_tmap_1(X16,X17)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|(X19!=u1_struct_0(X17)|X18=k6_tmap_1(X16,X19)))|(~v1_pre_topc(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))|~m1_pre_topc(X17,X16)|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&((m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))|X18=k8_tmap_1(X16,X17)|(~v1_pre_topc(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))|~m1_pre_topc(X17,X16)|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&((esk1_3(X16,X17,X18)=u1_struct_0(X17)|X18=k8_tmap_1(X16,X17)|(~v1_pre_topc(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))|~m1_pre_topc(X17,X16)|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(X18!=k6_tmap_1(X16,esk1_3(X16,X17,X18))|X18=k8_tmap_1(X16,X17)|(~v1_pre_topc(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))|~m1_pre_topc(X17,X16)|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.19/0.44  fof(c_0_18, plain, ![X8]:(~v2_struct_0(X8)|~l1_struct_0(X8)|v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.19/0.44  fof(c_0_19, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.44  cnf(c_0_20, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  cnf(c_0_21, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  fof(c_0_22, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_pre_topc(esk5_0,esk4_0)&((~v1_tsep_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|(~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))))&(((((v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0))&(v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|v1_tsep_1(esk5_0,esk4_0)))&(v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)))&(m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|v1_tsep_1(esk5_0,esk4_0)))&((((v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|m1_pre_topc(esk5_0,esk4_0))&(v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|m1_pre_topc(esk5_0,esk4_0)))&(v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|m1_pre_topc(esk5_0,esk4_0)))&(m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|m1_pre_topc(esk5_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).
% 0.19/0.44  cnf(c_0_23, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  fof(c_0_24, plain, ![X32, X33]:(((v1_pre_topc(k8_tmap_1(X32,X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|~m1_pre_topc(X33,X32)))&(v2_pre_topc(k8_tmap_1(X32,X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|~m1_pre_topc(X33,X32))))&(l1_pre_topc(k8_tmap_1(X32,X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|~m1_pre_topc(X33,X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.19/0.44  cnf(c_0_25, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_26, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_27, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.44  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  cnf(c_0_32, plain, (X1=k6_tmap_1(X2,u1_struct_0(X3))|v2_struct_0(X2)|u1_struct_0(X3)!=u1_struct_0(X4)|X1!=k8_tmap_1(X2,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.19/0.44  cnf(c_0_33, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_34, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_35, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  fof(c_0_36, plain, ![X26, X27, X28]:((~v1_tsep_1(X27,X26)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(X28!=u1_struct_0(X27)|v3_pre_topc(X28,X26)))|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))&((m1_subset_1(esk3_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))|v1_tsep_1(X27,X26)|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))&((esk3_2(X26,X27)=u1_struct_0(X27)|v1_tsep_1(X27,X26)|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))&(~v3_pre_topc(esk3_2(X26,X27),X26)|v1_tsep_1(X27,X26)|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.19/0.44  fof(c_0_37, plain, ![X9]:(v2_struct_0(X9)|~l1_struct_0(X9)|~v1_xboole_0(u1_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.44  cnf(c_0_38, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, (u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_40, plain, (k8_tmap_1(X1,X2)=k6_tmap_1(X1,u1_struct_0(X3))|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.44  fof(c_0_41, plain, ![X34, X35]:(((v1_funct_1(k9_tmap_1(X34,X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_pre_topc(X35,X34)))&(v1_funct_2(k9_tmap_1(X34,X35),u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_pre_topc(X35,X34))))&(m1_subset_1(k9_tmap_1(X34,X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_pre_topc(X35,X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.19/0.44  fof(c_0_42, plain, ![X30, X31]:(((v1_funct_1(k7_tmap_1(X30,X31))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))))&(v1_funct_2(k7_tmap_1(X30,X31),u1_struct_0(X30),u1_struct_0(k6_tmap_1(X30,X31)))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))))))&(m1_subset_1(k7_tmap_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(k6_tmap_1(X30,X31)))))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.19/0.44  cnf(c_0_43, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.44  cnf(c_0_44, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.44  cnf(c_0_45, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~v2_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))|~l1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(X1))=k8_tmap_1(esk4_0,esk5_0)|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_47, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  fof(c_0_48, plain, ![X21, X22, X23, X24]:((X23!=k9_tmap_1(X21,X22)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|(X24!=u1_struct_0(X22)|r1_funct_2(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)),u1_struct_0(X21),u1_struct_0(k6_tmap_1(X21,X24)),X23,k7_tmap_1(X21,X24))))|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22))))))|~m1_pre_topc(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&((m1_subset_1(esk2_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))|X23=k9_tmap_1(X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22))))))|~m1_pre_topc(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&((esk2_3(X21,X22,X23)=u1_struct_0(X22)|X23=k9_tmap_1(X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22))))))|~m1_pre_topc(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~r1_funct_2(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)),u1_struct_0(X21),u1_struct_0(k6_tmap_1(X21,esk2_3(X21,X22,X23))),X23,k7_tmap_1(X21,esk2_3(X21,X22,X23)))|X23=k9_tmap_1(X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22)))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(k8_tmap_1(X21,X22))))))|~m1_pre_topc(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.19/0.44  cnf(c_0_49, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.44  cnf(c_0_50, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.44  cnf(c_0_51, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.44  fof(c_0_52, plain, ![X10, X11, X12, X13, X14, X15]:((~r1_funct_2(X10,X11,X12,X13,X14,X15)|X14=X15|(v1_xboole_0(X11)|v1_xboole_0(X13)|~v1_funct_1(X14)|~v1_funct_2(X14,X10,X11)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|~v1_funct_1(X15)|~v1_funct_2(X15,X12,X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))))&(X14!=X15|r1_funct_2(X10,X11,X12,X13,X14,X15)|(v1_xboole_0(X11)|v1_xboole_0(X13)|~v1_funct_1(X14)|~v1_funct_2(X14,X10,X11)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|~v1_funct_1(X15)|~v1_funct_2(X15,X12,X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.19/0.44  cnf(c_0_53, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.44  cnf(c_0_54, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_28]), c_0_30])])).
% 0.19/0.44  cnf(c_0_55, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 0.19/0.44  cnf(c_0_56, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~v2_struct_0(k8_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_28])])).
% 0.19/0.44  cnf(c_0_57, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.44  cnf(c_0_58, plain, (r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))|v2_struct_0(X2)|X1!=k9_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.44  cnf(c_0_59, negated_conjecture, (m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_60, negated_conjecture, (v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (v1_funct_1(k9_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_62, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.44  cnf(c_0_63, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|m1_subset_1(k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_64, negated_conjecture, (u1_struct_0(k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))=u1_struct_0(esk4_0)|v1_tsep_1(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_54]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (v2_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))|~v1_xboole_0(u1_struct_0(esk4_0))|~l1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_55, c_0_39])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (~v2_struct_0(k8_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_67, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.44  cnf(c_0_68, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|v1_funct_2(k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_54]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_69, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1))|X1!=u1_struct_0(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_28]), c_0_29]), c_0_60]), c_0_61]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_70, negated_conjecture, (u1_struct_0(k8_tmap_1(esk4_0,esk5_0))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_46]), c_0_28])])).
% 0.19/0.44  cnf(c_0_71, plain, (esk3_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.44  fof(c_0_72, plain, ![X38, X39]:(((((v1_funct_1(k7_tmap_1(X38,X39))|~v3_pre_topc(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(v1_funct_2(k7_tmap_1(X38,X39),u1_struct_0(X38),u1_struct_0(k6_tmap_1(X38,X39)))|~v3_pre_topc(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))&(v5_pre_topc(k7_tmap_1(X38,X39),X38,k6_tmap_1(X38,X39))|~v3_pre_topc(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))&(m1_subset_1(k7_tmap_1(X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(k6_tmap_1(X38,X39)))))|~v3_pre_topc(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))&(~v1_funct_1(k7_tmap_1(X38,X39))|~v1_funct_2(k7_tmap_1(X38,X39),u1_struct_0(X38),u1_struct_0(k6_tmap_1(X38,X39)))|~v5_pre_topc(k7_tmap_1(X38,X39),X38,k6_tmap_1(X38,X39))|~m1_subset_1(k7_tmap_1(X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(k6_tmap_1(X38,X39)))))|v3_pre_topc(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).
% 0.19/0.44  cnf(c_0_73, plain, (X1=X2|v1_xboole_0(X3)|~r1_funct_2(X4,X3,X5,X3,X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~v1_funct_2(X2,X5,X3)|~v1_funct_2(X1,X4,X3)|~v1_funct_1(X2)|~v1_funct_1(X1)), inference(ef,[status(thm)],[c_0_62])).
% 0.19/0.44  cnf(c_0_74, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|m1_subset_1(k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.44  cnf(c_0_75, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_46]), c_0_47]), c_0_28])]), c_0_66])).
% 0.19/0.44  cnf(c_0_76, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|v1_funct_1(k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_54]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_77, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|v1_funct_2(k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_68, c_0_64])).
% 0.19/0.44  cnf(c_0_78, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1))|X1!=u1_struct_0(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.44  cnf(c_0_79, negated_conjecture, (esk3_2(esk4_0,esk5_0)=u1_struct_0(esk5_0)|v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_28]), c_0_30])])).
% 0.19/0.44  cnf(c_0_80, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|~v1_funct_1(k7_tmap_1(X1,X2))|~v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|~v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|~m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.44  cnf(c_0_81, negated_conjecture, (X1=k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)|~r1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),X1,k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk4_0))))|~v1_funct_2(X1,X2,u1_struct_0(esk4_0))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76]), c_0_77])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_64]), c_0_54]), c_0_79])).
% 0.19/0.44  cnf(c_0_83, negated_conjecture, (m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_59, c_0_70])).
% 0.19/0.44  cnf(c_0_84, negated_conjecture, (v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_60, c_0_70])).
% 0.19/0.44  cnf(c_0_85, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_80, c_0_67]), c_0_57]), c_0_53])).
% 0.19/0.44  cnf(c_0_86, negated_conjecture, (k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))=k9_tmap_1(esk4_0,esk5_0)|v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83]), c_0_84]), c_0_61])])).
% 0.19/0.44  cnf(c_0_87, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk3_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.44  cnf(c_0_88, negated_conjecture, (v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)|v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_29]), c_0_30])]), c_0_31]), c_0_54])).
% 0.19/0.44  cnf(c_0_89, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_79]), c_0_28]), c_0_30])])).
% 0.19/0.44  cnf(c_0_90, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.44  cnf(c_0_91, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_79]), c_0_89])).
% 0.19/0.44  cnf(c_0_92, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  cnf(c_0_93, plain, (m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_53, c_0_21])).
% 0.19/0.44  cnf(c_0_94, plain, (v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_57, c_0_21])).
% 0.19/0.44  cnf(c_0_95, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_67, c_0_21])).
% 0.19/0.44  cnf(c_0_96, negated_conjecture, (~v1_tsep_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  cnf(c_0_97, plain, (v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.44  cnf(c_0_98, plain, (v3_pre_topc(u1_struct_0(X1),X2)|u1_struct_0(X1)!=u1_struct_0(X3)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_90, c_0_21])).
% 0.19/0.44  cnf(c_0_99, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_46]), c_0_28])]), c_0_92])).
% 0.19/0.44  cnf(c_0_100, negated_conjecture, (m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_28]), c_0_39]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_101, negated_conjecture, (v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_28]), c_0_39]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_102, negated_conjecture, (v1_funct_1(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.44  cnf(c_0_103, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_28])]), c_0_61])])).
% 0.19/0.44  cnf(c_0_104, plain, (v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_97, c_0_21])).
% 0.19/0.44  cnf(c_0_105, negated_conjecture, (v3_pre_topc(u1_struct_0(X1),esk4_0)|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_28]), c_0_30])])).
% 0.19/0.44  cnf(c_0_106, negated_conjecture, (X1=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))|~r1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),X1,k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk4_0))))|~v1_funct_2(X1,X2,u1_struct_0(esk4_0))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_100]), c_0_101]), c_0_102])]), c_0_75])).
% 0.19/0.44  cnf(c_0_107, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))|~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_78, c_0_39])).
% 0.19/0.44  cnf(c_0_108, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_60])]), c_0_59])])).
% 0.19/0.44  cnf(c_0_109, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k8_tmap_1(esk4_0,esk5_0))|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_46]), c_0_29]), c_0_30])]), c_0_31]), c_0_105])).
% 0.19/0.44  cnf(c_0_110, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k9_tmap_1(esk4_0,esk5_0)|~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_83]), c_0_84]), c_0_61])])).
% 0.19/0.44  cnf(c_0_111, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_99])])).
% 0.19/0.44  cnf(c_0_112, negated_conjecture, (~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_28])]), c_0_111])).
% 0.19/0.44  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_21]), c_0_28]), c_0_30])]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 114
% 0.19/0.44  # Proof object clause steps            : 85
% 0.19/0.44  # Proof object formula steps           : 29
% 0.19/0.44  # Proof object conjectures             : 53
% 0.19/0.44  # Proof object clause conjectures      : 50
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 29
% 0.19/0.44  # Proof object initial formulas used   : 14
% 0.19/0.44  # Proof object generating inferences   : 49
% 0.19/0.44  # Proof object simplifying inferences  : 139
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 14
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 47
% 0.19/0.44  # Removed in clause preprocessing      : 0
% 0.19/0.44  # Initial clauses in saturation        : 47
% 0.19/0.44  # Processed clauses                    : 363
% 0.19/0.44  # ...of these trivial                  : 19
% 0.19/0.44  # ...subsumed                          : 80
% 0.19/0.44  # ...remaining for further processing  : 264
% 0.19/0.44  # Other redundant clauses eliminated   : 1
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 25
% 0.19/0.44  # Backward-rewritten                   : 50
% 0.19/0.44  # Generated clauses                    : 541
% 0.19/0.44  # ...of the previous two non-trivial   : 507
% 0.19/0.44  # Contextual simplify-reflections      : 27
% 0.19/0.44  # Paramodulations                      : 527
% 0.19/0.44  # Factorizations                       : 6
% 0.19/0.44  # Equation resolutions                 : 5
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 185
% 0.19/0.44  #    Positive orientable unit clauses  : 18
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 5
% 0.19/0.44  #    Non-unit-clauses                  : 162
% 0.19/0.44  # Current number of unprocessed clauses: 133
% 0.19/0.44  # ...number of literals in the above   : 836
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 78
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 11969
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 1036
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 114
% 0.19/0.44  # Unit Clause-clause subsumption calls : 202
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 8
% 0.19/0.44  # BW rewrite match successes           : 8
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 27237
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.093 s
% 0.19/0.44  # System time              : 0.007 s
% 0.19/0.44  # Total time               : 0.099 s
% 0.19/0.44  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
