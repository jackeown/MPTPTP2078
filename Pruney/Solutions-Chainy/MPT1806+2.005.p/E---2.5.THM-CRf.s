%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:29 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 (2498 expanded)
%              Number of clauses        :   88 ( 858 expanded)
%              Number of leaves         :   15 ( 622 expanded)
%              Depth                    :   14
%              Number of atoms          :  654 (24494 expanded)
%              Number of equality atoms :   70 ( 643 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

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

fof(rc1_connsp_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

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

fof(c_0_15,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k7_tmap_1(X17,X18) = k6_partfun1(u1_struct_0(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

fof(c_0_16,plain,(
    ! [X43,X44] :
      ( ~ l1_pre_topc(X43)
      | ~ m1_pre_topc(X44,X43)
      | m1_subset_1(u1_struct_0(X44),k1_zfmisc_1(u1_struct_0(X43))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X19,X20,X21,X22] :
      ( ( X21 != k8_tmap_1(X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | X22 != u1_struct_0(X20)
        | X21 = k6_tmap_1(X19,X22)
        | ~ v1_pre_topc(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))
        | X21 = k8_tmap_1(X19,X20)
        | ~ v1_pre_topc(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( esk2_3(X19,X20,X21) = u1_struct_0(X20)
        | X21 = k8_tmap_1(X19,X20)
        | ~ v1_pre_topc(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( X21 != k6_tmap_1(X19,esk2_3(X19,X20,X21))
        | X21 = k8_tmap_1(X19,X20)
        | ~ v1_pre_topc(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_19,plain,(
    ! [X9] :
      ( ( m1_subset_1(esk1_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( v1_xboole_0(esk1_1(X9))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc1_connsp_1])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_pre_topc(esk6_0,esk5_0)
    & ( ~ v1_tsep_1(esk6_0,esk5_0)
      | ~ m1_pre_topc(esk6_0,esk5_0)
      | ~ v1_funct_1(k9_tmap_1(esk5_0,esk6_0))
      | ~ v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))
      | ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
      | ~ m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))))) )
    & ( v1_funct_1(k9_tmap_1(esk5_0,esk6_0))
      | v1_tsep_1(esk6_0,esk5_0) )
    & ( v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))
      | v1_tsep_1(esk6_0,esk5_0) )
    & ( v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
      | v1_tsep_1(esk6_0,esk5_0) )
    & ( m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))
      | v1_tsep_1(esk6_0,esk5_0) )
    & ( v1_funct_1(k9_tmap_1(esk5_0,esk6_0))
      | m1_pre_topc(esk6_0,esk5_0) )
    & ( v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))
      | m1_pre_topc(esk6_0,esk5_0) )
    & ( v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
      | m1_pre_topc(esk6_0,esk5_0) )
    & ( m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))
      | m1_pre_topc(esk6_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).

fof(c_0_23,plain,(
    ! [X39,X40] :
      ( ( u1_struct_0(k6_tmap_1(X39,X40)) = u1_struct_0(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( u1_pre_topc(k6_tmap_1(X39,X40)) = k5_tmap_1(X39,X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_24,plain,(
    ! [X37,X38] :
      ( ( v1_funct_1(k9_tmap_1(X37,X38))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) )
      & ( v1_funct_2(k9_tmap_1(X37,X38),u1_struct_0(X37),u1_struct_0(k8_tmap_1(X37,X38)))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) )
      & ( m1_subset_1(k9_tmap_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(k8_tmap_1(X37,X38)))))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X35,X36] :
      ( ( v1_pre_topc(k8_tmap_1(X35,X36))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X35) )
      & ( v2_pre_topc(k8_tmap_1(X35,X36))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X35) )
      & ( l1_pre_topc(k8_tmap_1(X35,X36))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_27,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v1_tsep_1(X30,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | X31 != u1_struct_0(X30)
        | v3_pre_topc(X31,X29)
        | ~ m1_pre_topc(X30,X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(esk4_2(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))
        | v1_tsep_1(X30,X29)
        | ~ m1_pre_topc(X30,X29)
        | ~ l1_pre_topc(X29) )
      & ( esk4_2(X29,X30) = u1_struct_0(X30)
        | v1_tsep_1(X30,X29)
        | ~ m1_pre_topc(X30,X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ v3_pre_topc(esk4_2(X29,X30),X29)
        | v1_tsep_1(X30,X29)
        | ~ m1_pre_topc(X30,X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

fof(c_0_28,plain,(
    ! [X33,X34] :
      ( ( v1_funct_1(k7_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( v1_funct_2(k7_tmap_1(X33,X34),u1_struct_0(X33),u1_struct_0(k6_tmap_1(X33,X34)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( m1_subset_1(k7_tmap_1(X33,X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(k6_tmap_1(X33,X34)))))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_36,plain,(
    ! [X24,X25,X26,X27] :
      ( ( X26 != k9_tmap_1(X24,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))
        | X27 != u1_struct_0(X25)
        | r1_funct_2(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)),u1_struct_0(X24),u1_struct_0(k6_tmap_1(X24,X27)),X26,k7_tmap_1(X24,X27))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))))
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk3_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))
        | X26 = k9_tmap_1(X24,X25)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))))
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( esk3_3(X24,X25,X26) = u1_struct_0(X25)
        | X26 = k9_tmap_1(X24,X25)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))))
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ r1_funct_2(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)),u1_struct_0(X24),u1_struct_0(k6_tmap_1(X24,esk3_3(X24,X25,X26))),X26,k7_tmap_1(X24,esk3_3(X24,X25,X26)))
        | X26 = k9_tmap_1(X24,X25)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))))
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
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
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_41,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_46,plain,
    ( k7_tmap_1(X1,esk1_1(X1)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk5_0)) = k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_48,plain,
    ( u1_struct_0(k6_tmap_1(X1,esk1_1(X1))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_49,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_55,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_21])).

cnf(c_0_56,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X3))
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_41]),c_0_42]),c_0_43])).

fof(c_0_57,plain,(
    ! [X41,X42] :
      ( ( v1_funct_1(k7_tmap_1(X41,X42))
        | ~ v3_pre_topc(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( v1_funct_2(k7_tmap_1(X41,X42),u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))
        | ~ v3_pre_topc(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( v5_pre_topc(k7_tmap_1(X41,X42),X41,k6_tmap_1(X41,X42))
        | ~ v3_pre_topc(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( m1_subset_1(k7_tmap_1(X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))))
        | ~ v3_pre_topc(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( ~ v1_funct_1(k7_tmap_1(X41,X42))
        | ~ v1_funct_2(k7_tmap_1(X41,X42),u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))
        | ~ v5_pre_topc(k7_tmap_1(X41,X42),X41,k6_tmap_1(X41,X42))
        | ~ m1_subset_1(k7_tmap_1(X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))))
        | v3_pre_topc(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).

cnf(c_0_58,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_31]),c_0_33])])).

fof(c_0_59,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r1_funct_2(X11,X12,X13,X14,X15,X16)
        | X15 = X16
        | v1_xboole_0(X12)
        | v1_xboole_0(X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X11,X12)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X13,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( X15 != X16
        | r1_funct_2(X11,X12,X13,X14,X15,X16)
        | v1_xboole_0(X12)
        | v1_xboole_0(X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X11,X12)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X13,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_60,plain,
    ( m1_subset_1(k7_tmap_1(X1,esk1_1(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk1_1(X1))))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( k7_tmap_1(esk5_0,esk1_1(esk5_0)) = k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_33])]),c_0_34]),c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk5_0,esk1_1(esk5_0))) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_63,plain,
    ( v1_funct_2(k7_tmap_1(X1,esk1_1(X1)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk1_1(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_29])).

cnf(c_0_64,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,X1)),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,X1))
    | X1 != u1_struct_0(esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_31]),c_0_32]),c_0_53]),c_0_54]),c_0_33])]),c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_67,negated_conjecture,
    ( k6_tmap_1(esk5_0,u1_struct_0(X1)) = k8_tmap_1(esk5_0,esk6_0)
    | u1_struct_0(X1) != u1_struct_0(esk6_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_68,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X2))
    | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( k7_tmap_1(esk5_0,esk4_2(esk5_0,esk6_0)) = k6_partfun1(u1_struct_0(esk5_0))
    | v1_tsep_1(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_58]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_70,plain,
    ( esk4_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_71,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_32]),c_0_61]),c_0_62]),c_0_33])]),c_0_34])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_32]),c_0_61]),c_0_62]),c_0_33])]),c_0_34])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_75,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk5_0,esk6_0)) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_31])])).

cnf(c_0_77,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_68,c_0_45]),c_0_50]),c_0_49])).

cnf(c_0_78,negated_conjecture,
    ( k7_tmap_1(esk5_0,esk4_2(esk5_0,esk6_0)) = k7_tmap_1(esk5_0,u1_struct_0(esk6_0))
    | v1_tsep_1(esk6_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_47])).

cnf(c_0_79,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk4_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_80,negated_conjecture,
    ( esk4_2(esk5_0,esk6_0) = u1_struct_0(esk6_0)
    | v1_tsep_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_31]),c_0_33])])).

fof(c_0_81,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_82,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_83,negated_conjecture,
    ( X1 = k7_tmap_1(esk5_0,u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk5_0),u1_struct_0(esk5_0),X1,k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74])])).

cnf(c_0_84,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_76])).

cnf(c_0_87,plain,
    ( v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_tsep_1(esk6_0,esk5_0)
    | ~ m1_pre_topc(esk6_0,esk5_0)
    | ~ v1_funct_1(k9_tmap_1(esk5_0,esk6_0))
    | ~ v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))
    | ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_89,negated_conjecture,
    ( v3_pre_topc(esk4_2(esk5_0,esk6_0),esk5_0)
    | v1_tsep_1(esk6_0,esk5_0)
    | ~ v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),esk5_0,k6_tmap_1(esk5_0,esk4_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_32]),c_0_33])]),c_0_34]),c_0_58])).

cnf(c_0_90,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0)
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_31]),c_0_33])])).

cnf(c_0_91,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_92,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_93,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_54]),c_0_86])])).

cnf(c_0_94,plain,
    ( v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_21])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk1_1(k6_tmap_1(esk5_0,u1_struct_0(esk6_0))),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_66])).

cnf(c_0_96,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_97,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ v1_tsep_1(esk6_0,esk5_0)
    | ~ v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))
    | ~ v1_funct_1(k9_tmap_1(esk5_0,esk6_0))
    | ~ m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_31])])).

cnf(c_0_98,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0)
    | ~ v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),esk5_0,k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_80]),c_0_90])).

cnf(c_0_99,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_21]),c_0_31]),c_0_33])])).

cnf(c_0_101,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(X1)),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | u1_struct_0(X1) != u1_struct_0(esk6_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk5_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_67]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_102,negated_conjecture,
    ( k7_tmap_1(esk5_0,X1) = k7_tmap_1(esk5_0,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_47]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(esk1_1(k8_tmap_1(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_67]),c_0_96]),c_0_31])])).

cnf(c_0_104,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ v1_tsep_1(esk6_0,esk5_0)
    | ~ v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))
    | ~ m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_54])])).

cnf(c_0_105,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0)
    | ~ v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),esk5_0,k8_tmap_1(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_67]),c_0_31])])).

cnf(c_0_106,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_33])]),c_0_34])).

cnf(c_0_107,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | v1_tsep_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_108,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk5_0,X1),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_31])])).

cnf(c_0_109,negated_conjecture,
    ( k7_tmap_1(esk5_0,esk1_1(k8_tmap_1(esk5_0,esk6_0))) = k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_103]),c_0_47]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_110,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ v1_tsep_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_53])]),c_0_52])])).

cnf(c_0_111,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_107])).

cnf(c_0_112,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_113,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_103])])).

cnf(c_0_114,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111])])).

cnf(c_0_115,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_112,c_0_21])).

cnf(c_0_116,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_106]),c_0_114])).

cnf(c_0_117,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk5_0)
    | u1_struct_0(X1) != u1_struct_0(esk6_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_111]),c_0_31]),c_0_33])])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:45:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.49  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.042 s
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.20/0.49  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.49  fof(t122_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t122_tmap_1)).
% 0.20/0.49  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.20/0.49  fof(rc1_connsp_1, axiom, ![X1]:(l1_pre_topc(X1)=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_connsp_1)).
% 0.20/0.49  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.20/0.49  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.20/0.49  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.20/0.49  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.20/0.49  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.20/0.49  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.20/0.49  fof(t113_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.20/0.49  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.20/0.49  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.49  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.49  fof(c_0_15, plain, ![X17, X18]:(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|k7_tmap_1(X17,X18)=k6_partfun1(u1_struct_0(X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.20/0.49  fof(c_0_16, plain, ![X43, X44]:(~l1_pre_topc(X43)|(~m1_pre_topc(X44,X43)|m1_subset_1(u1_struct_0(X44),k1_zfmisc_1(u1_struct_0(X43))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.49  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t122_tmap_1])).
% 0.20/0.49  fof(c_0_18, plain, ![X19, X20, X21, X22]:((X21!=k8_tmap_1(X19,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|(X22!=u1_struct_0(X20)|X21=k6_tmap_1(X19,X22)))|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((m1_subset_1(esk2_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))|X21=k8_tmap_1(X19,X20)|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((esk2_3(X19,X20,X21)=u1_struct_0(X20)|X21=k8_tmap_1(X19,X20)|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(X21!=k6_tmap_1(X19,esk2_3(X19,X20,X21))|X21=k8_tmap_1(X19,X20)|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.20/0.49  fof(c_0_19, plain, ![X9]:((m1_subset_1(esk1_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))&(v1_xboole_0(esk1_1(X9))|~l1_pre_topc(X9))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc1_connsp_1])])])])).
% 0.20/0.49  cnf(c_0_20, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.49  cnf(c_0_21, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  fof(c_0_22, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_pre_topc(esk6_0,esk5_0)&((~v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(esk6_0,esk5_0)|(~v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|~v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))))&(((((v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|v1_tsep_1(esk6_0,esk5_0))&(v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|v1_tsep_1(esk6_0,esk5_0)))&(v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|v1_tsep_1(esk6_0,esk5_0)))&(m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))|v1_tsep_1(esk6_0,esk5_0)))&((((v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|m1_pre_topc(esk6_0,esk5_0))&(v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|m1_pre_topc(esk6_0,esk5_0)))&(v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|m1_pre_topc(esk6_0,esk5_0)))&(m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))|m1_pre_topc(esk6_0,esk5_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).
% 0.20/0.49  fof(c_0_23, plain, ![X39, X40]:((u1_struct_0(k6_tmap_1(X39,X40))=u1_struct_0(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(u1_pre_topc(k6_tmap_1(X39,X40))=k5_tmap_1(X39,X40)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.20/0.49  fof(c_0_24, plain, ![X37, X38]:(((v1_funct_1(k9_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37)))&(v1_funct_2(k9_tmap_1(X37,X38),u1_struct_0(X37),u1_struct_0(k8_tmap_1(X37,X38)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37))))&(m1_subset_1(k9_tmap_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(k8_tmap_1(X37,X38)))))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.20/0.49  cnf(c_0_25, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  fof(c_0_26, plain, ![X35, X36]:(((v1_pre_topc(k8_tmap_1(X35,X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))&(v2_pre_topc(k8_tmap_1(X35,X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35))))&(l1_pre_topc(k8_tmap_1(X35,X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.20/0.49  fof(c_0_27, plain, ![X29, X30, X31]:((~v1_tsep_1(X30,X29)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(X31!=u1_struct_0(X30)|v3_pre_topc(X31,X29)))|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29))&((m1_subset_1(esk4_2(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))|v1_tsep_1(X30,X29)|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29))&((esk4_2(X29,X30)=u1_struct_0(X30)|v1_tsep_1(X30,X29)|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29))&(~v3_pre_topc(esk4_2(X29,X30),X29)|v1_tsep_1(X30,X29)|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.20/0.49  fof(c_0_28, plain, ![X33, X34]:(((v1_funct_1(k7_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))))&(v1_funct_2(k7_tmap_1(X33,X34),u1_struct_0(X33),u1_struct_0(k6_tmap_1(X33,X34)))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))))))&(m1_subset_1(k7_tmap_1(X33,X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(k6_tmap_1(X33,X34)))))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.20/0.49  cnf(c_0_29, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.49  cnf(c_0_30, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.49  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.49  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.49  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.49  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.49  cnf(c_0_35, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.49  fof(c_0_36, plain, ![X24, X25, X26, X27]:((X26!=k9_tmap_1(X24,X25)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))|(X27!=u1_struct_0(X25)|r1_funct_2(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)),u1_struct_0(X24),u1_struct_0(k6_tmap_1(X24,X27)),X26,k7_tmap_1(X24,X27))))|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25))))))|~m1_pre_topc(X25,X24)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&((m1_subset_1(esk3_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))|X26=k9_tmap_1(X24,X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25))))))|~m1_pre_topc(X25,X24)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&((esk3_3(X24,X25,X26)=u1_struct_0(X25)|X26=k9_tmap_1(X24,X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25))))))|~m1_pre_topc(X25,X24)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~r1_funct_2(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)),u1_struct_0(X24),u1_struct_0(k6_tmap_1(X24,esk3_3(X24,X25,X26))),X26,k7_tmap_1(X24,esk3_3(X24,X25,X26)))|X26=k9_tmap_1(X24,X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25))))))|~m1_pre_topc(X25,X24)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.20/0.49  cnf(c_0_37, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.49  cnf(c_0_38, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.49  cnf(c_0_39, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.49  cnf(c_0_40, plain, (X1=k6_tmap_1(X2,u1_struct_0(X3))|v2_struct_0(X2)|u1_struct_0(X3)!=u1_struct_0(X4)|X1!=k8_tmap_1(X2,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.20/0.49  cnf(c_0_41, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.49  cnf(c_0_42, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.49  cnf(c_0_43, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.49  cnf(c_0_44, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.49  cnf(c_0_45, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.49  cnf(c_0_46, plain, (k7_tmap_1(X1,esk1_1(X1))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_29])).
% 0.20/0.49  cnf(c_0_47, negated_conjecture, (k6_partfun1(u1_struct_0(esk5_0))=k7_tmap_1(esk5_0,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_48, plain, (u1_struct_0(k6_tmap_1(X1,esk1_1(X1)))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_29])).
% 0.20/0.49  cnf(c_0_49, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.49  cnf(c_0_50, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.49  cnf(c_0_51, plain, (r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))|v2_struct_0(X2)|X1!=k9_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.49  cnf(c_0_52, negated_conjecture, (m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_53, negated_conjecture, (v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_54, negated_conjecture, (v1_funct_1(k9_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_55, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_21])).
% 0.20/0.49  cnf(c_0_56, plain, (k8_tmap_1(X1,X2)=k6_tmap_1(X1,u1_struct_0(X3))|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.20/0.49  fof(c_0_57, plain, ![X41, X42]:(((((v1_funct_1(k7_tmap_1(X41,X42))|~v3_pre_topc(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(v1_funct_2(k7_tmap_1(X41,X42),u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))|~v3_pre_topc(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41))))&(v5_pre_topc(k7_tmap_1(X41,X42),X41,k6_tmap_1(X41,X42))|~v3_pre_topc(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41))))&(m1_subset_1(k7_tmap_1(X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))))|~v3_pre_topc(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41))))&(~v1_funct_1(k7_tmap_1(X41,X42))|~v1_funct_2(k7_tmap_1(X41,X42),u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))|~v5_pre_topc(k7_tmap_1(X41,X42),X41,k6_tmap_1(X41,X42))|~m1_subset_1(k7_tmap_1(X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))))|v3_pre_topc(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).
% 0.20/0.49  cnf(c_0_58, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_31]), c_0_33])])).
% 0.20/0.49  fof(c_0_59, plain, ![X11, X12, X13, X14, X15, X16]:((~r1_funct_2(X11,X12,X13,X14,X15,X16)|X15=X16|(v1_xboole_0(X12)|v1_xboole_0(X14)|~v1_funct_1(X15)|~v1_funct_2(X15,X11,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))&(X15!=X16|r1_funct_2(X11,X12,X13,X14,X15,X16)|(v1_xboole_0(X12)|v1_xboole_0(X14)|~v1_funct_1(X15)|~v1_funct_2(X15,X11,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.20/0.49  cnf(c_0_60, plain, (m1_subset_1(k7_tmap_1(X1,esk1_1(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk1_1(X1))))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_29])).
% 0.20/0.49  cnf(c_0_61, negated_conjecture, (k7_tmap_1(esk5_0,esk1_1(esk5_0))=k7_tmap_1(esk5_0,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_32]), c_0_33])]), c_0_34]), c_0_47])).
% 0.20/0.49  cnf(c_0_62, negated_conjecture, (u1_struct_0(k6_tmap_1(esk5_0,esk1_1(esk5_0)))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_63, plain, (v1_funct_2(k7_tmap_1(X1,esk1_1(X1)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk1_1(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_49, c_0_29])).
% 0.20/0.49  cnf(c_0_64, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_21])).
% 0.20/0.49  cnf(c_0_65, negated_conjecture, (r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,X1)),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,X1))|X1!=u1_struct_0(esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_31]), c_0_32]), c_0_53]), c_0_54]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_66, negated_conjecture, (u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_67, negated_conjecture, (k6_tmap_1(esk5_0,u1_struct_0(X1))=k8_tmap_1(esk5_0,esk6_0)|u1_struct_0(X1)!=u1_struct_0(esk6_0)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_68, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|~v1_funct_1(k7_tmap_1(X1,X2))|~v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|~v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|~m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.49  cnf(c_0_69, negated_conjecture, (k7_tmap_1(esk5_0,esk4_2(esk5_0,esk6_0))=k6_partfun1(u1_struct_0(esk5_0))|v1_tsep_1(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_58]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_70, plain, (esk4_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.49  cnf(c_0_71, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.49  cnf(c_0_72, negated_conjecture, (m1_subset_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_32]), c_0_61]), c_0_62]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_73, negated_conjecture, (v1_funct_2(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_32]), c_0_61]), c_0_62]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_74, negated_conjecture, (v1_funct_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_75, negated_conjecture, (r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.49  cnf(c_0_76, negated_conjecture, (u1_struct_0(k8_tmap_1(esk5_0,esk6_0))=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_31])])).
% 0.20/0.49  cnf(c_0_77, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_68, c_0_45]), c_0_50]), c_0_49])).
% 0.20/0.49  cnf(c_0_78, negated_conjecture, (k7_tmap_1(esk5_0,esk4_2(esk5_0,esk6_0))=k7_tmap_1(esk5_0,u1_struct_0(esk6_0))|v1_tsep_1(esk6_0,esk5_0)), inference(rw,[status(thm)],[c_0_69, c_0_47])).
% 0.20/0.49  cnf(c_0_79, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk4_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.49  cnf(c_0_80, negated_conjecture, (esk4_2(esk5_0,esk6_0)=u1_struct_0(esk6_0)|v1_tsep_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_31]), c_0_33])])).
% 0.20/0.49  fof(c_0_81, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.49  fof(c_0_82, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.49  cnf(c_0_83, negated_conjecture, (X1=k7_tmap_1(esk5_0,u1_struct_0(esk6_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk5_0),u1_struct_0(esk5_0),X1,k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74])])).
% 0.20/0.49  cnf(c_0_84, negated_conjecture, (r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.49  cnf(c_0_85, negated_conjecture, (v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_53, c_0_76])).
% 0.20/0.49  cnf(c_0_86, negated_conjecture, (m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(rw,[status(thm)],[c_0_52, c_0_76])).
% 0.20/0.49  cnf(c_0_87, plain, (v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.49  cnf(c_0_88, negated_conjecture, (~v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(esk6_0,esk5_0)|~v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|~v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.49  cnf(c_0_89, negated_conjecture, (v3_pre_topc(esk4_2(esk5_0,esk6_0),esk5_0)|v1_tsep_1(esk6_0,esk5_0)|~v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),esk5_0,k6_tmap_1(esk5_0,esk4_2(esk5_0,esk6_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_32]), c_0_33])]), c_0_34]), c_0_58])).
% 0.20/0.49  cnf(c_0_90, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)|~v3_pre_topc(u1_struct_0(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_31]), c_0_33])])).
% 0.20/0.49  cnf(c_0_91, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.49  cnf(c_0_92, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.49  cnf(c_0_93, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_54]), c_0_86])])).
% 0.20/0.49  cnf(c_0_94, plain, (v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_87, c_0_21])).
% 0.20/0.49  cnf(c_0_95, negated_conjecture, (m1_subset_1(esk1_1(k6_tmap_1(esk5_0,u1_struct_0(esk6_0))),k1_zfmisc_1(u1_struct_0(esk5_0)))|~l1_pre_topc(k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_29, c_0_66])).
% 0.20/0.49  cnf(c_0_96, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_97, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~v1_tsep_1(esk6_0,esk5_0)|~v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|~v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|~m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_31])])).
% 0.20/0.49  cnf(c_0_98, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)|~v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),esk5_0,k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_80]), c_0_90])).
% 0.20/0.49  cnf(c_0_99, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.49  cnf(c_0_100, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_21]), c_0_31]), c_0_33])])).
% 0.20/0.49  cnf(c_0_101, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(X1)),esk5_0,k8_tmap_1(esk5_0,esk6_0))|u1_struct_0(X1)!=u1_struct_0(esk6_0)|~v3_pre_topc(u1_struct_0(X1),esk5_0)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_67]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_102, negated_conjecture, (k7_tmap_1(esk5_0,X1)=k7_tmap_1(esk5_0,u1_struct_0(esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_47]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_103, negated_conjecture, (m1_subset_1(esk1_1(k8_tmap_1(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_67]), c_0_96]), c_0_31])])).
% 0.20/0.49  cnf(c_0_104, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~v1_tsep_1(esk6_0,esk5_0)|~v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|~m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_54])])).
% 0.20/0.49  cnf(c_0_105, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)|~v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),esk5_0,k8_tmap_1(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_67]), c_0_31])])).
% 0.20/0.49  cnf(c_0_106, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_107, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|v1_tsep_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.49  cnf(c_0_108, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk5_0,X1),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~v3_pre_topc(u1_struct_0(esk6_0),esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_31])])).
% 0.20/0.49  cnf(c_0_109, negated_conjecture, (k7_tmap_1(esk5_0,esk1_1(k8_tmap_1(esk5_0,esk6_0)))=k7_tmap_1(esk5_0,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_103]), c_0_47]), c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.49  cnf(c_0_110, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~v1_tsep_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_53])]), c_0_52])])).
% 0.20/0.49  cnf(c_0_111, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106]), c_0_107])).
% 0.20/0.49  cnf(c_0_112, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.49  cnf(c_0_113, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~v3_pre_topc(u1_struct_0(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_103])])).
% 0.20/0.49  cnf(c_0_114, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111])])).
% 0.20/0.49  cnf(c_0_115, plain, (v3_pre_topc(u1_struct_0(X1),X2)|u1_struct_0(X1)!=u1_struct_0(X3)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_112, c_0_21])).
% 0.20/0.49  cnf(c_0_116, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_106]), c_0_114])).
% 0.20/0.49  cnf(c_0_117, negated_conjecture, (v3_pre_topc(u1_struct_0(X1),esk5_0)|u1_struct_0(X1)!=u1_struct_0(esk6_0)|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_111]), c_0_31]), c_0_33])])).
% 0.20/0.49  cnf(c_0_118, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_31])]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 119
% 0.20/0.49  # Proof object clause steps            : 88
% 0.20/0.49  # Proof object formula steps           : 31
% 0.20/0.49  # Proof object conjectures             : 54
% 0.20/0.49  # Proof object clause conjectures      : 51
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 30
% 0.20/0.49  # Proof object initial formulas used   : 15
% 0.20/0.49  # Proof object generating inferences   : 47
% 0.20/0.49  # Proof object simplifying inferences  : 139
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 15
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 49
% 0.20/0.49  # Removed in clause preprocessing      : 0
% 0.20/0.49  # Initial clauses in saturation        : 49
% 0.20/0.49  # Processed clauses                    : 706
% 0.20/0.49  # ...of these trivial                  : 37
% 0.20/0.49  # ...subsumed                          : 228
% 0.20/0.49  # ...remaining for further processing  : 441
% 0.20/0.49  # Other redundant clauses eliminated   : 1
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 19
% 0.20/0.49  # Backward-rewritten                   : 161
% 0.20/0.49  # Generated clauses                    : 1601
% 0.20/0.49  # ...of the previous two non-trivial   : 1527
% 0.20/0.49  # Contextual simplify-reflections      : 26
% 0.20/0.49  # Paramodulations                      : 1585
% 0.20/0.49  # Factorizations                       : 10
% 0.20/0.49  # Equation resolutions                 : 5
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 259
% 0.20/0.49  #    Positive orientable unit clauses  : 21
% 0.20/0.49  #    Positive unorientable unit clauses: 0
% 0.20/0.49  #    Negative unit clauses             : 3
% 0.20/0.49  #    Non-unit-clauses                  : 235
% 0.20/0.49  # Current number of unprocessed clauses: 847
% 0.20/0.49  # ...number of literals in the above   : 4521
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 181
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 39043
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 4129
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 262
% 0.20/0.49  # Unit Clause-clause subsumption calls : 550
% 0.20/0.49  # Rewrite failures with RHS unbound    : 0
% 0.20/0.49  # BW rewrite match attempts            : 17
% 0.20/0.49  # BW rewrite match successes           : 14
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 63304
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.142 s
% 0.20/0.49  # System time              : 0.008 s
% 0.20/0.49  # Total time               : 0.150 s
% 0.20/0.49  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
