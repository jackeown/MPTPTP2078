%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:29 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  144 (8323 expanded)
%              Number of clauses        :  107 (2886 expanded)
%              Number of leaves         :   18 (2080 expanded)
%              Depth                    :   16
%              Number of atoms          :  768 (77826 expanded)
%              Number of equality atoms :   76 (1756 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(existence_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ? [X2] : m1_pre_topc(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

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

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

fof(reflexivity_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => r1_funct_2(X1,X2,X3,X4,X5,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

fof(c_0_18,plain,(
    ! [X43,X44] :
      ( ( u1_struct_0(k6_tmap_1(X43,X44)) = u1_struct_0(X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( u1_pre_topc(k6_tmap_1(X43,X44)) = k5_tmap_1(X43,X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_19,plain,(
    ! [X47,X48] :
      ( ~ l1_pre_topc(X47)
      | ~ m1_pre_topc(X48,X47)
      | m1_subset_1(u1_struct_0(X48),k1_zfmisc_1(u1_struct_0(X47))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_20,plain,(
    ! [X33,X34] :
      ( ( v1_pre_topc(k6_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( v2_pre_topc(k6_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( l1_pre_topc(k6_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_21,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | m1_pre_topc(esk1_1(X8),X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[existence_m1_pre_topc])])])).

fof(c_0_24,negated_conjecture,(
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

cnf(c_0_25,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
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

fof(c_0_27,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_28,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_29,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( m1_pre_topc(esk1_1(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_33,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X37,X38] :
      ( ( v1_pre_topc(k8_tmap_1(X37,X38))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) )
      & ( v2_pre_topc(k8_tmap_1(X37,X38))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) )
      & ( l1_pre_topc(k8_tmap_1(X37,X38))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(esk1_1(X1)))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k6_tmap_1(X1,u1_struct_0(esk1_1(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

fof(c_0_42,plain,(
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

cnf(c_0_43,plain,
    ( X1 = k6_tmap_1(X2,u1_struct_0(X3))
    | v2_struct_0(X2)
    | u1_struct_0(X3) != u1_struct_0(X4)
    | X1 != k8_tmap_1(X2,X4)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_44,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_48,plain,(
    ! [X49] :
      ( ~ l1_pre_topc(X49)
      | m1_pre_topc(X49,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_49,plain,(
    ! [X35,X36] :
      ( ( v1_funct_1(k7_tmap_1(X35,X36))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) )
      & ( v1_funct_2(k7_tmap_1(X35,X36),u1_struct_0(X35),u1_struct_0(k6_tmap_1(X35,X36)))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) )
      & ( m1_subset_1(k7_tmap_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(k6_tmap_1(X35,X36)))))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

fof(c_0_50,plain,(
    ! [X41,X42] :
      ( ( ~ v2_struct_0(k6_tmap_1(X41,X42))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))) )
      & ( v1_pre_topc(k6_tmap_1(X41,X42))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))) )
      & ( v2_pre_topc(k6_tmap_1(X41,X42))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk1_1(esk5_0)))) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk5_0,u1_struct_0(esk1_1(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_54,plain,
    ( esk4_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_55,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k7_tmap_1(X17,X18) = k6_partfun1(u1_struct_0(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

cnf(c_0_56,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_58,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X3))
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_47]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_47]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_61,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_63,plain,(
    ! [X39,X40] :
      ( ( v1_funct_1(k9_tmap_1(X39,X40))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | ~ m1_pre_topc(X40,X39) )
      & ( v1_funct_2(k9_tmap_1(X39,X40),u1_struct_0(X39),u1_struct_0(k8_tmap_1(X39,X40)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | ~ m1_pre_topc(X40,X39) )
      & ( m1_subset_1(k9_tmap_1(X39,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(k8_tmap_1(X39,X40)))))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | ~ m1_pre_topc(X40,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk1_1(esk5_0))))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_66,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_67,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_68,negated_conjecture,
    ( esk4_2(esk5_0,esk6_0) = u1_struct_0(esk6_0)
    | v1_tsep_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_39])])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,plain,
    ( esk2_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_71,plain,
    ( v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_22])).

cnf(c_0_72,plain,
    ( v2_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_22])).

fof(c_0_73,plain,(
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

cnf(c_0_74,negated_conjecture,
    ( k6_tmap_1(esk5_0,u1_struct_0(X1)) = k8_tmap_1(esk5_0,esk6_0)
    | u1_struct_0(X1) != u1_struct_0(esk6_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_47]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_pre_topc(X1,k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_59]),c_0_60])])).

cnf(c_0_76,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X1))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_61])).

cnf(c_0_77,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_22])).

fof(c_0_78,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( v1_xboole_0(X12)
      | v1_xboole_0(X14)
      | ~ v1_funct_1(X15)
      | ~ v1_funct_2(X15,X11,X12)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,X13,X14)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | r1_funct_2(X11,X12,X13,X14,X15,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_funct_2])])])).

cnf(c_0_79,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_80,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_81,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk1_1(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_38]),c_0_39])]),c_0_40])).

fof(c_0_83,plain,(
    ! [X45,X46] :
      ( ( v1_funct_1(k7_tmap_1(X45,X46))
        | ~ v3_pre_topc(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( v1_funct_2(k7_tmap_1(X45,X46),u1_struct_0(X45),u1_struct_0(k6_tmap_1(X45,X46)))
        | ~ v3_pre_topc(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( v5_pre_topc(k7_tmap_1(X45,X46),X45,k6_tmap_1(X45,X46))
        | ~ v3_pre_topc(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( m1_subset_1(k7_tmap_1(X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(k6_tmap_1(X45,X46)))))
        | ~ v3_pre_topc(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( ~ v1_funct_1(k7_tmap_1(X45,X46))
        | ~ v1_funct_2(k7_tmap_1(X45,X46),u1_struct_0(X45),u1_struct_0(k6_tmap_1(X45,X46)))
        | ~ v5_pre_topc(k7_tmap_1(X45,X46),X45,k6_tmap_1(X45,X46))
        | ~ m1_subset_1(k7_tmap_1(X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(k6_tmap_1(X45,X46)))))
        | v3_pre_topc(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).

cnf(c_0_84,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_22])).

cnf(c_0_85,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0)
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_47]),c_0_39])])).

cnf(c_0_86,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_22])).

cnf(c_0_87,negated_conjecture,
    ( esk2_3(esk5_0,esk6_0,X1) = u1_struct_0(esk6_0)
    | X1 = k8_tmap_1(esk5_0,esk6_0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_47]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_88,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_47]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_89,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_47]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_90,plain,
    ( esk3_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_91,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk5_0,esk6_0)) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_74]),c_0_47])])).

cnf(c_0_92,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_61]),c_0_59]),c_0_60])])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk5_0))) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_95,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_96,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_61])).

cnf(c_0_97,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_funct_2(X4,X1,X6,X2,X3,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X6,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_47]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_47]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_47]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_pre_topc(esk1_1(esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_22]),c_0_39])])).

cnf(c_0_102,plain,
    ( v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_103,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk5_0)
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | u1_struct_0(X1) != u1_struct_0(esk6_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_47]),c_0_39])])).

cnf(c_0_104,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk5_0)) = k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_47]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_105,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk2_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_106,negated_conjecture,
    ( esk2_3(esk5_0,esk6_0,k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) = u1_struct_0(esk6_0)
    | k6_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k8_tmap_1(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_60])])).

cnf(c_0_107,negated_conjecture,
    ( esk3_3(esk5_0,esk6_0,X1) = u1_struct_0(esk6_0)
    | X1 = k9_tmap_1(esk5_0,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk5_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_38]),c_0_47]),c_0_39])]),c_0_40])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_109,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_93]),c_0_94]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_110,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk5_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_111,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X2))
    | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_112,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)),X3,X3)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_100])])).

cnf(c_0_113,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_30]),c_0_39])])).

cnf(c_0_114,negated_conjecture,
    ( ~ v1_tsep_1(esk6_0,esk5_0)
    | ~ m1_pre_topc(esk6_0,esk5_0)
    | ~ v1_funct_1(k9_tmap_1(esk5_0,esk6_0))
    | ~ v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))
    | ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_115,plain,
    ( v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_22])).

cnf(c_0_116,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk6_0),esk5_0)
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_47])).

cnf(c_0_117,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k7_tmap_1(esk5_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_93]),c_0_104]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_118,negated_conjecture,
    ( k6_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k8_tmap_1(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_88]),c_0_38]),c_0_89]),c_0_47]),c_0_39]),c_0_60])]),c_0_40])).

cnf(c_0_119,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_120,negated_conjecture,
    ( esk3_3(esk5_0,esk6_0,k7_tmap_1(esk5_0,u1_struct_0(esk5_0))) = u1_struct_0(esk6_0)
    | k7_tmap_1(esk5_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109]),c_0_110])])).

cnf(c_0_121,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_111,c_0_62]),c_0_95]),c_0_92])).

cnf(c_0_122,plain,
    ( X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk3_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk3_3(X1,X2,X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_123,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk5_0),u1_struct_0(esk5_0),X3,X3)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_91]),c_0_91]),c_0_113])).

cnf(c_0_124,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ v1_tsep_1(esk6_0,esk5_0)
    | ~ m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_47])]),c_0_99]),c_0_100])])).

cnf(c_0_125,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117]),c_0_38]),c_0_47]),c_0_39])]),c_0_40]),c_0_118])).

cnf(c_0_126,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk5_0,esk6_0)
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_38]),c_0_91]),c_0_108]),c_0_91]),c_0_109]),c_0_110]),c_0_47]),c_0_39])]),c_0_40])).

cnf(c_0_127,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk6_0),esk5_0)
    | ~ v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),esk5_0,k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_117]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_128,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk5_0,esk6_0)
    | ~ r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),k7_tmap_1(esk5_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_120]),c_0_38]),c_0_91]),c_0_118]),c_0_91]),c_0_117]),c_0_91]),c_0_108]),c_0_91]),c_0_109]),c_0_110]),c_0_47]),c_0_39])]),c_0_40])).

cnf(c_0_129,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),k7_tmap_1(esk5_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_108]),c_0_109]),c_0_110])]),c_0_113])).

cnf(c_0_130,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ v1_tsep_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_98])])).

cnf(c_0_131,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_132,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk6_0),esk5_0)
    | ~ v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),esk5_0,k8_tmap_1(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_74]),c_0_47])]),c_0_116])).

cnf(c_0_133,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])])).

cnf(c_0_134,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk4_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_85])).

cnf(c_0_136,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk6_0),esk5_0)
    | ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | v1_tsep_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_138,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0)
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_68]),c_0_47]),c_0_39])])).

cnf(c_0_139,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk6_0),esk5_0)
    | u1_struct_0(esk6_0) != u1_struct_0(X1)
    | ~ v1_tsep_1(X1,esk5_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_135]),c_0_39])])).

cnf(c_0_140,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_138])).

cnf(c_0_141,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_47])])).

cnf(c_0_142,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_140])])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_141]),c_0_117]),c_0_133]),c_0_118]),c_0_38]),c_0_47]),c_0_39])]),c_0_40]),c_0_142]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.39/1.57  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.39/1.57  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.39/1.57  #
% 1.39/1.57  # Preprocessing time       : 0.066 s
% 1.39/1.57  
% 1.39/1.57  # Proof found!
% 1.39/1.57  # SZS status Theorem
% 1.39/1.57  # SZS output start CNFRefutation
% 1.39/1.57  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 1.39/1.57  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 1.39/1.57  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 1.39/1.57  fof(existence_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>?[X2]:m1_pre_topc(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_pre_topc)).
% 1.39/1.57  fof(t122_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t122_tmap_1)).
% 1.39/1.57  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 1.39/1.57  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.39/1.57  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.39/1.57  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 1.39/1.57  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 1.39/1.57  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 1.39/1.57  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 1.39/1.57  fof(fc4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((~(v2_struct_0(k6_tmap_1(X1,X2)))&v1_pre_topc(k6_tmap_1(X1,X2)))&v2_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 1.39/1.57  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_tmap_1)).
% 1.39/1.57  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 1.39/1.57  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_tmap_1)).
% 1.39/1.57  fof(reflexivity_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>r1_funct_2(X1,X2,X3,X4,X5,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 1.39/1.57  fof(t113_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_tmap_1)).
% 1.39/1.57  fof(c_0_18, plain, ![X43, X44]:((u1_struct_0(k6_tmap_1(X43,X44))=u1_struct_0(X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))&(u1_pre_topc(k6_tmap_1(X43,X44))=k5_tmap_1(X43,X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 1.39/1.57  fof(c_0_19, plain, ![X47, X48]:(~l1_pre_topc(X47)|(~m1_pre_topc(X48,X47)|m1_subset_1(u1_struct_0(X48),k1_zfmisc_1(u1_struct_0(X47))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 1.39/1.57  fof(c_0_20, plain, ![X33, X34]:(((v1_pre_topc(k6_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))))&(v2_pre_topc(k6_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))))))&(l1_pre_topc(k6_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 1.39/1.57  cnf(c_0_21, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.39/1.57  cnf(c_0_22, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.39/1.57  fof(c_0_23, plain, ![X8]:(~l1_pre_topc(X8)|m1_pre_topc(esk1_1(X8),X8)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[existence_m1_pre_topc])])])).
% 1.39/1.57  fof(c_0_24, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t122_tmap_1])).
% 1.39/1.57  cnf(c_0_25, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.39/1.57  fof(c_0_26, plain, ![X19, X20, X21, X22]:((X21!=k8_tmap_1(X19,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|(X22!=u1_struct_0(X20)|X21=k6_tmap_1(X19,X22)))|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((m1_subset_1(esk2_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))|X21=k8_tmap_1(X19,X20)|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((esk2_3(X19,X20,X21)=u1_struct_0(X20)|X21=k8_tmap_1(X19,X20)|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(X21!=k6_tmap_1(X19,esk2_3(X19,X20,X21))|X21=k8_tmap_1(X19,X20)|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 1.39/1.57  fof(c_0_27, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 1.39/1.57  fof(c_0_28, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 1.39/1.57  cnf(c_0_29, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.39/1.57  cnf(c_0_30, plain, (m1_pre_topc(esk1_1(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.39/1.57  fof(c_0_31, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_pre_topc(esk6_0,esk5_0)&((~v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(esk6_0,esk5_0)|(~v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|~v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))))&(((((v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|v1_tsep_1(esk6_0,esk5_0))&(v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|v1_tsep_1(esk6_0,esk5_0)))&(v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|v1_tsep_1(esk6_0,esk5_0)))&(m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))|v1_tsep_1(esk6_0,esk5_0)))&((((v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|m1_pre_topc(esk6_0,esk5_0))&(v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|m1_pre_topc(esk6_0,esk5_0)))&(v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|m1_pre_topc(esk6_0,esk5_0)))&(m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))|m1_pre_topc(esk6_0,esk5_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])])).
% 1.39/1.57  cnf(c_0_32, plain, (v2_struct_0(X1)|l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 1.39/1.57  cnf(c_0_33, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.39/1.57  fof(c_0_34, plain, ![X37, X38]:(((v1_pre_topc(k8_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37)))&(v2_pre_topc(k8_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37))))&(l1_pre_topc(k8_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 1.39/1.57  cnf(c_0_35, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.39/1.57  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.39/1.57  cnf(c_0_37, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(esk1_1(X1))))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.39/1.57  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.39/1.57  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.39/1.57  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.39/1.57  cnf(c_0_41, plain, (v2_struct_0(X1)|l1_pre_topc(k6_tmap_1(X1,u1_struct_0(esk1_1(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 1.39/1.57  fof(c_0_42, plain, ![X29, X30, X31]:((~v1_tsep_1(X30,X29)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(X31!=u1_struct_0(X30)|v3_pre_topc(X31,X29)))|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29))&((m1_subset_1(esk4_2(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))|v1_tsep_1(X30,X29)|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29))&((esk4_2(X29,X30)=u1_struct_0(X30)|v1_tsep_1(X30,X29)|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29))&(~v3_pre_topc(esk4_2(X29,X30),X29)|v1_tsep_1(X30,X29)|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 1.39/1.57  cnf(c_0_43, plain, (X1=k6_tmap_1(X2,u1_struct_0(X3))|v2_struct_0(X2)|u1_struct_0(X3)!=u1_struct_0(X4)|X1!=k8_tmap_1(X2,X4)|~v1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_22])).
% 1.39/1.57  cnf(c_0_44, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.39/1.57  cnf(c_0_45, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.39/1.57  cnf(c_0_46, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.39/1.57  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.39/1.57  fof(c_0_48, plain, ![X49]:(~l1_pre_topc(X49)|m1_pre_topc(X49,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 1.39/1.57  fof(c_0_49, plain, ![X35, X36]:(((v1_funct_1(k7_tmap_1(X35,X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))))&(v1_funct_2(k7_tmap_1(X35,X36),u1_struct_0(X35),u1_struct_0(k6_tmap_1(X35,X36)))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))))))&(m1_subset_1(k7_tmap_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(k6_tmap_1(X35,X36)))))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 1.39/1.57  fof(c_0_50, plain, ![X41, X42]:(((~v2_struct_0(k6_tmap_1(X41,X42))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))))&(v1_pre_topc(k6_tmap_1(X41,X42))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))))))&(v2_pre_topc(k6_tmap_1(X41,X42))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).
% 1.39/1.57  cnf(c_0_51, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.39/1.57  cnf(c_0_52, negated_conjecture, (u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk1_1(esk5_0))))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_53, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk5_0,u1_struct_0(esk1_1(esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_54, plain, (esk4_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.39/1.57  fof(c_0_55, plain, ![X17, X18]:(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|k7_tmap_1(X17,X18)=k6_partfun1(u1_struct_0(X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 1.39/1.57  cnf(c_0_56, plain, (v1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.39/1.57  cnf(c_0_57, plain, (v2_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.39/1.57  cnf(c_0_58, plain, (k8_tmap_1(X1,X2)=k6_tmap_1(X1,u1_struct_0(X3))|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 1.39/1.57  cnf(c_0_59, negated_conjecture, (u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_47]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_60, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_47]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_61, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.39/1.57  cnf(c_0_62, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.39/1.57  fof(c_0_63, plain, ![X39, X40]:(((v1_funct_1(k9_tmap_1(X39,X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|~m1_pre_topc(X40,X39)))&(v1_funct_2(k9_tmap_1(X39,X40),u1_struct_0(X39),u1_struct_0(k8_tmap_1(X39,X40)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|~m1_pre_topc(X40,X39))))&(m1_subset_1(k9_tmap_1(X39,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(k8_tmap_1(X39,X40)))))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|~m1_pre_topc(X40,X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 1.39/1.57  cnf(c_0_64, plain, (v2_struct_0(X1)|~v2_struct_0(k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.39/1.57  cnf(c_0_65, negated_conjecture, (v2_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk1_1(esk5_0))))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 1.39/1.57  cnf(c_0_66, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.39/1.57  cnf(c_0_67, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.39/1.57  cnf(c_0_68, negated_conjecture, (esk4_2(esk5_0,esk6_0)=u1_struct_0(esk6_0)|v1_tsep_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_47]), c_0_39])])).
% 1.39/1.57  cnf(c_0_69, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.39/1.57  cnf(c_0_70, plain, (esk2_3(X1,X2,X3)=u1_struct_0(X2)|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.39/1.57  cnf(c_0_71, plain, (v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_56, c_0_22])).
% 1.39/1.57  cnf(c_0_72, plain, (v2_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_57, c_0_22])).
% 1.39/1.57  fof(c_0_73, plain, ![X24, X25, X26, X27]:((X26!=k9_tmap_1(X24,X25)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))|(X27!=u1_struct_0(X25)|r1_funct_2(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)),u1_struct_0(X24),u1_struct_0(k6_tmap_1(X24,X27)),X26,k7_tmap_1(X24,X27))))|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25))))))|~m1_pre_topc(X25,X24)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&((m1_subset_1(esk3_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))|X26=k9_tmap_1(X24,X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25))))))|~m1_pre_topc(X25,X24)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&((esk3_3(X24,X25,X26)=u1_struct_0(X25)|X26=k9_tmap_1(X24,X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25))))))|~m1_pre_topc(X25,X24)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~r1_funct_2(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)),u1_struct_0(X24),u1_struct_0(k6_tmap_1(X24,esk3_3(X24,X25,X26))),X26,k7_tmap_1(X24,esk3_3(X24,X25,X26)))|X26=k9_tmap_1(X24,X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(k8_tmap_1(X24,X25))))))|~m1_pre_topc(X25,X24)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 1.39/1.57  cnf(c_0_74, negated_conjecture, (k6_tmap_1(esk5_0,u1_struct_0(X1))=k8_tmap_1(esk5_0,esk6_0)|u1_struct_0(X1)!=u1_struct_0(esk6_0)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_47]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_75, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_pre_topc(X1,k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_59]), c_0_60])])).
% 1.39/1.57  cnf(c_0_76, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X1)))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_29, c_0_61])).
% 1.39/1.57  cnf(c_0_77, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_62, c_0_22])).
% 1.39/1.57  fof(c_0_78, plain, ![X11, X12, X13, X14, X15, X16]:(v1_xboole_0(X12)|v1_xboole_0(X14)|~v1_funct_1(X15)|~v1_funct_2(X15,X11,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|r1_funct_2(X11,X12,X13,X14,X15,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_funct_2])])])).
% 1.39/1.57  cnf(c_0_79, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.39/1.57  cnf(c_0_80, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.39/1.57  cnf(c_0_81, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.39/1.57  cnf(c_0_82, negated_conjecture, (~m1_subset_1(u1_struct_0(esk1_1(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  fof(c_0_83, plain, ![X45, X46]:(((((v1_funct_1(k7_tmap_1(X45,X46))|~v3_pre_topc(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)))&(v1_funct_2(k7_tmap_1(X45,X46),u1_struct_0(X45),u1_struct_0(k6_tmap_1(X45,X46)))|~v3_pre_topc(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45))))&(v5_pre_topc(k7_tmap_1(X45,X46),X45,k6_tmap_1(X45,X46))|~v3_pre_topc(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45))))&(m1_subset_1(k7_tmap_1(X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(k6_tmap_1(X45,X46)))))|~v3_pre_topc(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45))))&(~v1_funct_1(k7_tmap_1(X45,X46))|~v1_funct_2(k7_tmap_1(X45,X46),u1_struct_0(X45),u1_struct_0(k6_tmap_1(X45,X46)))|~v5_pre_topc(k7_tmap_1(X45,X46),X45,k6_tmap_1(X45,X46))|~m1_subset_1(k7_tmap_1(X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(k6_tmap_1(X45,X46)))))|v3_pre_topc(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).
% 1.39/1.57  cnf(c_0_84, plain, (v3_pre_topc(u1_struct_0(X1),X2)|u1_struct_0(X1)!=u1_struct_0(X3)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_66, c_0_22])).
% 1.39/1.57  cnf(c_0_85, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_47]), c_0_39])])).
% 1.39/1.57  cnf(c_0_86, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_69, c_0_22])).
% 1.39/1.57  cnf(c_0_87, negated_conjecture, (esk2_3(esk5_0,esk6_0,X1)=u1_struct_0(esk6_0)|X1=k8_tmap_1(esk5_0,esk6_0)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_47]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_88, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_47]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_89, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_47]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_90, plain, (esk3_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.39/1.57  cnf(c_0_91, negated_conjecture, (u1_struct_0(k8_tmap_1(esk5_0,esk6_0))=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_74]), c_0_47])])).
% 1.39/1.57  cnf(c_0_92, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.39/1.57  cnf(c_0_93, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_61]), c_0_59]), c_0_60])])).
% 1.39/1.57  cnf(c_0_94, negated_conjecture, (u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk5_0)))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_95, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.39/1.57  cnf(c_0_96, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_77, c_0_61])).
% 1.39/1.57  cnf(c_0_97, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_funct_2(X4,X1,X6,X2,X3,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X5)|~v1_funct_2(X5,X6,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X2)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 1.39/1.57  cnf(c_0_98, negated_conjecture, (m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_47]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_99, negated_conjecture, (v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_47]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_100, negated_conjecture, (v1_funct_1(k9_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_47]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_101, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))|~m1_pre_topc(esk1_1(esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_22]), c_0_39])])).
% 1.39/1.57  cnf(c_0_102, plain, (v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 1.39/1.57  cnf(c_0_103, negated_conjecture, (v3_pre_topc(u1_struct_0(X1),esk5_0)|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|u1_struct_0(X1)!=u1_struct_0(esk6_0)|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_47]), c_0_39])])).
% 1.39/1.57  cnf(c_0_104, negated_conjecture, (k6_partfun1(u1_struct_0(esk5_0))=k7_tmap_1(esk5_0,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_47]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_105, plain, (X1=k8_tmap_1(X2,X3)|v2_struct_0(X2)|X1!=k6_tmap_1(X2,esk2_3(X2,X3,X1))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.39/1.57  cnf(c_0_106, negated_conjecture, (esk2_3(esk5_0,esk6_0,k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))=u1_struct_0(esk6_0)|k6_tmap_1(esk5_0,u1_struct_0(esk6_0))=k8_tmap_1(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_60])])).
% 1.39/1.57  cnf(c_0_107, negated_conjecture, (esk3_3(esk5_0,esk6_0,X1)=u1_struct_0(esk6_0)|X1=k9_tmap_1(esk5_0,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))|~v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk5_0))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_38]), c_0_47]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_108, negated_conjecture, (m1_subset_1(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_109, negated_conjecture, (v1_funct_2(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_93]), c_0_94]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_110, negated_conjecture, (v1_funct_1(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_111, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|~v1_funct_1(k7_tmap_1(X1,X2))|~v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|~v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|~m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 1.39/1.57  cnf(c_0_112, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)),X3,X3)|v1_xboole_0(u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|v1_xboole_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99]), c_0_100])])).
% 1.39/1.57  cnf(c_0_113, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_30]), c_0_39])])).
% 1.39/1.57  cnf(c_0_114, negated_conjecture, (~v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(esk6_0,esk5_0)|~v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|~v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.39/1.57  cnf(c_0_115, plain, (v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_102, c_0_22])).
% 1.39/1.57  cnf(c_0_116, negated_conjecture, (v3_pre_topc(u1_struct_0(esk6_0),esk5_0)|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_103, c_0_47])).
% 1.39/1.57  cnf(c_0_117, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k7_tmap_1(esk5_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_93]), c_0_104]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_118, negated_conjecture, (k6_tmap_1(esk5_0,u1_struct_0(esk6_0))=k8_tmap_1(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_88]), c_0_38]), c_0_89]), c_0_47]), c_0_39]), c_0_60])]), c_0_40])).
% 1.39/1.57  cnf(c_0_119, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.39/1.57  cnf(c_0_120, negated_conjecture, (esk3_3(esk5_0,esk6_0,k7_tmap_1(esk5_0,u1_struct_0(esk5_0)))=u1_struct_0(esk6_0)|k7_tmap_1(esk5_0,u1_struct_0(esk5_0))=k9_tmap_1(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109]), c_0_110])])).
% 1.39/1.57  cnf(c_0_121, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_111, c_0_62]), c_0_95]), c_0_92])).
% 1.39/1.57  cnf(c_0_122, plain, (X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk3_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk3_3(X1,X2,X3)))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.39/1.57  cnf(c_0_123, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk5_0),u1_struct_0(esk5_0),X3,X3)|v1_xboole_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_91]), c_0_91]), c_0_113])).
% 1.39/1.57  cnf(c_0_124, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~v1_tsep_1(esk6_0,esk5_0)|~m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_47])]), c_0_99]), c_0_100])])).
% 1.39/1.57  cnf(c_0_125, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),esk5_0,k8_tmap_1(esk5_0,esk6_0))|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117]), c_0_38]), c_0_47]), c_0_39])]), c_0_40]), c_0_118])).
% 1.39/1.57  cnf(c_0_126, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk5_0))=k9_tmap_1(esk5_0,esk6_0)|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_38]), c_0_91]), c_0_108]), c_0_91]), c_0_109]), c_0_110]), c_0_47]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_127, negated_conjecture, (v3_pre_topc(u1_struct_0(esk6_0),esk5_0)|~v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),esk5_0,k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_117]), c_0_38]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_128, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk5_0))=k9_tmap_1(esk5_0,esk6_0)|~r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),k7_tmap_1(esk5_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_120]), c_0_38]), c_0_91]), c_0_118]), c_0_91]), c_0_117]), c_0_91]), c_0_108]), c_0_91]), c_0_109]), c_0_110]), c_0_47]), c_0_39])]), c_0_40])).
% 1.39/1.57  cnf(c_0_129, negated_conjecture, (r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),k7_tmap_1(esk5_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_108]), c_0_109]), c_0_110])]), c_0_113])).
% 1.39/1.57  cnf(c_0_130, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~v1_tsep_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_98])])).
% 1.39/1.57  cnf(c_0_131, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 1.39/1.57  cnf(c_0_132, negated_conjecture, (v3_pre_topc(u1_struct_0(esk6_0),esk5_0)|~v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(esk5_0)),esk5_0,k8_tmap_1(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_74]), c_0_47])]), c_0_116])).
% 1.39/1.57  cnf(c_0_133, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk5_0))=k9_tmap_1(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129])])).
% 1.39/1.57  cnf(c_0_134, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk4_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.39/1.57  cnf(c_0_135, negated_conjecture, (m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_85])).
% 1.39/1.57  cnf(c_0_136, negated_conjecture, (v3_pre_topc(u1_struct_0(esk6_0),esk5_0)|~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_132, c_0_133])).
% 1.39/1.57  cnf(c_0_137, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|v1_tsep_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.39/1.57  cnf(c_0_138, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)|~v3_pre_topc(u1_struct_0(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_68]), c_0_47]), c_0_39])])).
% 1.39/1.57  cnf(c_0_139, negated_conjecture, (v3_pre_topc(u1_struct_0(esk6_0),esk5_0)|u1_struct_0(esk6_0)!=u1_struct_0(X1)|~v1_tsep_1(X1,esk5_0)|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_135]), c_0_39])])).
% 1.39/1.57  cnf(c_0_140, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_138])).
% 1.39/1.57  cnf(c_0_141, negated_conjecture, (v3_pre_topc(u1_struct_0(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_47])])).
% 1.39/1.57  cnf(c_0_142, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_140])])).
% 1.39/1.57  cnf(c_0_143, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_141]), c_0_117]), c_0_133]), c_0_118]), c_0_38]), c_0_47]), c_0_39])]), c_0_40]), c_0_142]), ['proof']).
% 1.39/1.57  # SZS output end CNFRefutation
% 1.39/1.57  # Proof object total steps             : 144
% 1.39/1.57  # Proof object clause steps            : 107
% 1.39/1.57  # Proof object formula steps           : 37
% 1.39/1.57  # Proof object conjectures             : 61
% 1.39/1.57  # Proof object clause conjectures      : 58
% 1.39/1.57  # Proof object formula conjectures     : 3
% 1.39/1.57  # Proof object initial clauses used    : 39
% 1.39/1.57  # Proof object initial formulas used   : 18
% 1.39/1.57  # Proof object generating inferences   : 61
% 1.39/1.57  # Proof object simplifying inferences  : 195
% 1.39/1.57  # Training examples: 0 positive, 0 negative
% 1.39/1.57  # Parsed axioms                        : 18
% 1.39/1.57  # Removed by relevancy pruning/SinE    : 0
% 1.39/1.57  # Initial clauses                      : 54
% 1.39/1.57  # Removed in clause preprocessing      : 0
% 1.39/1.57  # Initial clauses in saturation        : 54
% 1.39/1.57  # Processed clauses                    : 5990
% 1.39/1.57  # ...of these trivial                  : 536
% 1.39/1.57  # ...subsumed                          : 2836
% 1.39/1.57  # ...remaining for further processing  : 2617
% 1.39/1.57  # Other redundant clauses eliminated   : 0
% 1.39/1.57  # Clauses deleted for lack of memory   : 0
% 1.39/1.57  # Backward-subsumed                    : 131
% 1.39/1.57  # Backward-rewritten                   : 885
% 1.39/1.57  # Generated clauses                    : 50125
% 1.39/1.57  # ...of the previous two non-trivial   : 44326
% 1.39/1.57  # Contextual simplify-reflections      : 688
% 1.39/1.57  # Paramodulations                      : 50043
% 1.39/1.57  # Factorizations                       : 0
% 1.39/1.57  # Equation resolutions                 : 31
% 1.39/1.57  # Propositional unsat checks           : 0
% 1.39/1.57  #    Propositional check models        : 0
% 1.39/1.57  #    Propositional check unsatisfiable : 0
% 1.39/1.57  #    Propositional clauses             : 0
% 1.39/1.57  #    Propositional clauses after purity: 0
% 1.39/1.57  #    Propositional unsat core size     : 0
% 1.39/1.57  #    Propositional preprocessing time  : 0.000
% 1.39/1.57  #    Propositional encoding time       : 0.000
% 1.39/1.57  #    Propositional solver time         : 0.000
% 1.39/1.57  #    Success case prop preproc time    : 0.000
% 1.39/1.57  #    Success case prop encoding time   : 0.000
% 1.39/1.57  #    Success case prop solver time     : 0.000
% 1.39/1.57  # Current number of processed clauses  : 1550
% 1.39/1.57  #    Positive orientable unit clauses  : 141
% 1.39/1.57  #    Positive unorientable unit clauses: 0
% 1.39/1.57  #    Negative unit clauses             : 7
% 1.39/1.57  #    Non-unit-clauses                  : 1402
% 1.39/1.57  # Current number of unprocessed clauses: 37040
% 1.39/1.57  # ...number of literals in the above   : 183419
% 1.39/1.57  # Current number of archived formulas  : 0
% 1.39/1.57  # Current number of archived clauses   : 1067
% 1.39/1.57  # Clause-clause subsumption calls (NU) : 562606
% 1.39/1.57  # Rec. Clause-clause subsumption calls : 101684
% 1.39/1.57  # Non-unit clause-clause subsumptions  : 3559
% 1.39/1.57  # Unit Clause-clause subsumption calls : 14749
% 1.39/1.57  # Rewrite failures with RHS unbound    : 0
% 1.39/1.57  # BW rewrite match attempts            : 626
% 1.39/1.57  # BW rewrite match successes           : 46
% 1.39/1.57  # Condensation attempts                : 0
% 1.39/1.57  # Condensation successes               : 0
% 1.39/1.57  # Termbank termtop insertions          : 3003153
% 1.42/1.58  
% 1.42/1.58  # -------------------------------------------------
% 1.42/1.58  # User time                : 1.203 s
% 1.42/1.58  # System time              : 0.030 s
% 1.42/1.58  # Total time               : 1.233 s
% 1.42/1.58  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
