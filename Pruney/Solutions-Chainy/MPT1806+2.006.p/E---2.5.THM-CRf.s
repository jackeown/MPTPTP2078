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

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  122 (6214 expanded)
%              Number of clauses        :   91 (2148 expanded)
%              Number of leaves         :   15 (1549 expanded)
%              Depth                    :   17
%              Number of atoms          :  676 (59348 expanded)
%              Number of equality atoms :   76 (1589 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

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

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

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

fof(c_0_15,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X19 != k8_tmap_1(X17,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))
        | X20 != u1_struct_0(X18)
        | X19 = k6_tmap_1(X17,X20)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk1_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))
        | X19 = k8_tmap_1(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( esk1_3(X17,X18,X19) = u1_struct_0(X18)
        | X19 = k8_tmap_1(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( X19 != k6_tmap_1(X17,esk1_3(X17,X18,X19))
        | X19 = k8_tmap_1(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_16,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_pre_topc(X42,X41)
      | m1_subset_1(u1_struct_0(X42),k1_zfmisc_1(u1_struct_0(X41))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_17,plain,(
    ! [X37,X38] :
      ( ( u1_struct_0(k6_tmap_1(X37,X38)) = u1_struct_0(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( u1_pre_topc(k6_tmap_1(X37,X38)) = k5_tmap_1(X37,X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_18,negated_conjecture,(
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

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X33,X34] :
      ( ( v1_pre_topc(k8_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_pre_topc(X34,X33) )
      & ( v2_pre_topc(k8_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_pre_topc(X34,X33) )
      & ( l1_pre_topc(k8_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_pre_topc(X34,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_22,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | k7_tmap_1(X15,X16) = k6_partfun1(u1_struct_0(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

cnf(c_0_23,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).

cnf(c_0_25,plain,
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
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X43] :
      ( ~ l1_pre_topc(X43)
      | m1_pre_topc(X43,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_31,plain,(
    ! [X31,X32] :
      ( ( v1_funct_1(k7_tmap_1(X31,X32))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))) )
      & ( v1_funct_2(k7_tmap_1(X31,X32),u1_struct_0(X31),u1_struct_0(k6_tmap_1(X31,X32)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))) )
      & ( m1_subset_1(k7_tmap_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(k6_tmap_1(X31,X32)))))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_32,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X3))
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_38,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_39,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_tsep_1(X28,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | X29 != u1_struct_0(X28)
        | v3_pre_topc(X29,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk3_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))
        | v1_tsep_1(X28,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( esk3_2(X27,X28) = u1_struct_0(X28)
        | v1_tsep_1(X28,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ v3_pre_topc(esk3_2(X27,X28),X27)
        | v1_tsep_1(X28,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

fof(c_0_42,plain,(
    ! [X39,X40] :
      ( ( v1_funct_1(k7_tmap_1(X39,X40))
        | ~ v3_pre_topc(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v1_funct_2(k7_tmap_1(X39,X40),u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))
        | ~ v3_pre_topc(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v5_pre_topc(k7_tmap_1(X39,X40),X39,k6_tmap_1(X39,X40))
        | ~ v3_pre_topc(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( m1_subset_1(k7_tmap_1(X39,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))))
        | ~ v3_pre_topc(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ v1_funct_1(k7_tmap_1(X39,X40))
        | ~ v1_funct_2(k7_tmap_1(X39,X40),u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))
        | ~ v5_pre_topc(k7_tmap_1(X39,X40),X39,k6_tmap_1(X39,X40))
        | ~ m1_subset_1(k7_tmap_1(X39,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))))
        | v3_pre_topc(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).

fof(c_0_43,plain,(
    ! [X22,X23,X24,X25] :
      ( ( X24 != k9_tmap_1(X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))
        | X25 != u1_struct_0(X23)
        | r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X25)),X24,k7_tmap_1(X22,X25))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))))
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk2_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))
        | X24 = k9_tmap_1(X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))))
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( esk2_3(X22,X23,X24) = u1_struct_0(X23)
        | X24 = k9_tmap_1(X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))))
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,esk2_3(X22,X23,X24))),X24,k7_tmap_1(X22,esk2_3(X22,X23,X24)))
        | X24 = k9_tmap_1(X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))))
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(X1)) = k8_tmap_1(esk4_0,esk5_0)
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_46,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k7_tmap_1(X1,u1_struct_0(X1)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk4_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_49,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_50,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_51,plain,
    ( esk3_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_52,plain,(
    ! [X35,X36] :
      ( ( v1_funct_1(k9_tmap_1(X35,X36))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X35) )
      & ( v1_funct_2(k9_tmap_1(X35,X36),u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X35) )
      & ( m1_subset_1(k9_tmap_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)))))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_53,plain,
    ( v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( esk2_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk4_0,esk5_0)) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_33])])).

cnf(c_0_56,plain,
    ( m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_34]),c_0_48]),c_0_35])]),c_0_36])).

cnf(c_0_58,plain,
    ( v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_20])).

cnf(c_0_59,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_39])).

cnf(c_0_60,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_61,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( esk3_2(esk4_0,esk5_0) = u1_struct_0(esk5_0)
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_33]),c_0_35])])).

cnf(c_0_63,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_20])).

cnf(c_0_65,negated_conjecture,
    ( esk2_3(esk4_0,esk5_0,X1) = u1_struct_0(esk5_0)
    | X1 = k9_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_33]),c_0_57]),c_0_44]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_33]),c_0_57]),c_0_44]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_69,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_33]),c_0_35])])).

cnf(c_0_71,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_72,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ m1_pre_topc(esk5_0,esk4_0)
    | ~ v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
    | ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_57]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_77,negated_conjecture,
    ( esk2_3(esk4_0,esk5_0,k7_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_struct_0(esk5_0)
    | k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])])).

cnf(c_0_78,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_33]),c_0_35])])).

cnf(c_0_79,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_33]),c_0_35])])).

cnf(c_0_80,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_83,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_33])]),c_0_74])])).

cnf(c_0_84,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_45]),c_0_33])])).

cnf(c_0_85,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk4_0,esk5_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_33]),c_0_34]),c_0_55]),c_0_66]),c_0_55]),c_0_67]),c_0_68]),c_0_35])]),c_0_36])).

cnf(c_0_86,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_33])).

cnf(c_0_87,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X2))
    | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_88,negated_conjecture,
    ( k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_79]),c_0_48]),c_0_34]),c_0_35])]),c_0_36])).

fof(c_0_89,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r1_funct_2(X9,X10,X11,X12,X13,X14)
        | X13 = X14
        | v1_xboole_0(X10)
        | v1_xboole_0(X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X9,X10)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( X13 != X14
        | r1_funct_2(X9,X10,X11,X12,X13,X14)
        | v1_xboole_0(X10)
        | v1_xboole_0(X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X9,X10)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_90,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1))
    | X1 != u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_33]),c_0_34]),c_0_82]),c_0_74]),c_0_35])]),c_0_36])).

cnf(c_0_91,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_82])]),c_0_81])])).

cnf(c_0_92,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_93,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_87,c_0_40]),c_0_49]),c_0_46])).

cnf(c_0_94,negated_conjecture,
    ( k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk4_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_57])).

cnf(c_0_95,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_96,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_97,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_98,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1))
    | X1 != u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_90,c_0_55])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_70])).

cnf(c_0_101,negated_conjecture,
    ( v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)
    | v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_34]),c_0_35])]),c_0_36]),c_0_79])).

cnf(c_0_102,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_62]),c_0_33]),c_0_35])])).

cnf(c_0_103,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_104,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_105,negated_conjecture,
    ( X1 = k7_tmap_1(esk4_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),X1,k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_66]),c_0_67]),c_0_68])])).

cnf(c_0_106,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_57]),c_0_44]),c_0_100])])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_81,c_0_55])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_55])).

cnf(c_0_109,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_62]),c_0_102])).

cnf(c_0_110,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_111,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk4_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_108]),c_0_74])])).

cnf(c_0_112,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_45]),c_0_33])])).

cnf(c_0_113,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_35])]),c_0_36])).

cnf(c_0_114,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_115,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk4_0)
    | u1_struct_0(esk5_0) != u1_struct_0(X1)
    | ~ v1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_100]),c_0_35])])).

cnf(c_0_116,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113]),c_0_114])).

cnf(c_0_117,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_45]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_118,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_33])])).

cnf(c_0_120,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_116])])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119]),c_0_33])]),c_0_120]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.59/0.77  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.59/0.77  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.59/0.77  #
% 0.59/0.77  # Preprocessing time       : 0.042 s
% 0.59/0.77  
% 0.59/0.77  # Proof found!
% 0.59/0.77  # SZS status Theorem
% 0.59/0.77  # SZS output start CNFRefutation
% 0.59/0.77  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.59/0.77  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.59/0.77  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.59/0.77  fof(t122_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t122_tmap_1)).
% 0.59/0.77  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.59/0.77  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.59/0.77  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.59/0.77  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.59/0.77  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.59/0.77  fof(t113_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.59/0.77  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.59/0.77  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.59/0.77  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.59/0.77  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.59/0.77  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.59/0.77  fof(c_0_15, plain, ![X17, X18, X19, X20]:((X19!=k8_tmap_1(X17,X18)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|(X20!=u1_struct_0(X18)|X19=k6_tmap_1(X17,X20)))|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((m1_subset_1(esk1_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((esk1_3(X17,X18,X19)=u1_struct_0(X18)|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(X19!=k6_tmap_1(X17,esk1_3(X17,X18,X19))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.59/0.77  fof(c_0_16, plain, ![X41, X42]:(~l1_pre_topc(X41)|(~m1_pre_topc(X42,X41)|m1_subset_1(u1_struct_0(X42),k1_zfmisc_1(u1_struct_0(X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.59/0.77  fof(c_0_17, plain, ![X37, X38]:((u1_struct_0(k6_tmap_1(X37,X38))=u1_struct_0(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(u1_pre_topc(k6_tmap_1(X37,X38))=k5_tmap_1(X37,X38)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.59/0.77  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t122_tmap_1])).
% 0.59/0.77  cnf(c_0_19, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.59/0.77  cnf(c_0_20, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.77  fof(c_0_21, plain, ![X33, X34]:(((v1_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))&(v2_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33))))&(l1_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.59/0.77  fof(c_0_22, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|k7_tmap_1(X15,X16)=k6_partfun1(u1_struct_0(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.59/0.77  cnf(c_0_23, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.59/0.77  fof(c_0_24, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_pre_topc(esk5_0,esk4_0)&((~v1_tsep_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|(~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))))&(((((v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0))&(v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|v1_tsep_1(esk5_0,esk4_0)))&(v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)))&(m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|v1_tsep_1(esk5_0,esk4_0)))&((((v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|m1_pre_topc(esk5_0,esk4_0))&(v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|m1_pre_topc(esk5_0,esk4_0)))&(v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|m1_pre_topc(esk5_0,esk4_0)))&(m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|m1_pre_topc(esk5_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).
% 0.59/0.77  cnf(c_0_25, plain, (X1=k6_tmap_1(X2,u1_struct_0(X3))|v2_struct_0(X2)|u1_struct_0(X3)!=u1_struct_0(X4)|X1!=k8_tmap_1(X2,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.59/0.77  cnf(c_0_26, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.59/0.77  cnf(c_0_27, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.59/0.77  cnf(c_0_28, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.59/0.77  cnf(c_0_29, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.59/0.77  fof(c_0_30, plain, ![X43]:(~l1_pre_topc(X43)|m1_pre_topc(X43,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.59/0.77  fof(c_0_31, plain, ![X31, X32]:(((v1_funct_1(k7_tmap_1(X31,X32))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))))&(v1_funct_2(k7_tmap_1(X31,X32),u1_struct_0(X31),u1_struct_0(k6_tmap_1(X31,X32)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))))&(m1_subset_1(k7_tmap_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(k6_tmap_1(X31,X32)))))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.59/0.77  cnf(c_0_32, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 0.59/0.77  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.77  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.77  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.77  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.77  cnf(c_0_37, plain, (k8_tmap_1(X1,X2)=k6_tmap_1(X1,u1_struct_0(X3))|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.59/0.77  cnf(c_0_38, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 0.59/0.77  cnf(c_0_39, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.59/0.77  cnf(c_0_40, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.59/0.77  fof(c_0_41, plain, ![X27, X28, X29]:((~v1_tsep_1(X28,X27)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|(X29!=u1_struct_0(X28)|v3_pre_topc(X29,X27)))|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&((m1_subset_1(esk3_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&((esk3_2(X27,X28)=u1_struct_0(X28)|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&(~v3_pre_topc(esk3_2(X27,X28),X27)|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.59/0.77  fof(c_0_42, plain, ![X39, X40]:(((((v1_funct_1(k7_tmap_1(X39,X40))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(v1_funct_2(k7_tmap_1(X39,X40),u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(v5_pre_topc(k7_tmap_1(X39,X40),X39,k6_tmap_1(X39,X40))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(m1_subset_1(k7_tmap_1(X39,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(~v1_funct_1(k7_tmap_1(X39,X40))|~v1_funct_2(k7_tmap_1(X39,X40),u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))|~v5_pre_topc(k7_tmap_1(X39,X40),X39,k6_tmap_1(X39,X40))|~m1_subset_1(k7_tmap_1(X39,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))))|v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).
% 0.59/0.77  fof(c_0_43, plain, ![X22, X23, X24, X25]:((X24!=k9_tmap_1(X22,X23)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))|(X25!=u1_struct_0(X23)|r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X25)),X24,k7_tmap_1(X22,X25))))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((m1_subset_1(esk2_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((esk2_3(X22,X23,X24)=u1_struct_0(X23)|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,esk2_3(X22,X23,X24))),X24,k7_tmap_1(X22,esk2_3(X22,X23,X24)))|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.59/0.77  cnf(c_0_44, negated_conjecture, (u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_45, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(X1))=k8_tmap_1(esk4_0,esk5_0)|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_46, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.59/0.77  cnf(c_0_47, plain, (k7_tmap_1(X1,u1_struct_0(X1))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.59/0.77  cnf(c_0_48, negated_conjecture, (k6_partfun1(u1_struct_0(esk4_0))=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_49, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.59/0.77  cnf(c_0_50, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 0.59/0.77  cnf(c_0_51, plain, (esk3_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.59/0.77  fof(c_0_52, plain, ![X35, X36]:(((v1_funct_1(k9_tmap_1(X35,X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))&(v1_funct_2(k9_tmap_1(X35,X36),u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35))))&(m1_subset_1(k9_tmap_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)))))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.59/0.77  cnf(c_0_53, plain, (v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.59/0.77  cnf(c_0_54, plain, (esk2_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.59/0.77  cnf(c_0_55, negated_conjecture, (u1_struct_0(k8_tmap_1(esk4_0,esk5_0))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_33])])).
% 0.59/0.77  cnf(c_0_56, plain, (m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_20])).
% 0.59/0.77  cnf(c_0_57, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_34]), c_0_48]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_58, plain, (v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_49, c_0_20])).
% 0.59/0.77  cnf(c_0_59, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_39])).
% 0.59/0.77  cnf(c_0_60, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.59/0.77  cnf(c_0_61, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.59/0.77  cnf(c_0_62, negated_conjecture, (esk3_2(esk4_0,esk5_0)=u1_struct_0(esk5_0)|v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_33]), c_0_35])])).
% 0.59/0.77  cnf(c_0_63, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.59/0.77  cnf(c_0_64, plain, (v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_53, c_0_20])).
% 0.59/0.77  cnf(c_0_65, negated_conjecture, (esk2_3(esk4_0,esk5_0,X1)=u1_struct_0(esk5_0)|X1=k9_tmap_1(esk4_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk4_0))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_66, negated_conjecture, (m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_33]), c_0_57]), c_0_44]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_67, negated_conjecture, (v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_33]), c_0_57]), c_0_44]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_68, negated_conjecture, (v1_funct_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_69, plain, (v3_pre_topc(u1_struct_0(X1),X2)|u1_struct_0(X1)!=u1_struct_0(X3)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_60, c_0_20])).
% 0.59/0.77  cnf(c_0_70, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_33]), c_0_35])])).
% 0.59/0.77  cnf(c_0_71, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.59/0.77  cnf(c_0_72, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.59/0.77  cnf(c_0_73, negated_conjecture, (~v1_tsep_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.77  cnf(c_0_74, negated_conjecture, (v1_funct_1(k9_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_75, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))|~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_57]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_76, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.59/0.77  cnf(c_0_77, negated_conjecture, (esk2_3(esk4_0,esk5_0,k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_struct_0(esk5_0)|k7_tmap_1(esk4_0,u1_struct_0(esk4_0))=k9_tmap_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68])])).
% 0.59/0.77  cnf(c_0_78, negated_conjecture, (v3_pre_topc(u1_struct_0(X1),esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_33]), c_0_35])])).
% 0.59/0.77  cnf(c_0_79, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_33]), c_0_35])])).
% 0.59/0.77  cnf(c_0_80, plain, (r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))|v2_struct_0(X2)|X1!=k9_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.59/0.77  cnf(c_0_81, negated_conjecture, (m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_82, negated_conjecture, (v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_83, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_33])]), c_0_74])])).
% 0.59/0.77  cnf(c_0_84, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_45]), c_0_33])])).
% 0.59/0.77  cnf(c_0_85, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk4_0))=k9_tmap_1(esk4_0,esk5_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_33]), c_0_34]), c_0_55]), c_0_66]), c_0_55]), c_0_67]), c_0_68]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_86, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_78, c_0_33])).
% 0.59/0.77  cnf(c_0_87, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|~v1_funct_1(k7_tmap_1(X1,X2))|~v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|~v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|~m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.59/0.77  cnf(c_0_88, negated_conjecture, (k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))|v1_tsep_1(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_79]), c_0_48]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  fof(c_0_89, plain, ![X9, X10, X11, X12, X13, X14]:((~r1_funct_2(X9,X10,X11,X12,X13,X14)|X13=X14|(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(X13!=X14|r1_funct_2(X9,X10,X11,X12,X13,X14)|(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.59/0.77  cnf(c_0_90, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1))|X1!=u1_struct_0(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_33]), c_0_34]), c_0_82]), c_0_74]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_91, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_82])]), c_0_81])])).
% 0.59/0.77  cnf(c_0_92, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 0.59/0.77  cnf(c_0_93, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_87, c_0_40]), c_0_49]), c_0_46])).
% 0.59/0.77  cnf(c_0_94, negated_conjecture, (k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))|v1_tsep_1(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_88, c_0_57])).
% 0.59/0.77  cnf(c_0_95, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk3_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.59/0.77  fof(c_0_96, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.59/0.77  fof(c_0_97, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.59/0.77  cnf(c_0_98, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.59/0.77  cnf(c_0_99, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(k6_tmap_1(esk4_0,X1)),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,X1))|X1!=u1_struct_0(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[c_0_90, c_0_55])).
% 0.59/0.77  cnf(c_0_100, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_70])).
% 0.59/0.77  cnf(c_0_101, negated_conjecture, (v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)|v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_34]), c_0_35])]), c_0_36]), c_0_79])).
% 0.59/0.77  cnf(c_0_102, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_62]), c_0_33]), c_0_35])])).
% 0.59/0.77  cnf(c_0_103, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.59/0.77  cnf(c_0_104, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.59/0.77  cnf(c_0_105, negated_conjecture, (X1=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),X1,k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_66]), c_0_67]), c_0_68])])).
% 0.59/0.77  cnf(c_0_106, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k9_tmap_1(esk4_0,esk5_0),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_57]), c_0_44]), c_0_100])])).
% 0.59/0.77  cnf(c_0_107, negated_conjecture, (m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_81, c_0_55])).
% 0.59/0.77  cnf(c_0_108, negated_conjecture, (v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_82, c_0_55])).
% 0.59/0.77  cnf(c_0_109, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_62]), c_0_102])).
% 0.59/0.77  cnf(c_0_110, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.59/0.77  cnf(c_0_111, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk4_0))=k9_tmap_1(esk4_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107]), c_0_108]), c_0_74])])).
% 0.59/0.77  cnf(c_0_112, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_45]), c_0_33])])).
% 0.59/0.77  cnf(c_0_113, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk4_0))=k9_tmap_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_114, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.77  cnf(c_0_115, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk4_0)|u1_struct_0(esk5_0)!=u1_struct_0(X1)|~v1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_100]), c_0_35])])).
% 0.59/0.77  cnf(c_0_116, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113]), c_0_114])).
% 0.59/0.77  cnf(c_0_117, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k8_tmap_1(esk4_0,esk5_0))|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~v3_pre_topc(u1_struct_0(X1),esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_45]), c_0_34]), c_0_35])]), c_0_36])).
% 0.59/0.77  cnf(c_0_118, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k9_tmap_1(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_57, c_0_113])).
% 0.59/0.77  cnf(c_0_119, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_33])])).
% 0.59/0.77  cnf(c_0_120, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_116])])).
% 0.59/0.77  cnf(c_0_121, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119]), c_0_33])]), c_0_120]), ['proof']).
% 0.59/0.77  # SZS output end CNFRefutation
% 0.59/0.77  # Proof object total steps             : 122
% 0.59/0.77  # Proof object clause steps            : 91
% 0.59/0.77  # Proof object formula steps           : 31
% 0.59/0.77  # Proof object conjectures             : 55
% 0.59/0.77  # Proof object clause conjectures      : 52
% 0.59/0.77  # Proof object formula conjectures     : 3
% 0.59/0.77  # Proof object initial clauses used    : 32
% 0.59/0.77  # Proof object initial formulas used   : 15
% 0.59/0.77  # Proof object generating inferences   : 49
% 0.59/0.77  # Proof object simplifying inferences  : 153
% 0.59/0.77  # Training examples: 0 positive, 0 negative
% 0.59/0.77  # Parsed axioms                        : 15
% 0.59/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.59/0.77  # Initial clauses                      : 48
% 0.59/0.77  # Removed in clause preprocessing      : 0
% 0.59/0.77  # Initial clauses in saturation        : 48
% 0.59/0.77  # Processed clauses                    : 1959
% 0.59/0.77  # ...of these trivial                  : 106
% 0.59/0.77  # ...subsumed                          : 1030
% 0.59/0.77  # ...remaining for further processing  : 823
% 0.59/0.77  # Other redundant clauses eliminated   : 1
% 0.59/0.77  # Clauses deleted for lack of memory   : 0
% 0.59/0.77  # Backward-subsumed                    : 77
% 0.59/0.77  # Backward-rewritten                   : 236
% 0.59/0.77  # Generated clauses                    : 6211
% 0.59/0.77  # ...of the previous two non-trivial   : 5659
% 0.59/0.77  # Contextual simplify-reflections      : 163
% 0.59/0.77  # Paramodulations                      : 6181
% 0.59/0.77  # Factorizations                       : 16
% 0.59/0.77  # Equation resolutions                 : 14
% 0.59/0.77  # Propositional unsat checks           : 0
% 0.59/0.77  #    Propositional check models        : 0
% 0.59/0.77  #    Propositional check unsatisfiable : 0
% 0.59/0.77  #    Propositional clauses             : 0
% 0.59/0.77  #    Propositional clauses after purity: 0
% 0.59/0.77  #    Propositional unsat core size     : 0
% 0.59/0.77  #    Propositional preprocessing time  : 0.000
% 0.59/0.77  #    Propositional encoding time       : 0.000
% 0.59/0.77  #    Propositional solver time         : 0.000
% 0.59/0.77  #    Success case prop preproc time    : 0.000
% 0.59/0.77  #    Success case prop encoding time   : 0.000
% 0.59/0.77  #    Success case prop solver time     : 0.000
% 0.59/0.77  # Current number of processed clauses  : 509
% 0.59/0.77  #    Positive orientable unit clauses  : 29
% 0.59/0.77  #    Positive unorientable unit clauses: 0
% 0.59/0.77  #    Negative unit clauses             : 2
% 0.59/0.77  #    Non-unit-clauses                  : 478
% 0.59/0.77  # Current number of unprocessed clauses: 3558
% 0.59/0.77  # ...number of literals in the above   : 19429
% 0.59/0.77  # Current number of archived formulas  : 0
% 0.59/0.77  # Current number of archived clauses   : 313
% 0.59/0.77  # Clause-clause subsumption calls (NU) : 105358
% 0.59/0.77  # Rec. Clause-clause subsumption calls : 15567
% 0.59/0.77  # Non-unit clause-clause subsumptions  : 1258
% 0.59/0.77  # Unit Clause-clause subsumption calls : 806
% 0.59/0.77  # Rewrite failures with RHS unbound    : 0
% 0.59/0.77  # BW rewrite match attempts            : 29
% 0.59/0.77  # BW rewrite match successes           : 15
% 0.59/0.77  # Condensation attempts                : 0
% 0.59/0.77  # Condensation successes               : 0
% 0.59/0.77  # Termbank termtop insertions          : 268287
% 0.59/0.77  
% 0.59/0.77  # -------------------------------------------------
% 0.59/0.77  # User time                : 0.419 s
% 0.59/0.77  # System time              : 0.011 s
% 0.59/0.77  # Total time               : 0.430 s
% 0.59/0.77  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
