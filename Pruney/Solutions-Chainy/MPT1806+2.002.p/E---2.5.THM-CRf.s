%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:29 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  151 (23082 expanded)
%              Number of clauses        :  120 (8049 expanded)
%              Number of leaves         :   15 (5772 expanded)
%              Depth                    :   19
%              Number of atoms          :  752 (216756 expanded)
%              Number of equality atoms :   98 (6258 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
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
    ! [X43,X44] :
      ( ~ l1_pre_topc(X43)
      | ~ m1_pre_topc(X44,X43)
      | m1_subset_1(u1_struct_0(X44),k1_zfmisc_1(u1_struct_0(X43))) ) ),
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
    ! [X45] :
      ( ~ l1_pre_topc(X45)
      | m1_pre_topc(X45,X45) ) ),
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

fof(c_0_32,plain,(
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

cnf(c_0_33,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X3))
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_39,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_40,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
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

cnf(c_0_43,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
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

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(X1)) = k8_tmap_1(esk4_0,esk5_0)
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_47,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,plain,
    ( k7_tmap_1(X1,u1_struct_0(X1)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk4_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_50,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_20])).

fof(c_0_52,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( v1_xboole_0(X10)
      | v1_xboole_0(X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,X9,X10)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,X11,X12)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | r1_funct_2(X9,X10,X11,X12,X13,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_funct_2])])])).

cnf(c_0_53,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_56,plain,(
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

cnf(c_0_57,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_34]),c_0_36])])).

cnf(c_0_58,plain,
    ( esk2_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk4_0,esk5_0)) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34])])).

cnf(c_0_60,plain,
    ( m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_35]),c_0_49]),c_0_36])]),c_0_37])).

cnf(c_0_62,plain,
    ( v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_20])).

cnf(c_0_63,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_40])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_funct_2(X4,X1,X6,X2,X3,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X6,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_68,plain,
    ( k8_tmap_1(X1,X1) = k6_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40])).

cnf(c_0_69,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X2))
    | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_57]),c_0_49]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_71,plain,
    ( esk3_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_72,negated_conjecture,
    ( esk2_3(esk4_0,esk5_0,X1) = u1_struct_0(esk5_0)
    | X1 = k9_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_34]),c_0_61]),c_0_45]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_34]),c_0_61]),c_0_45]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_76,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)),X3,X3)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67])])).

cnf(c_0_77,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X1))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_40])).

cnf(c_0_78,plain,
    ( k6_tmap_1(X1,u1_struct_0(X1)) = k8_tmap_1(X1,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_40])).

cnf(c_0_79,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_69,c_0_41]),c_0_50]),c_0_47])).

cnf(c_0_80,negated_conjecture,
    ( k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk4_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_70,c_0_61])).

cnf(c_0_81,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_82,negated_conjecture,
    ( esk3_2(esk4_0,esk5_0) = u1_struct_0(esk5_0)
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_34]),c_0_36])])).

fof(c_0_83,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_84,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_85,plain,
    ( X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk2_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk2_3(X1,X2,X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_86,negated_conjecture,
    ( esk2_3(esk4_0,esk5_0,k7_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_struct_0(esk5_0)
    | k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75])])).

cnf(c_0_87,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),X3,X3)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_59]),c_0_59])).

cnf(c_0_88,plain,
    ( m1_subset_1(k9_tmap_1(X1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_89,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_90,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_91,plain,
    ( v1_funct_2(k9_tmap_1(X1,X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_40])).

cnf(c_0_92,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_93,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_40])).

cnf(c_0_94,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_40])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k8_tmap_1(X1,X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_96,negated_conjecture,
    ( v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)
    | v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_35]),c_0_36])]),c_0_37]),c_0_57])).

cnf(c_0_97,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_34]),c_0_36])])).

cnf(c_0_98,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_99,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_100,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk4_0,esk5_0)
    | ~ r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k7_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_34]),c_0_35]),c_0_59]),c_0_45]),c_0_61]),c_0_59]),c_0_73]),c_0_59]),c_0_74]),c_0_75]),c_0_36])]),c_0_37])).

cnf(c_0_101,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_73]),c_0_74]),c_0_75])])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk4_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk4_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_103,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk4_0,esk4_0)) = u1_struct_0(esk4_0) ),
    inference(rw,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_104,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk4_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_105,plain,
    ( v1_funct_1(k9_tmap_1(X1,X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_40])).

cnf(c_0_106,negated_conjecture,
    ( esk1_3(esk4_0,esk5_0,X1) = u1_struct_0(esk5_0)
    | X1 = k8_tmap_1(esk4_0,esk5_0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_107,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_108,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_109,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_110,negated_conjecture,
    ( ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ m1_pre_topc(esk5_0,esk4_0)
    | ~ v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
    | ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_111,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_82]),c_0_97])).

cnf(c_0_112,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_113,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk4_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk4_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_115,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk4_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_104,c_0_103])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_117,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_118,negated_conjecture,
    ( esk1_3(esk4_0,esk5_0,k8_tmap_1(esk4_0,esk4_0)) = u1_struct_0(esk5_0)
    | k8_tmap_1(esk4_0,esk5_0) = k8_tmap_1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108]),c_0_109])])).

cnf(c_0_119,plain,
    ( v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_120,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_34])]),c_0_67])])).

cnf(c_0_121,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_46]),c_0_34])])).

cnf(c_0_122,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_36])]),c_0_37])).

cnf(c_0_123,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_124,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_125,negated_conjecture,
    ( esk2_3(esk4_0,esk5_0,k9_tmap_1(esk4_0,esk4_0)) = u1_struct_0(esk5_0)
    | k9_tmap_1(esk4_0,esk5_0) = k9_tmap_1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_114]),c_0_115]),c_0_116])])).

cnf(c_0_126,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_127,negated_conjecture,
    ( k8_tmap_1(esk4_0,esk5_0) = k8_tmap_1(esk4_0,esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_107]),c_0_34]),c_0_108]),c_0_35]),c_0_109]),c_0_36])]),c_0_37])).

cnf(c_0_128,plain,
    ( v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_119,c_0_20])).

cnf(c_0_129,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_66])]),c_0_65])])).

cnf(c_0_130,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122]),c_0_123])).

cnf(c_0_131,negated_conjecture,
    ( k9_tmap_1(esk4_0,esk5_0) = k9_tmap_1(esk4_0,esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_34]),c_0_35]),c_0_59]),c_0_114]),c_0_59]),c_0_115]),c_0_116]),c_0_36])]),c_0_37])).

cnf(c_0_132,negated_conjecture,
    ( k7_tmap_1(esk4_0,X1) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_49]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_133,negated_conjecture,
    ( k8_tmap_1(esk4_0,esk5_0) = k8_tmap_1(esk4_0,esk4_0)
    | v3_pre_topc(u1_struct_0(esk5_0),esk4_0)
    | u1_struct_0(esk5_0) != u1_struct_0(X1)
    | ~ v1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_36])])).

cnf(c_0_134,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_46]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_135,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_122])).

cnf(c_0_136,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130])])).

cnf(c_0_137,negated_conjecture,
    ( k9_tmap_1(esk4_0,esk5_0) = k9_tmap_1(esk4_0,esk4_0)
    | v3_pre_topc(u1_struct_0(esk5_0),esk4_0)
    | u1_struct_0(esk5_0) != u1_struct_0(X1)
    | ~ v1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_131]),c_0_36])])).

cnf(c_0_138,negated_conjecture,
    ( k7_tmap_1(esk4_0,X1) = k7_tmap_1(esk4_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_132,c_0_61])).

cnf(c_0_139,negated_conjecture,
    ( k8_tmap_1(esk4_0,esk5_0) = k8_tmap_1(esk4_0,esk4_0)
    | v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_130]),c_0_34])])).

cnf(c_0_140,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_34])]),c_0_136])).

cnf(c_0_141,negated_conjecture,
    ( k9_tmap_1(esk4_0,esk5_0) = k9_tmap_1(esk4_0,esk4_0)
    | v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_130]),c_0_34])])).

cnf(c_0_142,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(X1)) = k7_tmap_1(esk4_0,u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_20]),c_0_36])])).

cnf(c_0_143,negated_conjecture,
    ( k8_tmap_1(esk4_0,esk5_0) = k8_tmap_1(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( k9_tmap_1(esk4_0,esk5_0) = k9_tmap_1(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_141,c_0_140])).

cnf(c_0_145,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_142])).

cnf(c_0_146,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk4_0),esk4_0,k8_tmap_1(esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_143]),c_0_144])).

cnf(c_0_147,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_126,c_0_20])).

cnf(c_0_148,negated_conjecture,
    ( u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_122]),c_0_144]),c_0_143]),c_0_146])).

cnf(c_0_149,negated_conjecture,
    ( u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_130]),c_0_34]),c_0_36])]),c_0_148])).

cnf(c_0_150,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_149,c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:10:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.68  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.47/0.68  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.47/0.68  #
% 0.47/0.68  # Preprocessing time       : 0.044 s
% 0.47/0.68  
% 0.47/0.68  # Proof found!
% 0.47/0.68  # SZS status Theorem
% 0.47/0.68  # SZS output start CNFRefutation
% 0.47/0.68  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.47/0.68  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.47/0.68  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.47/0.68  fof(t122_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t122_tmap_1)).
% 0.47/0.68  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.47/0.68  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.47/0.68  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.47/0.68  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.47/0.68  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.47/0.68  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.47/0.68  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.47/0.68  fof(reflexivity_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>r1_funct_2(X1,X2,X3,X4,X5,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 0.47/0.68  fof(t113_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.47/0.68  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.47/0.68  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.47/0.68  fof(c_0_15, plain, ![X17, X18, X19, X20]:((X19!=k8_tmap_1(X17,X18)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|(X20!=u1_struct_0(X18)|X19=k6_tmap_1(X17,X20)))|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((m1_subset_1(esk1_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((esk1_3(X17,X18,X19)=u1_struct_0(X18)|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(X19!=k6_tmap_1(X17,esk1_3(X17,X18,X19))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.47/0.68  fof(c_0_16, plain, ![X43, X44]:(~l1_pre_topc(X43)|(~m1_pre_topc(X44,X43)|m1_subset_1(u1_struct_0(X44),k1_zfmisc_1(u1_struct_0(X43))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.47/0.68  fof(c_0_17, plain, ![X37, X38]:((u1_struct_0(k6_tmap_1(X37,X38))=u1_struct_0(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(u1_pre_topc(k6_tmap_1(X37,X38))=k5_tmap_1(X37,X38)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.47/0.68  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t122_tmap_1])).
% 0.47/0.68  cnf(c_0_19, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.68  cnf(c_0_20, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.68  fof(c_0_21, plain, ![X33, X34]:(((v1_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))&(v2_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33))))&(l1_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.47/0.68  fof(c_0_22, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|k7_tmap_1(X15,X16)=k6_partfun1(u1_struct_0(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.47/0.68  cnf(c_0_23, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.68  fof(c_0_24, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_pre_topc(esk5_0,esk4_0)&((~v1_tsep_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|(~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))))&(((((v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0))&(v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|v1_tsep_1(esk5_0,esk4_0)))&(v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)))&(m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|v1_tsep_1(esk5_0,esk4_0)))&((((v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|m1_pre_topc(esk5_0,esk4_0))&(v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|m1_pre_topc(esk5_0,esk4_0)))&(v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|m1_pre_topc(esk5_0,esk4_0)))&(m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|m1_pre_topc(esk5_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).
% 0.47/0.68  cnf(c_0_25, plain, (X1=k6_tmap_1(X2,u1_struct_0(X3))|v2_struct_0(X2)|u1_struct_0(X3)!=u1_struct_0(X4)|X1!=k8_tmap_1(X2,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.47/0.68  cnf(c_0_26, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.68  cnf(c_0_27, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.68  cnf(c_0_28, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.68  cnf(c_0_29, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.68  fof(c_0_30, plain, ![X45]:(~l1_pre_topc(X45)|m1_pre_topc(X45,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.47/0.68  fof(c_0_31, plain, ![X31, X32]:(((v1_funct_1(k7_tmap_1(X31,X32))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))))&(v1_funct_2(k7_tmap_1(X31,X32),u1_struct_0(X31),u1_struct_0(k6_tmap_1(X31,X32)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))))&(m1_subset_1(k7_tmap_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(k6_tmap_1(X31,X32)))))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.47/0.68  fof(c_0_32, plain, ![X27, X28, X29]:((~v1_tsep_1(X28,X27)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|(X29!=u1_struct_0(X28)|v3_pre_topc(X29,X27)))|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&((m1_subset_1(esk3_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&((esk3_2(X27,X28)=u1_struct_0(X28)|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&(~v3_pre_topc(esk3_2(X27,X28),X27)|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.47/0.68  cnf(c_0_33, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 0.47/0.68  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.68  cnf(c_0_35, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.68  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.68  cnf(c_0_37, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.68  cnf(c_0_38, plain, (k8_tmap_1(X1,X2)=k6_tmap_1(X1,u1_struct_0(X3))|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.47/0.68  cnf(c_0_39, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 0.47/0.68  cnf(c_0_40, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.47/0.68  cnf(c_0_41, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.68  fof(c_0_42, plain, ![X35, X36]:(((v1_funct_1(k9_tmap_1(X35,X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))&(v1_funct_2(k9_tmap_1(X35,X36),u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35))))&(m1_subset_1(k9_tmap_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)))))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.47/0.68  cnf(c_0_43, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.68  fof(c_0_44, plain, ![X22, X23, X24, X25]:((X24!=k9_tmap_1(X22,X23)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))|(X25!=u1_struct_0(X23)|r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X25)),X24,k7_tmap_1(X22,X25))))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((m1_subset_1(esk2_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((esk2_3(X22,X23,X24)=u1_struct_0(X23)|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,esk2_3(X22,X23,X24))),X24,k7_tmap_1(X22,esk2_3(X22,X23,X24)))|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.47/0.68  cnf(c_0_45, negated_conjecture, (u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_46, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(X1))=k8_tmap_1(esk4_0,esk5_0)|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_47, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.68  cnf(c_0_48, plain, (k7_tmap_1(X1,u1_struct_0(X1))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.47/0.68  cnf(c_0_49, negated_conjecture, (k6_partfun1(u1_struct_0(esk4_0))=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_50, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.68  cnf(c_0_51, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_20])).
% 0.47/0.68  fof(c_0_52, plain, ![X9, X10, X11, X12, X13, X14]:(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|r1_funct_2(X9,X10,X11,X12,X13,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_funct_2])])])).
% 0.47/0.68  cnf(c_0_53, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.68  cnf(c_0_54, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.68  cnf(c_0_55, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.68  fof(c_0_56, plain, ![X39, X40]:(((((v1_funct_1(k7_tmap_1(X39,X40))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(v1_funct_2(k7_tmap_1(X39,X40),u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(v5_pre_topc(k7_tmap_1(X39,X40),X39,k6_tmap_1(X39,X40))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(m1_subset_1(k7_tmap_1(X39,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(~v1_funct_1(k7_tmap_1(X39,X40))|~v1_funct_2(k7_tmap_1(X39,X40),u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))|~v5_pre_topc(k7_tmap_1(X39,X40),X39,k6_tmap_1(X39,X40))|~m1_subset_1(k7_tmap_1(X39,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))))|v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).
% 0.47/0.68  cnf(c_0_57, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_34]), c_0_36])])).
% 0.47/0.68  cnf(c_0_58, plain, (esk2_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.47/0.68  cnf(c_0_59, negated_conjecture, (u1_struct_0(k8_tmap_1(esk4_0,esk5_0))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_34])])).
% 0.47/0.68  cnf(c_0_60, plain, (m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_47, c_0_20])).
% 0.47/0.68  cnf(c_0_61, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_35]), c_0_49]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_62, plain, (v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_20])).
% 0.47/0.68  cnf(c_0_63, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_51, c_0_40])).
% 0.47/0.68  cnf(c_0_64, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_funct_2(X4,X1,X6,X2,X3,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X5)|~v1_funct_2(X5,X6,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X2)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.47/0.68  cnf(c_0_65, negated_conjecture, (m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_66, negated_conjecture, (v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_67, negated_conjecture, (v1_funct_1(k9_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_68, plain, (k8_tmap_1(X1,X1)=k6_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X1)|u1_struct_0(X2)!=u1_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_40])).
% 0.47/0.68  cnf(c_0_69, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|~v1_funct_1(k7_tmap_1(X1,X2))|~v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|~v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|~m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.47/0.68  cnf(c_0_70, negated_conjecture, (k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))|v1_tsep_1(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_57]), c_0_49]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_71, plain, (esk3_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.68  cnf(c_0_72, negated_conjecture, (esk2_3(esk4_0,esk5_0,X1)=u1_struct_0(esk5_0)|X1=k9_tmap_1(esk4_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk4_0))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_73, negated_conjecture, (m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_34]), c_0_61]), c_0_45]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_74, negated_conjecture, (v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_34]), c_0_61]), c_0_45]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_75, negated_conjecture, (v1_funct_1(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_76, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)),X3,X3)|v1_xboole_0(u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|v1_xboole_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67])])).
% 0.47/0.68  cnf(c_0_77, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X1)))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_40])).
% 0.47/0.68  cnf(c_0_78, plain, (k6_tmap_1(X1,u1_struct_0(X1))=k8_tmap_1(X1,X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_68, c_0_40])).
% 0.47/0.68  cnf(c_0_79, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_69, c_0_41]), c_0_50]), c_0_47])).
% 0.47/0.68  cnf(c_0_80, negated_conjecture, (k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))|v1_tsep_1(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_70, c_0_61])).
% 0.47/0.68  cnf(c_0_81, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk3_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.68  cnf(c_0_82, negated_conjecture, (esk3_2(esk4_0,esk5_0)=u1_struct_0(esk5_0)|v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_34]), c_0_36])])).
% 0.47/0.68  fof(c_0_83, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.47/0.68  fof(c_0_84, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.47/0.68  cnf(c_0_85, plain, (X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk2_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk2_3(X1,X2,X3)))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.47/0.68  cnf(c_0_86, negated_conjecture, (esk2_3(esk4_0,esk5_0,k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_struct_0(esk5_0)|k7_tmap_1(esk4_0,u1_struct_0(esk4_0))=k9_tmap_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_75])])).
% 0.47/0.68  cnf(c_0_87, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),X3,X3)|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_59]), c_0_59])).
% 0.47/0.68  cnf(c_0_88, plain, (m1_subset_1(k9_tmap_1(X1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_53, c_0_40])).
% 0.47/0.68  cnf(c_0_89, negated_conjecture, (u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_90, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk4_0))=k8_tmap_1(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_91, plain, (v1_funct_2(k9_tmap_1(X1,X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_54, c_0_40])).
% 0.47/0.68  cnf(c_0_92, plain, (esk1_3(X1,X2,X3)=u1_struct_0(X2)|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.68  cnf(c_0_93, plain, (v1_pre_topc(k8_tmap_1(X1,X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_28, c_0_40])).
% 0.47/0.68  cnf(c_0_94, plain, (v2_pre_topc(k8_tmap_1(X1,X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_27, c_0_40])).
% 0.47/0.68  cnf(c_0_95, plain, (v2_struct_0(X1)|l1_pre_topc(k8_tmap_1(X1,X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 0.47/0.68  cnf(c_0_96, negated_conjecture, (v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)|v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_35]), c_0_36])]), c_0_37]), c_0_57])).
% 0.47/0.68  cnf(c_0_97, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_34]), c_0_36])])).
% 0.47/0.68  cnf(c_0_98, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.47/0.68  cnf(c_0_99, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.47/0.68  cnf(c_0_100, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk4_0))=k9_tmap_1(esk4_0,esk5_0)|~r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_34]), c_0_35]), c_0_59]), c_0_45]), c_0_61]), c_0_59]), c_0_73]), c_0_59]), c_0_74]), c_0_75]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_101, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),k7_tmap_1(esk4_0,u1_struct_0(esk4_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_73]), c_0_74]), c_0_75])])).
% 0.47/0.68  cnf(c_0_102, negated_conjecture, (m1_subset_1(k9_tmap_1(esk4_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk4_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_103, negated_conjecture, (u1_struct_0(k8_tmap_1(esk4_0,esk4_0))=u1_struct_0(esk4_0)), inference(rw,[status(thm)],[c_0_89, c_0_90])).
% 0.47/0.68  cnf(c_0_104, negated_conjecture, (v1_funct_2(k9_tmap_1(esk4_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_105, plain, (v1_funct_1(k9_tmap_1(X1,X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_55, c_0_40])).
% 0.47/0.68  cnf(c_0_106, negated_conjecture, (esk1_3(esk4_0,esk5_0,X1)=u1_struct_0(esk5_0)|X1=k8_tmap_1(esk4_0,esk5_0)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_107, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_108, negated_conjecture, (v2_pre_topc(k8_tmap_1(esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_109, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_110, negated_conjecture, (~v1_tsep_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.68  cnf(c_0_111, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_82]), c_0_97])).
% 0.47/0.68  cnf(c_0_112, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.47/0.68  cnf(c_0_113, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk4_0))=k9_tmap_1(esk4_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.47/0.68  cnf(c_0_114, negated_conjecture, (m1_subset_1(k9_tmap_1(esk4_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 0.47/0.68  cnf(c_0_115, negated_conjecture, (v1_funct_2(k9_tmap_1(esk4_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_104, c_0_103])).
% 0.47/0.68  cnf(c_0_116, negated_conjecture, (v1_funct_1(k9_tmap_1(esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_117, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.68  cnf(c_0_118, negated_conjecture, (esk1_3(esk4_0,esk5_0,k8_tmap_1(esk4_0,esk4_0))=u1_struct_0(esk5_0)|k8_tmap_1(esk4_0,esk5_0)=k8_tmap_1(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_108]), c_0_109])])).
% 0.47/0.68  cnf(c_0_119, plain, (v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.47/0.68  cnf(c_0_120, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_34])]), c_0_67])])).
% 0.47/0.68  cnf(c_0_121, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_46]), c_0_34])])).
% 0.47/0.68  cnf(c_0_122, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk4_0))=k9_tmap_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_123, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.68  cnf(c_0_124, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.47/0.68  cnf(c_0_125, negated_conjecture, (esk2_3(esk4_0,esk5_0,k9_tmap_1(esk4_0,esk4_0))=u1_struct_0(esk5_0)|k9_tmap_1(esk4_0,esk5_0)=k9_tmap_1(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_114]), c_0_115]), c_0_116])])).
% 0.47/0.68  cnf(c_0_126, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.68  cnf(c_0_127, negated_conjecture, (k8_tmap_1(esk4_0,esk5_0)=k8_tmap_1(esk4_0,esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_107]), c_0_34]), c_0_108]), c_0_35]), c_0_109]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_128, plain, (v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_119, c_0_20])).
% 0.47/0.68  cnf(c_0_129, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_66])]), c_0_65])])).
% 0.47/0.68  cnf(c_0_130, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_122]), c_0_123])).
% 0.47/0.68  cnf(c_0_131, negated_conjecture, (k9_tmap_1(esk4_0,esk5_0)=k9_tmap_1(esk4_0,esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_34]), c_0_35]), c_0_59]), c_0_114]), c_0_59]), c_0_115]), c_0_116]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_132, negated_conjecture, (k7_tmap_1(esk4_0,X1)=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_49]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_133, negated_conjecture, (k8_tmap_1(esk4_0,esk5_0)=k8_tmap_1(esk4_0,esk4_0)|v3_pre_topc(u1_struct_0(esk5_0),esk4_0)|u1_struct_0(esk5_0)!=u1_struct_0(X1)|~v1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_36])])).
% 0.47/0.68  cnf(c_0_134, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k8_tmap_1(esk4_0,esk5_0))|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~v3_pre_topc(u1_struct_0(X1),esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_46]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_135, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k9_tmap_1(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_61, c_0_122])).
% 0.47/0.68  cnf(c_0_136, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130])])).
% 0.47/0.68  cnf(c_0_137, negated_conjecture, (k9_tmap_1(esk4_0,esk5_0)=k9_tmap_1(esk4_0,esk4_0)|v3_pre_topc(u1_struct_0(esk5_0),esk4_0)|u1_struct_0(esk5_0)!=u1_struct_0(X1)|~v1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_131]), c_0_36])])).
% 0.47/0.68  cnf(c_0_138, negated_conjecture, (k7_tmap_1(esk4_0,X1)=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[c_0_132, c_0_61])).
% 0.47/0.68  cnf(c_0_139, negated_conjecture, (k8_tmap_1(esk4_0,esk5_0)=k8_tmap_1(esk4_0,esk4_0)|v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_130]), c_0_34])])).
% 0.47/0.68  cnf(c_0_140, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_34])]), c_0_136])).
% 0.47/0.68  cnf(c_0_141, negated_conjecture, (k9_tmap_1(esk4_0,esk5_0)=k9_tmap_1(esk4_0,esk4_0)|v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_130]), c_0_34])])).
% 0.47/0.68  cnf(c_0_142, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(X1))=k7_tmap_1(esk4_0,u1_struct_0(esk4_0))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_20]), c_0_36])])).
% 0.47/0.68  cnf(c_0_143, negated_conjecture, (k8_tmap_1(esk4_0,esk5_0)=k8_tmap_1(esk4_0,esk4_0)), inference(sr,[status(thm)],[c_0_139, c_0_140])).
% 0.47/0.68  cnf(c_0_144, negated_conjecture, (k9_tmap_1(esk4_0,esk5_0)=k9_tmap_1(esk4_0,esk4_0)), inference(sr,[status(thm)],[c_0_141, c_0_140])).
% 0.47/0.68  cnf(c_0_145, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk4_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~v3_pre_topc(u1_struct_0(X1),esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_134, c_0_142])).
% 0.47/0.68  cnf(c_0_146, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk4_0),esk4_0,k8_tmap_1(esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136, c_0_143]), c_0_144])).
% 0.47/0.68  cnf(c_0_147, plain, (v3_pre_topc(u1_struct_0(X1),X2)|u1_struct_0(X1)!=u1_struct_0(X3)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_126, c_0_20])).
% 0.47/0.68  cnf(c_0_148, negated_conjecture, (u1_struct_0(X1)!=u1_struct_0(esk5_0)|~v3_pre_topc(u1_struct_0(X1),esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145, c_0_122]), c_0_144]), c_0_143]), c_0_146])).
% 0.47/0.68  cnf(c_0_149, negated_conjecture, (u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_130]), c_0_34]), c_0_36])]), c_0_148])).
% 0.47/0.68  cnf(c_0_150, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_149, c_0_34]), ['proof']).
% 0.47/0.68  # SZS output end CNFRefutation
% 0.47/0.68  # Proof object total steps             : 151
% 0.47/0.68  # Proof object clause steps            : 120
% 0.47/0.68  # Proof object formula steps           : 31
% 0.47/0.68  # Proof object conjectures             : 73
% 0.47/0.68  # Proof object clause conjectures      : 70
% 0.47/0.68  # Proof object formula conjectures     : 3
% 0.47/0.68  # Proof object initial clauses used    : 34
% 0.47/0.68  # Proof object initial formulas used   : 15
% 0.47/0.68  # Proof object generating inferences   : 70
% 0.47/0.68  # Proof object simplifying inferences  : 206
% 0.47/0.68  # Training examples: 0 positive, 0 negative
% 0.47/0.68  # Parsed axioms                        : 16
% 0.47/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.68  # Initial clauses                      : 48
% 0.47/0.68  # Removed in clause preprocessing      : 0
% 0.47/0.68  # Initial clauses in saturation        : 48
% 0.47/0.68  # Processed clauses                    : 2037
% 0.47/0.68  # ...of these trivial                  : 118
% 0.47/0.68  # ...subsumed                          : 1033
% 0.47/0.68  # ...remaining for further processing  : 886
% 0.47/0.68  # Other redundant clauses eliminated   : 0
% 0.47/0.68  # Clauses deleted for lack of memory   : 0
% 0.47/0.68  # Backward-subsumed                    : 99
% 0.47/0.68  # Backward-rewritten                   : 419
% 0.47/0.68  # Generated clauses                    : 7782
% 0.47/0.68  # ...of the previous two non-trivial   : 7310
% 0.47/0.68  # Contextual simplify-reflections      : 179
% 0.47/0.68  # Paramodulations                      : 7770
% 0.47/0.68  # Factorizations                       : 0
% 0.47/0.68  # Equation resolutions                 : 10
% 0.47/0.68  # Propositional unsat checks           : 0
% 0.47/0.68  #    Propositional check models        : 0
% 0.47/0.68  #    Propositional check unsatisfiable : 0
% 0.47/0.68  #    Propositional clauses             : 0
% 0.47/0.68  #    Propositional clauses after purity: 0
% 0.47/0.68  #    Propositional unsat core size     : 0
% 0.47/0.68  #    Propositional preprocessing time  : 0.000
% 0.47/0.68  #    Propositional encoding time       : 0.000
% 0.47/0.68  #    Propositional solver time         : 0.000
% 0.47/0.68  #    Success case prop preproc time    : 0.000
% 0.47/0.68  #    Success case prop encoding time   : 0.000
% 0.47/0.68  #    Success case prop solver time     : 0.000
% 0.47/0.68  # Current number of processed clauses  : 366
% 0.47/0.68  #    Positive orientable unit clauses  : 21
% 0.47/0.68  #    Positive unorientable unit clauses: 0
% 0.47/0.68  #    Negative unit clauses             : 5
% 0.47/0.68  #    Non-unit-clauses                  : 340
% 0.47/0.68  # Current number of unprocessed clauses: 5155
% 0.47/0.68  # ...number of literals in the above   : 29431
% 0.47/0.68  # Current number of archived formulas  : 0
% 0.47/0.68  # Current number of archived clauses   : 520
% 0.47/0.68  # Clause-clause subsumption calls (NU) : 110312
% 0.47/0.68  # Rec. Clause-clause subsumption calls : 13406
% 0.47/0.68  # Non-unit clause-clause subsumptions  : 1287
% 0.47/0.68  # Unit Clause-clause subsumption calls : 1666
% 0.47/0.68  # Rewrite failures with RHS unbound    : 0
% 0.47/0.68  # BW rewrite match attempts            : 26
% 0.47/0.68  # BW rewrite match successes           : 16
% 0.47/0.68  # Condensation attempts                : 0
% 0.47/0.68  # Condensation successes               : 0
% 0.47/0.68  # Termbank termtop insertions          : 374797
% 0.47/0.68  
% 0.47/0.68  # -------------------------------------------------
% 0.47/0.68  # User time                : 0.338 s
% 0.47/0.68  # System time              : 0.007 s
% 0.47/0.68  # Total time               : 0.345 s
% 0.47/0.68  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
