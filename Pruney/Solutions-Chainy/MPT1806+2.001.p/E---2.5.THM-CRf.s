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
% DateTime   : Thu Dec  3 11:18:29 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 (6616 expanded)
%              Number of clauses        :   91 (2262 expanded)
%              Number of leaves         :   14 (1647 expanded)
%              Depth                    :   18
%              Number of atoms          :  675 (65423 expanded)
%              Number of equality atoms :   71 (1740 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

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

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

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

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
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

fof(c_0_16,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_17,plain,(
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

fof(c_0_18,plain,(
    ! [X42,X43] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_pre_topc(X43,X42)
      | m1_subset_1(u1_struct_0(X43),k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_19,plain,
    ( esk3_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X38,X39] :
      ( ( u1_struct_0(k6_tmap_1(X38,X39)) = u1_struct_0(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( u1_pre_topc(k6_tmap_1(X38,X39)) = k5_tmap_1(X38,X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

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

cnf(c_0_24,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
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

cnf(c_0_26,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( esk3_2(esk4_0,esk5_0) = u1_struct_0(esk5_0)
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_29,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
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
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X40,X41] :
      ( ( v1_funct_1(k7_tmap_1(X40,X41))
        | ~ v3_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v1_funct_2(k7_tmap_1(X40,X41),u1_struct_0(X40),u1_struct_0(k6_tmap_1(X40,X41)))
        | ~ v3_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v5_pre_topc(k7_tmap_1(X40,X41),X40,k6_tmap_1(X40,X41))
        | ~ v3_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(k7_tmap_1(X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(k6_tmap_1(X40,X41)))))
        | ~ v3_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ v1_funct_1(k7_tmap_1(X40,X41))
        | ~ v1_funct_2(k7_tmap_1(X40,X41),u1_struct_0(X40),u1_struct_0(k6_tmap_1(X40,X41)))
        | ~ v5_pre_topc(k7_tmap_1(X40,X41),X40,k6_tmap_1(X40,X41))
        | ~ m1_subset_1(k7_tmap_1(X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(k6_tmap_1(X40,X41)))))
        | v3_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).

cnf(c_0_35,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_20]),c_0_21])])).

fof(c_0_37,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | k7_tmap_1(X15,X16) = k6_partfun1(u1_struct_0(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

cnf(c_0_38,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X3))
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_31]),c_0_32]),c_0_33])).

fof(c_0_42,plain,(
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

cnf(c_0_43,plain,
    ( v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_20]),c_0_21])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
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

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_20]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(X1)) = k8_tmap_1(esk4_0,esk5_0)
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_20]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_49,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

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
    ( v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk4_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_20])).

cnf(c_0_55,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_24])).

cnf(c_0_56,plain,
    ( esk2_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk4_0,esk5_0)) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_20])])).

cnf(c_0_58,plain,
    ( m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_24])).

cnf(c_0_59,plain,
    ( v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_24])).

cnf(c_0_60,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_24])).

fof(c_0_61,plain,(
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

cnf(c_0_62,negated_conjecture,
    ( ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ m1_pre_topc(esk5_0,esk4_0)
    | ~ v1_funct_1(k9_tmap_1(esk4_0,esk5_0))
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
    | ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_63,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_20]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_66,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk4_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_20]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_67,negated_conjecture,
    ( esk2_3(esk4_0,esk5_0,X1) = u1_struct_0(esk5_0)
    | X1 = k9_tmap_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_20]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_20]),c_0_47]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_20]),c_0_47]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_20]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_71,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))
    | ~ v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))
    | ~ v1_funct_1(k9_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_20])])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_20]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_20]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_75,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_76,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_48]),c_0_20])])).

cnf(c_0_77,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(X1)) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_66]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_78,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_79,negated_conjecture,
    ( esk2_3(esk4_0,esk5_0,k7_tmap_1(esk4_0,u1_struct_0(esk5_0))) = u1_struct_0(esk5_0)
    | k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70])])).

cnf(c_0_80,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_20]),c_0_21])])).

cnf(c_0_81,plain,
    ( r1_funct_2(X1,X2,X3,X4,X5,X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X5,X3,X4)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ v1_funct_1(X5) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( k7_tmap_1(esk4_0,X1) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_66]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_83,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0)
    | ~ m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])]),c_0_74])])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_20]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_85,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk4_0,esk5_0)
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_20]),c_0_39]),c_0_57]),c_0_68]),c_0_57]),c_0_69]),c_0_70]),c_0_21])]),c_0_40])).

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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_88,negated_conjecture,
    ( k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)) = k6_partfun1(u1_struct_0(esk4_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_80]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_89,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_68]),c_0_69]),c_0_70])])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_82]),c_0_47]),c_0_20]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_91,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v1_tsep_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_92,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_20])])).

cnf(c_0_93,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_87,c_0_51]),c_0_50]),c_0_49])).

cnf(c_0_94,negated_conjecture,
    ( k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)) = k7_tmap_1(esk4_0,u1_struct_0(esk5_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_66])).

cnf(c_0_95,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

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
    ( X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk2_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk2_3(X1,X2,X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_99,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_69])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_36])).

cnf(c_0_101,negated_conjecture,
    ( v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)
    | v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_39]),c_0_21])]),c_0_40]),c_0_80])).

cnf(c_0_102,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_28]),c_0_20]),c_0_21])])).

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
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk4_0,esk5_0)
    | ~ r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k7_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_79]),c_0_20]),c_0_39]),c_0_57]),c_0_47]),c_0_57]),c_0_68]),c_0_57]),c_0_69]),c_0_70]),c_0_21])]),c_0_40])).

cnf(c_0_106,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_107,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_28]),c_0_102])).

cnf(c_0_108,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk4_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0)
    | ~ v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_48]),c_0_20])])).

cnf(c_0_111,negated_conjecture,
    ( k7_tmap_1(esk4_0,u1_struct_0(esk5_0)) = k9_tmap_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_21])]),c_0_40])).

cnf(c_0_112,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | v1_tsep_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_113,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_100]),c_0_39]),c_0_21])]),c_0_40])).

cnf(c_0_114,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk4_0)
    | u1_struct_0(esk5_0) != u1_struct_0(X1)
    | ~ v1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_100]),c_0_21])])).

cnf(c_0_115,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_48]),c_0_20])])).

cnf(c_0_117,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_20])])).

cnf(c_0_118,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_115])])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_111]),c_0_117])]),c_0_118]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:20:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.49  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.21/0.49  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.49  #
% 0.21/0.49  # Preprocessing time       : 0.043 s
% 0.21/0.49  
% 0.21/0.49  # Proof found!
% 0.21/0.49  # SZS status Theorem
% 0.21/0.49  # SZS output start CNFRefutation
% 0.21/0.49  fof(t122_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t122_tmap_1)).
% 0.21/0.49  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.21/0.49  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.21/0.49  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.49  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.21/0.49  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.21/0.49  fof(t113_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.21/0.49  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.21/0.49  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.21/0.49  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.21/0.49  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.21/0.49  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.21/0.49  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.21/0.49  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.49  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t122_tmap_1])).
% 0.21/0.49  fof(c_0_15, plain, ![X27, X28, X29]:((~v1_tsep_1(X28,X27)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|(X29!=u1_struct_0(X28)|v3_pre_topc(X29,X27)))|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&((m1_subset_1(esk3_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&((esk3_2(X27,X28)=u1_struct_0(X28)|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&(~v3_pre_topc(esk3_2(X27,X28),X27)|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.21/0.49  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_pre_topc(esk5_0,esk4_0)&((~v1_tsep_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|(~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))))&(((((v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0))&(v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|v1_tsep_1(esk5_0,esk4_0)))&(v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)))&(m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|v1_tsep_1(esk5_0,esk4_0)))&((((v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|m1_pre_topc(esk5_0,esk4_0))&(v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|m1_pre_topc(esk5_0,esk4_0)))&(v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|m1_pre_topc(esk5_0,esk4_0)))&(m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|m1_pre_topc(esk5_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 0.21/0.49  fof(c_0_17, plain, ![X17, X18, X19, X20]:((X19!=k8_tmap_1(X17,X18)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|(X20!=u1_struct_0(X18)|X19=k6_tmap_1(X17,X20)))|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((m1_subset_1(esk1_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((esk1_3(X17,X18,X19)=u1_struct_0(X18)|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(X19!=k6_tmap_1(X17,esk1_3(X17,X18,X19))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.21/0.49  fof(c_0_18, plain, ![X42, X43]:(~l1_pre_topc(X42)|(~m1_pre_topc(X43,X42)|m1_subset_1(u1_struct_0(X43),k1_zfmisc_1(u1_struct_0(X42))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.49  cnf(c_0_19, plain, (esk3_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.49  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  fof(c_0_22, plain, ![X38, X39]:((u1_struct_0(k6_tmap_1(X38,X39))=u1_struct_0(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(u1_pre_topc(k6_tmap_1(X38,X39))=k5_tmap_1(X38,X39)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.21/0.49  cnf(c_0_23, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_24, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.49  fof(c_0_25, plain, ![X33, X34]:(((v1_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))&(v2_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33))))&(l1_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.21/0.49  cnf(c_0_26, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.49  cnf(c_0_27, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.49  cnf(c_0_28, negated_conjecture, (esk3_2(esk4_0,esk5_0)=u1_struct_0(esk5_0)|v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.21/0.49  cnf(c_0_29, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.49  cnf(c_0_30, plain, (X1=k6_tmap_1(X2,u1_struct_0(X3))|v2_struct_0(X2)|u1_struct_0(X3)!=u1_struct_0(X4)|X1!=k8_tmap_1(X2,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.49  cnf(c_0_31, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.49  cnf(c_0_32, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.49  cnf(c_0_33, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.49  fof(c_0_34, plain, ![X40, X41]:(((((v1_funct_1(k7_tmap_1(X40,X41))|~v3_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(v1_funct_2(k7_tmap_1(X40,X41),u1_struct_0(X40),u1_struct_0(k6_tmap_1(X40,X41)))|~v3_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(v5_pre_topc(k7_tmap_1(X40,X41),X40,k6_tmap_1(X40,X41))|~v3_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(m1_subset_1(k7_tmap_1(X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(k6_tmap_1(X40,X41)))))|~v3_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(~v1_funct_1(k7_tmap_1(X40,X41))|~v1_funct_2(k7_tmap_1(X40,X41),u1_struct_0(X40),u1_struct_0(k6_tmap_1(X40,X41)))|~v5_pre_topc(k7_tmap_1(X40,X41),X40,k6_tmap_1(X40,X41))|~m1_subset_1(k7_tmap_1(X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(k6_tmap_1(X40,X41)))))|v3_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).
% 0.21/0.49  cnf(c_0_35, plain, (v3_pre_topc(u1_struct_0(X1),X2)|u1_struct_0(X1)!=u1_struct_0(X3)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.21/0.49  cnf(c_0_36, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_20]), c_0_21])])).
% 0.21/0.49  fof(c_0_37, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|k7_tmap_1(X15,X16)=k6_partfun1(u1_struct_0(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.21/0.49  cnf(c_0_38, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_29, c_0_24])).
% 0.21/0.49  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_41, plain, (k8_tmap_1(X1,X2)=k6_tmap_1(X1,u1_struct_0(X3))|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.21/0.49  fof(c_0_42, plain, ![X31, X32]:(((v1_funct_1(k7_tmap_1(X31,X32))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))))&(v1_funct_2(k7_tmap_1(X31,X32),u1_struct_0(X31),u1_struct_0(k6_tmap_1(X31,X32)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))))&(m1_subset_1(k7_tmap_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(k6_tmap_1(X31,X32)))))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.21/0.49  cnf(c_0_43, plain, (v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.49  cnf(c_0_44, negated_conjecture, (v3_pre_topc(u1_struct_0(X1),esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_20]), c_0_21])])).
% 0.21/0.49  cnf(c_0_45, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.49  fof(c_0_46, plain, ![X22, X23, X24, X25]:((X24!=k9_tmap_1(X22,X23)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))|(X25!=u1_struct_0(X23)|r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X25)),X24,k7_tmap_1(X22,X25))))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((m1_subset_1(esk2_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((esk2_3(X22,X23,X24)=u1_struct_0(X23)|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,esk2_3(X22,X23,X24))),X24,k7_tmap_1(X22,esk2_3(X22,X23,X24)))|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.21/0.49  cnf(c_0_47, negated_conjecture, (u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_20]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_48, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(X1))=k8_tmap_1(esk4_0,esk5_0)|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_20]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_49, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.49  cnf(c_0_50, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.49  cnf(c_0_51, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.49  fof(c_0_52, plain, ![X35, X36]:(((v1_funct_1(k9_tmap_1(X35,X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))&(v1_funct_2(k9_tmap_1(X35,X36),u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35))))&(m1_subset_1(k9_tmap_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)))))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.21/0.49  cnf(c_0_53, plain, (v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_24])).
% 0.21/0.49  cnf(c_0_54, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk4_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_44, c_0_20])).
% 0.21/0.49  cnf(c_0_55, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_24])).
% 0.21/0.49  cnf(c_0_56, plain, (esk2_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.49  cnf(c_0_57, negated_conjecture, (u1_struct_0(k8_tmap_1(esk4_0,esk5_0))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_20])])).
% 0.21/0.49  cnf(c_0_58, plain, (m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_49, c_0_24])).
% 0.21/0.49  cnf(c_0_59, plain, (v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_24])).
% 0.21/0.49  cnf(c_0_60, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_51, c_0_24])).
% 0.21/0.49  fof(c_0_61, plain, ![X9, X10, X11, X12, X13, X14]:((~r1_funct_2(X9,X10,X11,X12,X13,X14)|X13=X14|(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(X13!=X14|r1_funct_2(X9,X10,X11,X12,X13,X14)|(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.21/0.49  cnf(c_0_62, negated_conjecture, (~v1_tsep_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_63, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.49  cnf(c_0_64, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.49  cnf(c_0_65, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_20]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_66, negated_conjecture, (k6_partfun1(u1_struct_0(esk4_0))=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_20]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_67, negated_conjecture, (esk2_3(esk4_0,esk5_0,X1)=u1_struct_0(esk5_0)|X1=k9_tmap_1(esk4_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk4_0))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_20]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_68, negated_conjecture, (m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_20]), c_0_47]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_69, negated_conjecture, (v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_20]), c_0_47]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_70, negated_conjecture, (v1_funct_1(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_20]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_71, plain, (r1_funct_2(X3,X4,X5,X6,X1,X2)|v1_xboole_0(X4)|v1_xboole_0(X6)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X6)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.49  cnf(c_0_72, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))|~v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))|~v1_funct_1(k9_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_20])])).
% 0.21/0.49  cnf(c_0_73, negated_conjecture, (v1_funct_1(k9_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_20]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_74, negated_conjecture, (v1_funct_2(k9_tmap_1(esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_20]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_75, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.49  cnf(c_0_76, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_48]), c_0_20])])).
% 0.21/0.49  cnf(c_0_77, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(X1))=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_66]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_78, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.49  cnf(c_0_79, negated_conjecture, (esk2_3(esk4_0,esk5_0,k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))=u1_struct_0(esk5_0)|k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k9_tmap_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70])])).
% 0.21/0.49  cnf(c_0_80, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|m1_subset_1(esk3_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_20]), c_0_21])])).
% 0.21/0.49  cnf(c_0_81, plain, (r1_funct_2(X1,X2,X3,X4,X5,X5)|v1_xboole_0(X4)|v1_xboole_0(X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X5,X3,X4)|~v1_funct_2(X5,X1,X2)|~v1_funct_1(X5)), inference(er,[status(thm)],[c_0_71])).
% 0.21/0.49  cnf(c_0_82, negated_conjecture, (k7_tmap_1(esk4_0,X1)=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_66]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_83, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)|~m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])]), c_0_74])])).
% 0.21/0.49  cnf(c_0_84, negated_conjecture, (m1_subset_1(k9_tmap_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk4_0,esk5_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_20]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_85, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(X1)),esk4_0,k8_tmap_1(esk4_0,esk5_0))|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.21/0.49  cnf(c_0_86, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k9_tmap_1(esk4_0,esk5_0)|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_20]), c_0_39]), c_0_57]), c_0_68]), c_0_57]), c_0_69]), c_0_70]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_87, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|~v1_funct_1(k7_tmap_1(X1,X2))|~v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|~v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|~m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.49  cnf(c_0_88, negated_conjecture, (k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))=k6_partfun1(u1_struct_0(esk4_0))|v1_tsep_1(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_80]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_89, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(X2)|~m1_subset_1(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_68]), c_0_69]), c_0_70])])).
% 0.21/0.49  cnf(c_0_90, negated_conjecture, (m1_subset_1(k7_tmap_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_82]), c_0_47]), c_0_20]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_91, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v1_tsep_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])])).
% 0.21/0.49  cnf(c_0_92, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_20])])).
% 0.21/0.49  cnf(c_0_93, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_87, c_0_51]), c_0_50]), c_0_49])).
% 0.21/0.49  cnf(c_0_94, negated_conjecture, (k7_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0))=k7_tmap_1(esk4_0,u1_struct_0(esk5_0))|v1_tsep_1(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_88, c_0_66])).
% 0.21/0.49  cnf(c_0_95, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk3_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.49  fof(c_0_96, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.21/0.49  fof(c_0_97, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.49  cnf(c_0_98, plain, (X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk2_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk2_3(X1,X2,X3)))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.49  cnf(c_0_99, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))|v1_xboole_0(u1_struct_0(esk4_0))|~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_69])])).
% 0.21/0.49  cnf(c_0_100, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_36])).
% 0.21/0.49  cnf(c_0_101, negated_conjecture, (v3_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)|v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k6_tmap_1(esk4_0,esk3_2(esk4_0,esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_39]), c_0_21])]), c_0_40]), c_0_80])).
% 0.21/0.49  cnf(c_0_102, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_28]), c_0_20]), c_0_21])])).
% 0.21/0.49  cnf(c_0_103, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.21/0.49  cnf(c_0_104, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.21/0.49  cnf(c_0_105, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k9_tmap_1(esk4_0,esk5_0)|~r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_79]), c_0_20]), c_0_39]), c_0_57]), c_0_47]), c_0_57]), c_0_68]), c_0_57]), c_0_69]), c_0_70]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_106, negated_conjecture, (r1_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),k7_tmap_1(esk4_0,u1_struct_0(esk5_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 0.21/0.49  cnf(c_0_107, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_28]), c_0_102])).
% 0.21/0.49  cnf(c_0_108, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.21/0.49  cnf(c_0_109, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k9_tmap_1(esk4_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.21/0.49  cnf(c_0_110, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)|~v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_48]), c_0_20])])).
% 0.21/0.49  cnf(c_0_111, negated_conjecture, (k7_tmap_1(esk4_0,u1_struct_0(esk5_0))=k9_tmap_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_112, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))|v1_tsep_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_113, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k6_tmap_1(esk4_0,u1_struct_0(esk5_0)))|~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_100]), c_0_39]), c_0_21])]), c_0_40])).
% 0.21/0.49  cnf(c_0_114, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk4_0)|u1_struct_0(esk5_0)!=u1_struct_0(X1)|~v1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_100]), c_0_21])])).
% 0.21/0.49  cnf(c_0_115, negated_conjecture, (v1_tsep_1(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111]), c_0_112])).
% 0.21/0.49  cnf(c_0_116, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk4_0,u1_struct_0(esk5_0)),esk4_0,k8_tmap_1(esk4_0,esk5_0))|~v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_48]), c_0_20])])).
% 0.21/0.49  cnf(c_0_117, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_20])])).
% 0.21/0.49  cnf(c_0_118, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk4_0,esk5_0),esk4_0,k8_tmap_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_115])])).
% 0.21/0.49  cnf(c_0_119, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_111]), c_0_117])]), c_0_118]), ['proof']).
% 0.21/0.49  # SZS output end CNFRefutation
% 0.21/0.49  # Proof object total steps             : 120
% 0.21/0.49  # Proof object clause steps            : 91
% 0.21/0.49  # Proof object formula steps           : 29
% 0.21/0.49  # Proof object conjectures             : 57
% 0.21/0.49  # Proof object clause conjectures      : 54
% 0.21/0.49  # Proof object formula conjectures     : 3
% 0.21/0.49  # Proof object initial clauses used    : 31
% 0.21/0.49  # Proof object initial formulas used   : 14
% 0.21/0.49  # Proof object generating inferences   : 50
% 0.21/0.49  # Proof object simplifying inferences  : 163
% 0.21/0.49  # Training examples: 0 positive, 0 negative
% 0.21/0.49  # Parsed axioms                        : 15
% 0.21/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.49  # Initial clauses                      : 50
% 0.21/0.49  # Removed in clause preprocessing      : 0
% 0.21/0.49  # Initial clauses in saturation        : 50
% 0.21/0.49  # Processed clauses                    : 670
% 0.21/0.49  # ...of these trivial                  : 24
% 0.21/0.49  # ...subsumed                          : 260
% 0.21/0.49  # ...remaining for further processing  : 385
% 0.21/0.49  # Other redundant clauses eliminated   : 1
% 0.21/0.49  # Clauses deleted for lack of memory   : 0
% 0.21/0.49  # Backward-subsumed                    : 31
% 0.21/0.49  # Backward-rewritten                   : 177
% 0.21/0.49  # Generated clauses                    : 1384
% 0.21/0.49  # ...of the previous two non-trivial   : 1288
% 0.21/0.49  # Contextual simplify-reflections      : 36
% 0.21/0.49  # Paramodulations                      : 1367
% 0.21/0.49  # Factorizations                       : 10
% 0.21/0.49  # Equation resolutions                 : 7
% 0.21/0.49  # Propositional unsat checks           : 0
% 0.21/0.49  #    Propositional check models        : 0
% 0.21/0.49  #    Propositional check unsatisfiable : 0
% 0.21/0.49  #    Propositional clauses             : 0
% 0.21/0.49  #    Propositional clauses after purity: 0
% 0.21/0.49  #    Propositional unsat core size     : 0
% 0.21/0.49  #    Propositional preprocessing time  : 0.000
% 0.21/0.49  #    Propositional encoding time       : 0.000
% 0.21/0.49  #    Propositional solver time         : 0.000
% 0.21/0.49  #    Success case prop preproc time    : 0.000
% 0.21/0.49  #    Success case prop encoding time   : 0.000
% 0.21/0.49  #    Success case prop solver time     : 0.000
% 0.21/0.49  # Current number of processed clauses  : 176
% 0.21/0.49  #    Positive orientable unit clauses  : 21
% 0.21/0.49  #    Positive unorientable unit clauses: 0
% 0.21/0.49  #    Negative unit clauses             : 2
% 0.21/0.49  #    Non-unit-clauses                  : 153
% 0.21/0.49  # Current number of unprocessed clauses: 640
% 0.21/0.49  # ...number of literals in the above   : 3572
% 0.21/0.49  # Current number of archived formulas  : 0
% 0.21/0.49  # Current number of archived clauses   : 208
% 0.21/0.49  # Clause-clause subsumption calls (NU) : 31241
% 0.21/0.49  # Rec. Clause-clause subsumption calls : 3271
% 0.21/0.49  # Non-unit clause-clause subsumptions  : 313
% 0.21/0.49  # Unit Clause-clause subsumption calls : 373
% 0.21/0.49  # Rewrite failures with RHS unbound    : 0
% 0.21/0.49  # BW rewrite match attempts            : 11
% 0.21/0.49  # BW rewrite match successes           : 11
% 0.21/0.49  # Condensation attempts                : 0
% 0.21/0.49  # Condensation successes               : 0
% 0.21/0.49  # Termbank termtop insertions          : 53292
% 0.21/0.49  
% 0.21/0.49  # -------------------------------------------------
% 0.21/0.49  # User time                : 0.139 s
% 0.21/0.49  # System time              : 0.006 s
% 0.21/0.49  # Total time               : 0.145 s
% 0.21/0.49  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
