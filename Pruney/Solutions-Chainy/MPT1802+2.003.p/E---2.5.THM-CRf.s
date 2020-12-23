%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:25 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 654 expanded)
%              Number of clauses        :   65 ( 224 expanded)
%              Number of leaves         :   15 ( 163 expanded)
%              Depth                    :   20
%              Number of atoms          :  539 (4726 expanded)
%              Number of equality atoms :   50 ( 150 expanded)
%              Maximal formula depth    :   18 (   6 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t118_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_tmap_1)).

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

fof(t109_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_xboole_0(u1_struct_0(X3),X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).

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

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

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

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r1_tsep_1(X2,X3)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X3))
                     => r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t118_tmap_1])).

fof(c_0_18,plain,(
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
    ! [X31,X32] :
      ( ( v1_pre_topc(k8_tmap_1(X31,X32))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_pre_topc(X32,X31) )
      & ( v2_pre_topc(k8_tmap_1(X31,X32))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_pre_topc(X32,X31) )
      & ( l1_pre_topc(k8_tmap_1(X31,X32))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_pre_topc(X32,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_22,plain,(
    ! [X33,X34] :
      ( ( v1_funct_1(k9_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_pre_topc(X34,X33) )
      & ( v1_funct_2(k9_tmap_1(X33,X34),u1_struct_0(X33),u1_struct_0(k8_tmap_1(X33,X34)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_pre_topc(X34,X33) )
      & ( m1_subset_1(k9_tmap_1(X33,X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(k8_tmap_1(X33,X34)))))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_pre_topc(X34,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & r1_tsep_1(esk4_0,esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ~ r1_tmap_1(esk5_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_24,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
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

fof(c_0_29,plain,(
    ! [X29,X30] :
      ( ( v1_funct_1(k7_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( v1_funct_2(k7_tmap_1(X29,X30),u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X30)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( m1_subset_1(k7_tmap_1(X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X30)))))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

fof(c_0_30,plain,(
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

cnf(c_0_31,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_39,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X3))
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_40,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(X1)) = k8_tmap_1(esk3_0,esk4_0)
    | u1_struct_0(X1) != u1_struct_0(esk4_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

fof(c_0_49,plain,(
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

cnf(c_0_50,plain,
    ( m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_51,plain,
    ( v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_20])).

cnf(c_0_52,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,X1)),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,X1))
    | X1 != u1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_33]),c_0_45]),c_0_46]),c_0_32]),c_0_34])]),c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_32])])).

cnf(c_0_55,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_47]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_32]),c_0_47]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_59,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,X1)),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,X1))
    | X1 != u1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( X1 = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk3_0),u1_struct_0(esk3_0),X1,k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_54])).

fof(c_0_64,plain,(
    ! [X39,X40,X41,X42] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | v2_struct_0(X41)
      | ~ m1_pre_topc(X41,X39)
      | ~ r1_xboole_0(u1_struct_0(X41),X40)
      | ~ m1_subset_1(X42,u1_struct_0(X41))
      | r1_tmap_1(X41,k6_tmap_1(X39,X40),k2_tmap_1(X39,k6_tmap_1(X39,X40),k7_tmap_1(X39,X40),X41),X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t109_tmap_1])])])])).

fof(c_0_65,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_66,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63]),c_0_46])])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_xboole_0(u1_struct_0(X3),X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_20]),c_0_32]),c_0_34])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(X2)),X1),X3)
    | v2_struct_0(X1)
    | u1_struct_0(X2) != u1_struct_0(esk4_0)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X2,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_48]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_71,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_35])).

fof(c_0_72,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_32])])).

cnf(c_0_74,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_34])])).

fof(c_0_76,plain,(
    ! [X27,X28] :
      ( ( ~ r1_tsep_1(X27,X28)
        | r1_xboole_0(u1_struct_0(X27),u1_struct_0(X28))
        | ~ l1_struct_0(X28)
        | ~ l1_struct_0(X27) )
      & ( ~ r1_xboole_0(u1_struct_0(X27),u1_struct_0(X28))
        | r1_tsep_1(X27,X28)
        | ~ l1_struct_0(X28)
        | ~ l1_struct_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

fof(c_0_77,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | l1_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_20]),c_0_32]),c_0_34])])).

cnf(c_0_79,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_80,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_32]),c_0_34])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_74]),c_0_82])])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_85,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_88,plain,(
    ! [X35,X36] :
      ( ~ l1_struct_0(X35)
      | ~ l1_struct_0(X36)
      | ~ r1_tsep_1(X35,X36)
      | r1_tsep_1(X36,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk4_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])]),c_0_86]),c_0_87])).

cnf(c_0_90,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_92,negated_conjecture,
    ( ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])])).

cnf(c_0_93,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_85]),c_0_34])])).

cnf(c_0_94,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_74]),c_0_93])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_74]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:54:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 2.65/2.84  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 2.65/2.84  # and selection function PSelectComplexExceptRRHorn.
% 2.65/2.84  #
% 2.65/2.84  # Preprocessing time       : 0.023 s
% 2.65/2.84  # Presaturation interreduction done
% 2.65/2.84  
% 2.65/2.84  # Proof found!
% 2.65/2.84  # SZS status Theorem
% 2.65/2.84  # SZS output start CNFRefutation
% 2.65/2.84  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 2.65/2.84  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.65/2.84  fof(t118_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_tsep_1(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_tmap_1)).
% 2.65/2.84  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.65/2.84  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 2.65/2.84  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 2.65/2.84  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 2.65/2.84  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 2.65/2.84  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 2.65/2.84  fof(t109_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_xboole_0(u1_struct_0(X3),X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_tmap_1)).
% 2.65/2.84  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.65/2.84  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.65/2.84  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.65/2.84  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.65/2.84  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.65/2.84  fof(c_0_15, plain, ![X17, X18, X19, X20]:((X19!=k8_tmap_1(X17,X18)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|(X20!=u1_struct_0(X18)|X19=k6_tmap_1(X17,X20)))|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((m1_subset_1(esk1_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((esk1_3(X17,X18,X19)=u1_struct_0(X18)|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(X19!=k6_tmap_1(X17,esk1_3(X17,X18,X19))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 2.65/2.84  fof(c_0_16, plain, ![X43, X44]:(~l1_pre_topc(X43)|(~m1_pre_topc(X44,X43)|m1_subset_1(u1_struct_0(X44),k1_zfmisc_1(u1_struct_0(X43))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 2.65/2.84  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_tsep_1(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4))))))), inference(assume_negation,[status(cth)],[t118_tmap_1])).
% 2.65/2.84  fof(c_0_18, plain, ![X37, X38]:((u1_struct_0(k6_tmap_1(X37,X38))=u1_struct_0(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(u1_pre_topc(k6_tmap_1(X37,X38))=k5_tmap_1(X37,X38)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 2.65/2.84  cnf(c_0_19, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.65/2.84  cnf(c_0_20, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.65/2.84  fof(c_0_21, plain, ![X31, X32]:(((v1_pre_topc(k8_tmap_1(X31,X32))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_pre_topc(X32,X31)))&(v2_pre_topc(k8_tmap_1(X31,X32))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_pre_topc(X32,X31))))&(l1_pre_topc(k8_tmap_1(X31,X32))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_pre_topc(X32,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 2.65/2.84  fof(c_0_22, plain, ![X33, X34]:(((v1_funct_1(k9_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))&(v1_funct_2(k9_tmap_1(X33,X34),u1_struct_0(X33),u1_struct_0(k8_tmap_1(X33,X34)))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33))))&(m1_subset_1(k9_tmap_1(X33,X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(k8_tmap_1(X33,X34)))))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 2.65/2.84  fof(c_0_23, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&(r1_tsep_1(esk4_0,esk5_0)&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&~r1_tmap_1(esk5_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 2.65/2.84  cnf(c_0_24, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.65/2.84  cnf(c_0_25, plain, (X1=k6_tmap_1(X2,u1_struct_0(X3))|v2_struct_0(X2)|u1_struct_0(X3)!=u1_struct_0(X4)|X1!=k8_tmap_1(X2,X4)|~v1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 2.65/2.84  cnf(c_0_26, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.65/2.84  cnf(c_0_27, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.65/2.84  cnf(c_0_28, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.65/2.84  fof(c_0_29, plain, ![X29, X30]:(((v1_funct_1(k7_tmap_1(X29,X30))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))))&(v1_funct_2(k7_tmap_1(X29,X30),u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X30)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))))))&(m1_subset_1(k7_tmap_1(X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X30)))))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 2.65/2.84  fof(c_0_30, plain, ![X22, X23, X24, X25]:((X24!=k9_tmap_1(X22,X23)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))|(X25!=u1_struct_0(X23)|r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X25)),X24,k7_tmap_1(X22,X25))))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((m1_subset_1(esk2_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((esk2_3(X22,X23,X24)=u1_struct_0(X23)|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,esk2_3(X22,X23,X24))),X24,k7_tmap_1(X22,esk2_3(X22,X23,X24)))|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 2.65/2.84  cnf(c_0_31, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.65/2.84  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.65/2.84  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.65/2.84  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.65/2.84  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.65/2.84  cnf(c_0_36, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.65/2.84  cnf(c_0_37, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.65/2.84  cnf(c_0_38, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_20])).
% 2.65/2.84  cnf(c_0_39, plain, (k8_tmap_1(X1,X2)=k6_tmap_1(X1,u1_struct_0(X3))|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 2.65/2.84  cnf(c_0_40, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.65/2.84  cnf(c_0_41, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.65/2.84  cnf(c_0_42, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.65/2.84  cnf(c_0_43, plain, (r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))|v2_struct_0(X2)|X1!=k9_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.65/2.84  cnf(c_0_44, negated_conjecture, (m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 2.65/2.84  cnf(c_0_45, negated_conjecture, (v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 2.65/2.84  cnf(c_0_46, negated_conjecture, (v1_funct_1(k9_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 2.65/2.84  cnf(c_0_47, negated_conjecture, (u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))=u1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 2.65/2.84  cnf(c_0_48, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(X1))=k8_tmap_1(esk3_0,esk4_0)|u1_struct_0(X1)!=u1_struct_0(esk4_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 2.65/2.84  fof(c_0_49, plain, ![X11, X12, X13, X14, X15, X16]:((~r1_funct_2(X11,X12,X13,X14,X15,X16)|X15=X16|(v1_xboole_0(X12)|v1_xboole_0(X14)|~v1_funct_1(X15)|~v1_funct_2(X15,X11,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))&(X15!=X16|r1_funct_2(X11,X12,X13,X14,X15,X16)|(v1_xboole_0(X12)|v1_xboole_0(X14)|~v1_funct_1(X15)|~v1_funct_2(X15,X11,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 2.65/2.84  cnf(c_0_50, plain, (m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 2.65/2.84  cnf(c_0_51, plain, (v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_20])).
% 2.65/2.84  cnf(c_0_52, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_42, c_0_20])).
% 2.65/2.84  cnf(c_0_53, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,X1)),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,X1))|X1!=u1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_33]), c_0_45]), c_0_46]), c_0_32]), c_0_34])]), c_0_35])).
% 2.65/2.84  cnf(c_0_54, negated_conjecture, (u1_struct_0(k8_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_32])])).
% 2.65/2.84  cnf(c_0_55, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 2.65/2.84  cnf(c_0_56, negated_conjecture, (m1_subset_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_32]), c_0_47]), c_0_33]), c_0_34])]), c_0_35])).
% 2.65/2.84  cnf(c_0_57, negated_conjecture, (v1_funct_2(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_32]), c_0_47]), c_0_33]), c_0_34])]), c_0_35])).
% 2.65/2.84  cnf(c_0_58, negated_conjecture, (v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 2.65/2.84  cnf(c_0_59, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,X1)),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,X1))|X1!=u1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 2.65/2.84  cnf(c_0_60, negated_conjecture, (X1=k7_tmap_1(esk3_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk3_0),u1_struct_0(esk3_0),X1,k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])])).
% 2.65/2.84  cnf(c_0_61, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_59, c_0_47])).
% 2.65/2.84  cnf(c_0_62, negated_conjecture, (m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_44, c_0_54])).
% 2.65/2.84  cnf(c_0_63, negated_conjecture, (v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_45, c_0_54])).
% 2.65/2.84  fof(c_0_64, plain, ![X39, X40, X41, X42]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X41)|~m1_pre_topc(X41,X39)|(~r1_xboole_0(u1_struct_0(X41),X40)|(~m1_subset_1(X42,u1_struct_0(X41))|r1_tmap_1(X41,k6_tmap_1(X39,X40),k2_tmap_1(X39,k6_tmap_1(X39,X40),k7_tmap_1(X39,X40),X41),X42)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t109_tmap_1])])])])).
% 2.65/2.84  fof(c_0_65, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 2.65/2.84  cnf(c_0_66, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63]), c_0_46])])).
% 2.65/2.84  cnf(c_0_67, plain, (v2_struct_0(X1)|v2_struct_0(X3)|r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~r1_xboole_0(u1_struct_0(X3),X2)|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.65/2.84  cnf(c_0_68, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 2.65/2.84  cnf(c_0_69, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_20]), c_0_32]), c_0_34])])).
% 2.65/2.84  cnf(c_0_70, negated_conjecture, (r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(X2)),X1),X3)|v2_struct_0(X1)|u1_struct_0(X2)!=u1_struct_0(esk4_0)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X2,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_48]), c_0_33]), c_0_34])]), c_0_35])).
% 2.65/2.84  cnf(c_0_71, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_35])).
% 2.65/2.84  fof(c_0_72, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 2.65/2.84  cnf(c_0_73, negated_conjecture, (r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk3_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_32])])).
% 2.65/2.84  cnf(c_0_74, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 2.65/2.84  cnf(c_0_75, negated_conjecture, (r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_34])])).
% 2.65/2.84  fof(c_0_76, plain, ![X27, X28]:((~r1_tsep_1(X27,X28)|r1_xboole_0(u1_struct_0(X27),u1_struct_0(X28))|~l1_struct_0(X28)|~l1_struct_0(X27))&(~r1_xboole_0(u1_struct_0(X27),u1_struct_0(X28))|r1_tsep_1(X27,X28)|~l1_struct_0(X28)|~l1_struct_0(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 2.65/2.84  fof(c_0_77, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|l1_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 2.65/2.84  cnf(c_0_78, negated_conjecture, (r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_20]), c_0_32]), c_0_34])])).
% 2.65/2.84  cnf(c_0_79, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 2.65/2.84  cnf(c_0_80, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 2.65/2.84  cnf(c_0_81, negated_conjecture, (r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)|v2_struct_0(X1)|~r1_tsep_1(X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk3_0)|~l1_struct_0(esk4_0)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 2.65/2.84  cnf(c_0_82, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_32]), c_0_34])])).
% 2.65/2.84  cnf(c_0_83, negated_conjecture, (r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)|v2_struct_0(X1)|~r1_tsep_1(X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_74]), c_0_82])])).
% 2.65/2.84  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.65/2.84  cnf(c_0_85, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.65/2.84  cnf(c_0_86, negated_conjecture, (~r1_tmap_1(esk5_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.65/2.84  cnf(c_0_87, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.65/2.84  fof(c_0_88, plain, ![X35, X36]:(~l1_struct_0(X35)|~l1_struct_0(X36)|(~r1_tsep_1(X35,X36)|r1_tsep_1(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 2.65/2.84  cnf(c_0_89, negated_conjecture, (~r1_tsep_1(esk5_0,esk4_0)|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])]), c_0_86]), c_0_87])).
% 2.65/2.84  cnf(c_0_90, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 2.65/2.84  cnf(c_0_91, negated_conjecture, (r1_tsep_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.65/2.84  cnf(c_0_92, negated_conjecture, (~l1_struct_0(esk5_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])])).
% 2.65/2.84  cnf(c_0_93, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_85]), c_0_34])])).
% 2.65/2.84  cnf(c_0_94, negated_conjecture, (~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_74]), c_0_93])])).
% 2.65/2.84  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_74]), c_0_82])]), ['proof']).
% 2.65/2.84  # SZS output end CNFRefutation
% 2.65/2.84  # Proof object total steps             : 96
% 2.65/2.84  # Proof object clause steps            : 65
% 2.65/2.84  # Proof object formula steps           : 31
% 2.65/2.84  # Proof object conjectures             : 42
% 2.65/2.84  # Proof object clause conjectures      : 39
% 2.65/2.84  # Proof object formula conjectures     : 3
% 2.65/2.84  # Proof object initial clauses used    : 29
% 2.65/2.84  # Proof object initial formulas used   : 15
% 2.65/2.84  # Proof object generating inferences   : 33
% 2.65/2.84  # Proof object simplifying inferences  : 87
% 2.65/2.84  # Training examples: 0 positive, 0 negative
% 2.65/2.84  # Parsed axioms                        : 15
% 2.65/2.84  # Removed by relevancy pruning/SinE    : 0
% 2.65/2.84  # Initial clauses                      : 39
% 2.65/2.84  # Removed in clause preprocessing      : 0
% 2.65/2.84  # Initial clauses in saturation        : 39
% 2.65/2.84  # Processed clauses                    : 16975
% 2.65/2.84  # ...of these trivial                  : 316
% 2.65/2.84  # ...subsumed                          : 11557
% 2.65/2.84  # ...remaining for further processing  : 5102
% 2.65/2.84  # Other redundant clauses eliminated   : 1
% 2.65/2.84  # Clauses deleted for lack of memory   : 0
% 2.65/2.84  # Backward-subsumed                    : 971
% 2.65/2.84  # Backward-rewritten                   : 35
% 2.65/2.84  # Generated clauses                    : 34601
% 2.65/2.84  # ...of the previous two non-trivial   : 32274
% 2.65/2.84  # Contextual simplify-reflections      : 191
% 2.65/2.84  # Paramodulations                      : 34545
% 2.65/2.84  # Factorizations                       : 36
% 2.65/2.84  # Equation resolutions                 : 20
% 2.65/2.84  # Propositional unsat checks           : 0
% 2.65/2.84  #    Propositional check models        : 0
% 2.65/2.84  #    Propositional check unsatisfiable : 0
% 2.65/2.84  #    Propositional clauses             : 0
% 2.65/2.84  #    Propositional clauses after purity: 0
% 2.65/2.84  #    Propositional unsat core size     : 0
% 2.65/2.84  #    Propositional preprocessing time  : 0.000
% 2.65/2.84  #    Propositional encoding time       : 0.000
% 2.65/2.84  #    Propositional solver time         : 0.000
% 2.65/2.84  #    Success case prop preproc time    : 0.000
% 2.65/2.84  #    Success case prop encoding time   : 0.000
% 2.65/2.84  #    Success case prop solver time     : 0.000
% 2.65/2.84  # Current number of processed clauses  : 4056
% 2.65/2.84  #    Positive orientable unit clauses  : 34
% 2.65/2.84  #    Positive unorientable unit clauses: 0
% 2.65/2.84  #    Negative unit clauses             : 5
% 2.65/2.84  #    Non-unit-clauses                  : 4017
% 2.65/2.84  # Current number of unprocessed clauses: 13609
% 2.65/2.84  # ...number of literals in the above   : 131297
% 2.65/2.84  # Current number of archived formulas  : 0
% 2.65/2.84  # Current number of archived clauses   : 1045
% 2.65/2.84  # Clause-clause subsumption calls (NU) : 6655441
% 2.65/2.84  # Rec. Clause-clause subsumption calls : 252914
% 2.65/2.84  # Non-unit clause-clause subsumptions  : 12691
% 2.65/2.84  # Unit Clause-clause subsumption calls : 4889
% 2.65/2.84  # Rewrite failures with RHS unbound    : 0
% 2.65/2.84  # BW rewrite match attempts            : 27
% 2.65/2.84  # BW rewrite match successes           : 16
% 2.65/2.84  # Condensation attempts                : 0
% 2.65/2.84  # Condensation successes               : 0
% 2.65/2.84  # Termbank termtop insertions          : 1410827
% 2.65/2.84  
% 2.65/2.84  # -------------------------------------------------
% 2.65/2.84  # User time                : 2.472 s
% 2.65/2.84  # System time              : 0.021 s
% 2.65/2.84  # Total time               : 2.493 s
% 2.65/2.84  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
